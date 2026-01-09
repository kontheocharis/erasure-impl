module Evaluation (($$), quote, eval, nf, tryForce, force, up, down, ix2Lvl, lvl2Ix, vApp) where

import Common
import Data.Maybe (fromMaybe)
import Debug.Trace (trace, traceStack)
import Metacontext
import Syntax
import Value

infixl 8 $$

($$) :: Closure -> Val -> Val
($$) (Closure mrk env t isd) ~u = eval mrk (env :> ifIsDowned up isd u) t

vApp :: Val -> Val -> Mode -> Icit -> Val
-- vApp t ~u q i = trace (">>>>>> applying " ++ show t ++ " to " ++ show u ++ " at mode " ++ show q ++ " and icit " ++ show i) $ case t of
vApp t ~u q i = case t of
  VLam isd _ _ _ t -> ifIsDowned down isd (t $$ ifIsDowned up isd u)
  VFlex isd m mrk sp -> VFlex isd m mrk (sp :> (ifIsDowned up isd u, q, i))
  VRigid isd isu x sp -> VRigid isd isu x (sp :> (ifIsDowned up isd u, q, i))
  _ -> error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  [] -> t
  sp :> (u, q, i) -> vApp (vAppSp t sp) u q i

vMeta :: MetaVar -> Marker -> Val
vMeta m mrk = case lookupMeta m of
  Solved v -> v
  Unsolved -> VMeta m mrk

vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([], []) -> v
  (env :> t, bds :> Bound q) -> vApp (vAppBDs env v bds) t q Expl
  (env :> t, bds :> Defined) -> vAppBDs env v bds
  _ -> error "impossible"

eval :: Marker -> Env -> Tm -> Val
-- eval mrk env t = trace (">>>>>> evaluating " ++ show t ++ " at " ++ show env) $ case t of
eval mrk env t = case t of
  Var x -> env !! unIx x
  App t u q i -> vApp (eval mrk env t) (eval mrk env u) q i
  Lam x q i t -> VLam NotDowned x q i (Closure mrk env t NotDowned)
  Pi x q i a b -> VPi NotUpped x q i (eval mrk env a) (Closure mrk env b NotDowned)
  Let _ _ _ t u -> eval mrk (env :> eval mrk env t) u
  U -> VU NotUpped
  Meta m mrk -> vMeta m mrk
  InsertedMeta m mrk bds -> vAppBDs env (vMeta m mrk) bds
  Up t -> up (eval mrk env t)
  Down t -> down (eval Present env t)

up :: Val -> Val
up = moveVal Upward

down :: Val -> Val
down = moveVal Downward

moveVal :: Dir -> Val -> Val
-- moveVal dir v = traceStack (">>>>>> moving " ++ show dir ++ " " ++ show v) $ case v of
moveVal dir v = case v of
  VFlex isd m mrk sp -> VFlex (moveIsDowned dir isd) m mrk sp
  VRigid isd isu x sp -> VRigid (moveIsDowned dir isd) isu x sp
  VLam isd x q i t -> VLam (moveIsDowned dir isd) x q i t
  VPi isu x q i a b -> VPi (moveIsUpped dir isu) x q i a b
  VU isu -> VU (moveIsUpped dir isu)

tryForce :: Val -> Maybe Val
-- tryForce v = trace (">>>>>> trying to force " ++ show v) $ case v of
tryForce v = case v of
  VFlex isd m mrk sp -> case lookupMeta m of
    Solved t -> ifIsDowned down isd <$> tryForce (vAppSp t sp)
    Unsolved -> Nothing
  t -> Just t

force :: Val -> Val
force t = fromMaybe t (tryForce t)

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

ix2Lvl :: Lvl -> Ix -> Lvl
ix2Lvl (Lvl l) (Ix x) = Lvl (l - x - 1)

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  [] -> t
  sp :> (u, q, i) -> App (quoteSp l t sp) (quote l u) q i

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex isd m mrk sp -> ifIsDowned downS isd $ quoteSp l (Meta m mrk) sp
  VRigid isd isu x sp -> ifIsDowned downS isd $ quoteSp l (ifIsUpped upS isu (Var (lvl2Ix l x))) sp
  VLam isd x q i t -> ifIsDowned downS isd $ Lam x q i (quote (l + 1) (t $$ VVar l q))
  VPi isu x q i a b -> ifIsUpped upS isu $ Pi x q i (quote l a) (quote (l + 1) (b $$ VVar l Zero))
  VU isu -> ifIsUpped upS isu U

nf :: Marker -> Env -> Tm -> Tm
nf mrk env t = quote (Lvl (length env)) (eval mrk env t)