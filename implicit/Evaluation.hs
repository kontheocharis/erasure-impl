module Evaluation (($$), quote, eval, nf, tryForce, force, ix2Lvl, lvl2Ix, vApp) where

import Common
import Data.Maybe (fromMaybe)
import Metacontext
import Syntax
import Value

infixl 8 $$

($$) :: Closure -> Val -> Val
($$) (Closure env t) ~u = eval (env :> u) t

vApp :: Val -> Val -> Mode -> Icit -> Val
vApp t ~u q i = case t of
  VLam _ _ _ t -> t $$ u
  VFlex m q' sp -> VFlex m q' (sp :> (u, q, i))
  VRigid x q' sp -> VRigid x q' (sp :> (u, q, i))
  _ -> error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  [] -> t
  sp :> (u, q, i) -> vApp (vAppSp t sp) u q i

vMeta :: MetaVar -> Val
vMeta m = case lookupMeta m of
  Solved _ v -> v
  Unsolved q -> VMeta m q

vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([], []) -> v
  (env :> t, bds :> Bound q) -> vApp (vAppBDs env v bds) t q Expl
  (env :> t, bds :> Defined) -> vAppBDs env v bds
  _ -> error "impossible"

eval :: Env -> Tm -> Val
-- eval env t = trace (">>>>>> evaluating " ++ show t ++ " at " ++ show env) $ case t of
eval env t = case t of
  Var x _ -> env !! unIx x
  App t u q i -> vApp (eval env t) (eval env u) q i
  Lam x q i t -> VLam x q i (Closure env t)
  Pi x q i a b -> VPi x q i (eval env a) (Closure env b)
  Let _ _ _ t u -> eval (env :> eval env t) u
  U -> VU
  Meta m q -> vMeta m
  InsertedMeta m _ bds -> vAppBDs env (vMeta m) bds

tryForce :: Val -> Maybe Val
tryForce = \case
  VFlex m _ sp -> case lookupMeta m of
    Solved _ t -> tryForce (vAppSp t sp)
    Unsolved _ -> Nothing
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
  VFlex m q sp -> quoteSp l (Meta m q) sp
  VRigid x q sp -> quoteSp l (Var (lvl2Ix l x) q) sp
  VLam x q i t -> Lam x q i (quote (l + 1) (t $$ VVar l q))
  VPi x q i a b -> Pi x q i (quote l a) (quote (l + 1) (b $$ VVar l Zero))
  VU -> U

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)