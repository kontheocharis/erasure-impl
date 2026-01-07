module Evaluation (($$), quote, eval, nf, force, lvl2Ix, vApp) where

import Common
import Debug.Trace (trace)
import Metacontext
import Pretty (showTm0)
import Syntax
import Value

infixl 8 $$

($$) :: Closure -> Val -> Val
($$) (Closure env t) ~u = eval (env :> u) t

vApp :: Val -> Val -> Mode -> Icit -> Val
vApp t ~u q i = case t of
  VLam _ _ _ t -> t $$ u
  VFlex m sp -> VFlex m (sp :> (u, q, i))
  VRigid x q' sp -> VRigid x q' (sp :> (u, q, i))
  _ -> error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  [] -> t
  sp :> (u, q, i) -> vApp (vAppSp t sp) u q i

vMeta :: MetaVar -> Val
vMeta m = case lookupMeta m of
  Solved v -> v
  Unsolved -> VMeta m

vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([], []) -> v
  (env :> t, bds :> Bound) -> vApp (vAppBDs env v bds) t Omega Expl
  (env :> t, bds :> Defined) -> vAppBDs env v bds
  _ -> error "impossible"

move :: Dir -> Tm -> Tm
move Upward = Up
move Downward = Down

coe :: Dir -> Val -> Val
coe dir = \case
  VFlex m sp -> VFlex m (map (\(u, q', i) -> (coe dir u, q', i)) sp)
  VRigid x q sp -> VRigid x (moveVarMode dir q) (map (\(u, q', i) -> (coe dir u, q', i)) sp)
  VLam x q i (Closure env t) -> VLam x q i (Closure env (move dir t))
  VPi x q i a (Closure env b) -> VPi x q i (coe dir a) (Closure env (move dir b))
  VU -> VU

eval :: Env -> Tm -> Val
eval env t = trace ("trying to eval " ++ show t ++ " in " ++ show env) $ case t of
  Var x _ -> env !! unIx x
  App t u q i -> vApp (eval env t) (eval env u) q i
  Lam x q i t -> VLam x q i (Closure env t)
  Pi x q i a b -> VPi x q i (eval env a) (Closure env b)
  Let _ _ _ t u -> eval (env :> eval env t) u
  U -> VU
  Meta m -> vMeta m
  InsertedMeta m bds -> vAppBDs env (vMeta m) bds
  Up t -> coe Upward (eval env t)
  Down t -> coe Downward (eval env t)

force :: Val -> Val
force = \case
  VFlex m sp | Solved t <- lookupMeta m -> force (vAppSp t sp)
  t -> t

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  [] -> t
  sp :> (u, q, i) -> App (quoteSp l t sp) (quote l u) q i

quote :: Lvl -> Val -> Tm
quote l t = trace ("trying to quote " ++ show t) $ case force t of
  VFlex m sp -> quoteSp l (Meta m) sp
  VRigid x q sp -> quoteSp l (wrapMode q (Var (lvl2Ix l x))) sp
  VLam x q i t -> Lam x q i (quote (l + 1) (t $$ VVar l (AtMode q)))
  VPi x q i a b -> Pi x q i (quote l a) (quote (l + 1) (b $$ VVar l (AtMode Zero)))
  VU -> U

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)
