module Extraction where

import Code (Code (..))
import Common (Ix (..), Lvl (..), Marker (..), Mode (..))
import Data.Maybe (fromJust)
import Evaluation
import Syntax (Tm (..))
import Value (Env, IsUpped (NotUpped), pattern VVar)

-- The environment used during extraction
--
-- It consists of the evaluation environment, and a list of *real* levels
-- that track how many irrelevant variables have been skipped.
--      | n(env) | env | n(real) | real |
type ExEnv = (Int, Env, Int, [Maybe Lvl])

-- Only allowed to extract closed terms
extract :: Tm -> Code
extract t = go (0, [], 0, []) t
  where
    extend :: ExEnv -> Mode -> ExEnv
    extend (n, env, rn, real) q@Zero = (n + 1, VVar (Lvl n) q : env, rn, Nothing : real)
    extend (n, env, rn, real) q@Omega = (n + 1, VVar (Lvl n) q : env, rn + 1, Just (Lvl rn) : real)

    goMeta :: ExEnv -> Tm -> Code
    goMeta exenv@(n, env, _, _) t = case tryForce (eval Absent env t) of
      Just t' -> go exenv (quote (Lvl n) t')
      Nothing -> error "extracting unsolved Meta"

    go :: ExEnv -> Tm -> Code
    go env@(n, _, rn, real) t = case t of
      Var (Ix x) -> CVar (lvl2Ix (Lvl rn) (fromJust $ real !! x))
      App t u Omega i -> CApp (go env t) (go env u)
      App t u Zero i -> go env t
      Lam x Omega i t -> CLam x (go (extend env Omega) t)
      Lam x Zero i t -> go (extend env Zero) t
      Let x Omega _ t u -> CLet x (go env t) (go (extend env Omega) u)
      Let x Zero _ t u -> go (extend env Zero) u
      Meta _ _ -> goMeta env t
      InsertedMeta _ _ _ -> goMeta env t
      Pi x q i a b -> error "extracting Pi"
      U -> error "extracting U"
      Up t -> error "extracting Up"
      Down t -> error "extracting Down"