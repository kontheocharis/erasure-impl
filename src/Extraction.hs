module Extraction where

import Code (Code (..))
import Common (Lvl (..), Mode (..))
import Evaluation
import Syntax (Tm (..))
import Value (Env, VarMode (..), pattern VVar)

extend :: Env -> Mode -> Env
extend env q = VVar (Lvl (length env)) (AtMode q) : env

extractMeta :: Env -> Tm -> Code
extractMeta env t = case tryForce (eval env t) of
  Just t' -> extract env (quote (Lvl (length env)) t')
  Nothing -> error "extracting unsolved Meta"

-- Only allowed to extract open terms in a context with mode Omega.
-- Env is syntactic environment, *not* semantic environment.
extract :: Env -> Tm -> Code
extract env t = case t of
  Var x _ -> CVar x
  App t u Omega i -> CApp (extract env t) (extract env u)
  App t u Zero i -> extract env t
  Lam x Omega i t -> CLam x (extract (extend env Omega) t)
  Lam x Zero i t -> extract (extend env Zero) t
  Let x Omega _ t u -> CLet x (extract env t) (extract (extend env Omega) u)
  Let x Zero _ t u -> extract (extend env Zero) u
  Meta _ _ -> extractMeta env t
  InsertedMeta _ _ _ -> extractMeta env t
  Pi x q i a b -> error "extracting Pi"
  U -> error "extracting U"
  Up t -> error "extracting Up"
  Down t -> error "extracting Down"