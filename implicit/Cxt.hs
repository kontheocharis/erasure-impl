module Cxt where

import Common
import Evaluation
import Pretty
import Syntax
import Value

-- Elaboration context
--------------------------------------------------------------------------------

data NameOrigin = Inserted | Source deriving (Eq)

type Types = [(String, NameOrigin, VTy)]

data Cxt = Cxt
  { -- used for:
    -----------------------------------
    env :: Env, -- evaluation
    lvl :: Lvl, -- unification
    types :: Types, -- raw name lookup, pretty printing
    modes :: [Mode], -- context modes
    bds :: [BD], -- fresh meta creation
    pos :: SourcePos, -- error reporting
    md :: Mode -- elaboration mode. Zero means erasure marker is present, Omega means absent
  }

cxtNames :: Cxt -> [Name]
cxtNames = fmap (\(x, _, _) -> x) . types

showVal :: Cxt -> Val -> String
showVal cxt v =
  prettyTm 0 (cxtNames cxt) (quote (lvl cxt) v) []

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (cxtNames cxt) t []

instance Show Cxt where
  show = show . cxtNames

emptyCxt :: SourcePos -> Cxt
emptyCxt p = Cxt [] 0 [] [] [] p Omega

-- | Extend Cxt with a bound variable.
bind :: Cxt -> Name -> Mode -> VTy -> Cxt
bind (Cxt env l types modes bds pos md) x q ~a =
  Cxt (env :> VVar l q) (l + 1) (types :> (x, Source, a)) (modes :> q) (bds :> Bound q) pos md

-- | Insert a new binding.
newBinder :: Cxt -> Name -> Mode -> VTy -> Cxt
newBinder (Cxt env l types modes bds pos md) x q ~a =
  Cxt (env :> VVar l q) (l + 1) (types :> (x, Inserted, a)) (modes :> q) (bds :> Bound q) pos md

-- | Extend Cxt with a definition.
define :: Cxt -> Name -> Mode -> Val -> VTy -> Cxt
define (Cxt env l types modes bds pos md) x q ~t ~a =
  Cxt (env :> t) (l + 1) (types :> (x, Source, a)) (modes :> q) (bds :> Defined) pos md

-- | closeVal : (Γ : Con) → Val (Γ, x : A) B → Closure Γ A B
closeVal :: Cxt -> Val -> Closure
closeVal cxt t = Closure (env cxt) (quote (lvl cxt + 1) t)

-- | closeVal : (Γ : Con) → Val (Γ, x : A) B → Closure Γ A B
enter :: Cxt -> Mode -> Cxt
enter (Cxt env l types modes bds pos md) md' = Cxt env l types modes bds pos (mult md md')
