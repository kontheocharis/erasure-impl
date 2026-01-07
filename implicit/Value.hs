module Value where

import Common
import Syntax

type Env = [Val]

-- Data attached to a variable
--
-- If `AtMode m`, the variable is used at its declared mode `m`.
--
-- If `Upped`, the variable is used at mode `Omega` but declared at mode
-- `Zero` (because we are in an erased context).
--
-- If `Downed`, the variable is used at mode `Zero` but declared at mode
-- `Omega`
data VarMode = AtMode Mode | Upped | Downed
  deriving (Show)

type Spine = [(Val, Mode, Icit)]

data Closure = Closure Env Tm VarMode
  -- the `VarMode` indicates how the bound variable is used in the closure; the
  -- reverse operation must be applied when instantiating
  deriving (Show)

-- Whether an erased-only value is wrapped in Up
-- In the basic setting, this applies to types
data IsUpped = YesUpped | NotUpped
  deriving (Eq, Show)

type VTy = Val

data Val
  = VFlex MetaVar VarMode Spine
  | VRigid Lvl VarMode Spine
  | VLam Name Mode Icit {-# UNPACK #-} Closure
  | VPi IsUpped Name Mode Icit ~VTy {-# UNPACK #-} Closure
  | VU IsUpped
  deriving (Show)

pattern VVar :: Lvl -> VarMode -> Val
pattern VVar x q = VRigid x q []

pattern VMeta :: MetaVar -> VarMode -> Val
pattern VMeta m q = VFlex m q []

-- Move an IsUpped in a given direction, if possible
moveIsUpped :: Dir -> IsUpped -> IsUpped
moveIsUpped Upward NotUpped = YesUpped
moveIsUpped Upward YesUpped = error "impossible"
moveIsUpped Downward YesUpped = NotUpped
moveIsUpped Downward NotUpped = error "impossible"

-- Wrap a type in Up/Down if needed
wrapIsUpped :: IsUpped -> Tm -> Tm
wrapIsUpped NotUpped t = t
wrapIsUpped YesUpped t = Up t

-- Move a VarMode in a given direction, if possible
moveVarMode :: Dir -> VarMode -> VarMode
moveVarMode Upward (AtMode Zero) = Upped
moveVarMode Upward (AtMode Omega) = error "impossible"
moveVarMode Upward Upped = error "impossible"
moveVarMode Upward Downed = AtMode Omega
moveVarMode Downward (AtMode Omega) = Downed
moveVarMode Downward (AtMode Zero) = error "impossible"
moveVarMode Downward Downed = error "impossible"
moveVarMode Downward Upped = AtMode Zero

-- The difference between two modes as a VarMode
diffVarMode :: Mode -> Mode -> VarMode
diffVarMode Omega Zero = Downed
diffVarMode Zero Omega = Upped
diffVarMode m _ = AtMode m

-- Wrap a term in the coercion corresponding to the VarMode
wrapMode :: VarMode -> (Mode -> Tm) -> Tm
wrapMode (AtMode m) f = f m
wrapMode Upped f = Up (f Zero)
wrapMode Downed f = Down (f Omega)

invertVarMode :: VarMode -> Mode -> Maybe VarMode
invertVarMode (AtMode m) _ = Just $ AtMode m
invertVarMode Upped _ = Just $ Downed
invertVarMode Downed Zero = Just $ Upped
invertVarMode Downed _ = Nothing

-- Perform substitution: x@vq[x ↦ z@vq']
substVarMode :: VarMode -> VarMode -> VarMode
substVarMode (AtMode _) q = q
substVarMode q (AtMode _) = q
substVarMode Upped Downed = AtMode Omega
substVarMode Downed Upped = AtMode Zero
substVarMode q1 q2 = error "impossible"

-- The mode of a variable before any coercion is applied
varModeOriginalMode :: VarMode -> Mode
varModeOriginalMode (AtMode m) = m
varModeOriginalMode Upped = Zero
varModeOriginalMode Downed = Omega