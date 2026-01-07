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
-- `Omega` (because we are in a non-erased context).
data VarMode = AtMode Mode | Upped | Downed
  deriving (Show)

type Spine = [(Val, Mode, Icit)]

data Closure = Closure Env Tm
  deriving (Show)

type VTy = Val

data Val
  = VFlex MetaVar Spine
  | VRigid Lvl VarMode Spine -- default in its declared mode
  | VLam Name Mode Icit {-# UNPACK #-} Closure -- default in mode ω
  | VPi Name Mode Icit ~VTy {-# UNPACK #-} Closure -- always in mode 0
  | VU -- always in mode 0
  deriving (Show)

pattern VVar :: Lvl -> VarMode -> Val
pattern VVar x m = VRigid x m []

pattern VMeta :: MetaVar -> Val
pattern VMeta m = VFlex m []

moveVarMode :: Dir -> VarMode -> VarMode
moveVarMode Upward (AtMode Zero) = Upped
moveVarMode Upward (AtMode Omega) = error "impossible"
moveVarMode Upward Upped = error "impossible"
moveVarMode Upward Downed = AtMode Omega
moveVarMode Downward (AtMode Omega) = Downed
moveVarMode Downward (AtMode Zero) = error "impossible"
moveVarMode Downward Downed = error "impossible"
moveVarMode Downward Upped = AtMode Zero

diffVarMode :: Mode -> Mode -> VarMode
diffVarMode Omega Zero = Downed
diffVarMode Zero Omega = Upped
diffVarMode m _ = AtMode m

wrapMode :: VarMode -> (Mode -> Tm) -> Tm
wrapMode (AtMode m) f = f m
wrapMode Upped f = Up (f Zero)
wrapMode Downed f = Down (f Omega)
