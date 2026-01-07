module Value where

import Common
import Syntax

type Env = [Val]

type Spine = [(Val, Mode, Icit)]

data Closure = Closure Env Tm

type VTy = Val

data Val
  = VFlex MetaVar Spine
  | VRigid Lvl Mode Spine
  | VLam Name Mode Icit {-# UNPACK #-} Closure
  | VPi Name Mode Icit ~VTy {-# UNPACK #-} Closure
  | VU

pattern VVar :: Lvl -> Mode -> Val
pattern VVar x m = VRigid x m []

pattern VMeta :: MetaVar -> Val
pattern VMeta m = VFlex m []
