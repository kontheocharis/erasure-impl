module Value where

import Common
import Syntax

type Env = [Val]

type Spine = [(Val, Mode, Icit)]

data Closure = Closure Env Tm deriving (Show)

type VTy = Val

data Val
  = VFlex MetaVar Mode Spine
  | VRigid Lvl Mode Spine
  | VLam Name Mode Icit {-# UNPACK #-} Closure
  | VPi Name Mode Icit ~VTy {-# UNPACK #-} Closure
  | VU
  deriving (Show)

pattern VVar :: Lvl -> Mode -> Val
pattern VVar x q = VRigid x q []

pattern VMeta :: MetaVar -> Mode -> Val
pattern VMeta m q = VFlex m q []
