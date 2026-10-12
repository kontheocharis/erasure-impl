module Value where

import Common
import Syntax

type Env = [Val]

type Spine = [(Val, Mode, Icit)]

data Closure = Closure Env Tm deriving (Show)

type VTy = Val

-- Each value is marked by whether it is coerced. There is only one possible
-- coercion per value.
data Val
  = VFlex MetaVar Marker Spine
  | VRigid Lvl Spine
  | VLam Name Mode Icit {-# UNPACK #-} Closure
  | VPi Name Mode Icit ~VTy {-# UNPACK #-} Closure
  | VU
  deriving (Show)

pattern VVar :: Lvl -> Val
pattern VVar x = VRigid x []

pattern VMeta :: MetaVar -> Marker -> Val
pattern VMeta m mrk = VFlex m mrk []