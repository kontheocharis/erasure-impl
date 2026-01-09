module Value where

import Common
import Syntax

type Env = [Val]

type Spine = [(Val, Mode, Icit)]

data IsUpped = YesUpped | NotUpped
  deriving (Eq, Show)

data IsDowned = YesDowned | NotDowned
  deriving (Eq, Show)

data Closure = Closure Marker Env Tm IsDowned
  deriving (Show)

data ModeWrapped a = UpWrapped a | DownWrapped a | Plain a
  deriving (Show)

type VTy = Val

data Val
  = VFlex IsDowned MetaVar Marker Spine
  | VRigid IsDowned IsUpped Lvl Spine
  | VLam IsDowned Name Mode Icit {-# UNPACK #-} Closure
  | VPi IsUpped Name Mode Icit ~VTy {-# UNPACK #-} Closure
  | VU IsUpped
  deriving (Show)

-- Pattern for variables x0 or xω
pattern VVar :: Lvl -> Mode -> Val
pattern VVar x m <- (matchVVar -> Just (m, x))
  where
    VVar x Zero = VRigid YesDowned YesUpped x []
    VVar x Omega = VRigid NotDowned NotUpped x []

matchVVar :: Val -> Maybe (Mode, Lvl)
matchVVar (VRigid YesDowned YesUpped x []) = Just (Zero, x)
matchVVar (VRigid NotDowned NotUpped x []) = Just (Omega, x)
matchVVar _ = Nothing

pattern VMeta :: MetaVar -> Marker -> Val
pattern VMeta m mrk = VFlex NotDowned m mrk []

-- Pattern for variables ↑x0, ↓xω, and x0/xω
pattern VWrappedVar :: Lvl -> Maybe Dir -> Val
pattern VWrappedVar mw dir <- (matchVWrappedVar -> Just (mw, dir))
  where
    VWrappedVar x Nothing = VRigid YesDowned YesUpped x []
    VWrappedVar x (Just Upward) = VRigid YesDowned NotUpped x []
    VWrappedVar x (Just Downward) = VRigid NotDowned YesUpped x []

matchVWrappedVar :: Val -> Maybe (Lvl, Maybe Dir)
matchVWrappedVar (VRigid YesDowned YesUpped x []) = Just (x, Nothing)
matchVWrappedVar (VRigid YesDowned NotUpped x []) = Just (x, Just Downward)
matchVWrappedVar (VRigid NotDowned NotUpped x []) = Just (x, Nothing)
matchVWrappedVar (VRigid NotDowned YesUpped x []) = Just (x, Just Upward)
matchVWrappedVar _ = Nothing

-- Move an IsUpped in a given direction, if possible
moveIsUpped :: Dir -> IsUpped -> IsUpped
moveIsUpped Upward NotUpped = YesUpped
moveIsUpped Upward YesUpped = error "impossible"
moveIsUpped Downward YesUpped = NotUpped
moveIsUpped Downward NotUpped = error "impossible"

moveIsDowned :: Dir -> IsDowned -> IsDowned
moveIsDowned Upward NotDowned = error "impossible"
moveIsDowned Upward YesDowned = NotDowned
moveIsDowned Downward NotDowned = YesDowned
moveIsDowned Downward YesDowned = error "impossible"

-- Wrap a type in Up/Down if needed
ifIsUpped :: (a -> a) -> IsUpped -> a -> a
ifIsUpped f NotUpped = id
ifIsUpped f YesUpped = f

ifIsDowned :: (a -> a) -> IsDowned -> a -> a
ifIsDowned f NotDowned = id
ifIsDowned f YesDowned = f

--
fromZero :: Mode -> Maybe Dir
fromZero Zero = Nothing
fromZero Omega = Just Upward

downToZero :: Mode -> IsDowned
downToZero Zero = NotDowned
downToZero Omega = YesDowned

wrappedDirection :: ModeWrapped a -> Maybe Dir
wrappedDirection (Plain _) = Nothing
wrappedDirection (UpWrapped _) = Just Upward
wrappedDirection (DownWrapped _) = Just Downward