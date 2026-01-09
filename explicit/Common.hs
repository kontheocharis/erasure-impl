module Common
  ( module Common,
    SourcePos (..),
    Pos,
    unPos,
    initialPos,
  )
where

import Text.Megaparsec

type Name = String

data Mode = Zero | Omega deriving (Eq)

data Marker = Present | Absent deriving (Eq, Show)

mult :: Mode -> Mode -> Mode
mult Zero _ = Zero
mult _ Zero = Zero
mult Omega Omega = Omega

ext :: Marker -> Marker -> Marker
ext Present _ = Present
ext _ Present = Present
ext Absent Absent = Absent

getMode :: Marker -> Mode
getMode Present = Zero
getMode Absent = Omega

getMarker :: Mode -> Marker
getMarker Zero = Present
getMarker Omega = Absent

data Dir = Upward | Downward deriving (Eq, Show)

invertDir :: Dir -> Dir
invertDir Upward = Downward
invertDir Downward = Upward

data Icit = Impl | Expl deriving (Eq)

data BD = Bound Mode | Defined deriving (Show)

instance Show Mode where
  show Zero = "0"
  show Omega = "ω"

instance Show Icit where
  show Impl = "implicit"
  show Expl = "explicit"

-- | De Bruijn index.
newtype Ix = Ix {unIx :: Int} deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Ord, Show, Num) via Int

newtype MetaVar = MetaVar {unMetaVar :: Int} deriving (Eq, Show, Num) via Int

-- Snoc
--------------------------------------------------------------------------------

infixl 4 :>

pattern (:>) :: [a] -> a -> [a]
pattern xs :> x <- x : xs where (:>) xs ~x = x : xs

{-# COMPLETE (:>), [] #-}
