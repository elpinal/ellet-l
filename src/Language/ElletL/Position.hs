{-# LANGUAGE DeriveFunctor #-}

module Language.ElletL.Position
  ( Positional(..)
  , getPosition
  , fromPositional
  , Position(..)
  , Point(..)
  , initialPoint
  , incPoint
  , newline
  ) where

data Positional a = Positional Position a
  deriving (Functor, Show)

getPosition :: Positional a -> Position
getPosition (Positional p _) = p

fromPositional :: Positional a -> a
fromPositional (Positional _ x) = x

data Position = Position Point Point
  deriving (Eq, Show)

data Point = Point
  { line :: Int
  , column :: Int
  }
  deriving (Eq, Show)

initialPoint :: Point
initialPoint = Point 0 0

incPoint :: Point -> Point
incPoint p = p { column = column p + 1 }

newline :: Point -> Point
newline p = p { line = line p + 1, column = 0 }
