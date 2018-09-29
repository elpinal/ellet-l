{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Language.ElletL.Stream
  ( Stream(..)
  , stream
  , runStream
  ) where

import Control.Monad.Freer
import Control.Monad.Freer.State

import Language.ElletL.Position

data Stream a where
  Stream :: Stream (Maybe Char)

stream :: Member Stream r => Eff r (Maybe Char)
stream = send Stream

runStream :: Member (State Point) r => Eff (Stream ': r) a -> Eff (State String ': r) a
runStream = reinterpret $ \Stream -> get >>= f
  where
    f [] = return Nothing
    f ('\n' : cs) = modify newline >> put cs >> return (Just '\n')
    f (c : cs) = modify incPoint >> put cs >> return (Just c)
