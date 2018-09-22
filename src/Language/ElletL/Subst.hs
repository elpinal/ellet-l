{-# LANGUAGE DeriveFunctor #-}

module Language.ElletL.Subst
  ( substTop
  ) where

import Control.Monad.Free

import Language.ElletL.Syntax

shiftAbove :: Mapper a => Int -> Int -> a -> a
shiftAbove c0 d x = runTMap (tmap x) f c0
  where
    f c n
      | c <= n    = TVar $ n + d
      | otherwise = TVar n

shift :: Mapper a => Int -> a -> a
shift = shiftAbove 0

subst :: Mapper a => a -> Int -> LType -> a
subst x j lt = runTMap (tmap x) f 0
  where
    f c n
      | n == c + j = lt
      | otherwise  = TVar n

substTop :: Mapper a => a -> LType -> a
substTop x = shift (-1) . subst x 0 . shift 1

data TMap a
  = Inc a
  | Ask ((Int -> Int -> LType) -> a)
  | Look (Int -> a)
  deriving Functor

class Mapper a where
  tmap :: a -> Free TMap a

instance Mapper Type where
  tmap (Forall s t) = inc >> Forall s <$> tmap t
  tmap TInt         = return TInt
  tmap Word         = return Word
  tmap (Code ctx)   = Code <$> tmap ctx

instance Mapper Context where
  tmap (Context m) = Context <$> mapM tmap m

instance Mapper LType where
  tmap (TVar n)      = ask <*> look <*> return n
  tmap (Type t)      = Type <$> tmap t
  tmap (Nullable mt) = Nullable <$> tmap mt
  tmap (Ref mt)      = Ref <$> tmap mt
  tmap (Exist s lt)  = inc >> Exist s <$> tmap lt
  tmap (Rec s lt)    = inc >> Rec s <$> tmap lt

instance Mapper MType where
  tmap (MType lt1 lt2) = MType <$> tmap lt1 <*> tmap lt2

inc :: Free TMap ()
inc = Free $ Inc $ Pure ()

ask :: Free TMap (Int -> Int -> LType)
ask = Free $ Ask Pure

look :: Free TMap Int
look = Free $ Look Pure

runTMap :: Free TMap a -> (Int -> Int -> LType) -> Int -> a
runTMap (Pure a) _ _ = a
runTMap (Free (Inc f)) onvar c = runTMap f onvar (c + 1)
runTMap (Free (Ask f)) onvar c = runTMap (f onvar) onvar c
runTMap (Free (Look f)) onvar c = runTMap (f c) onvar c
