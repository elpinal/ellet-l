{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.ElletL.Syntax
  ( Reg(..)
  , CLab(..)
  , Operand(..)
  , Offset(..)
  , Inst(..)
  , Terminator(..)
  , Block(..)

  -- * Types
  , Context(..)
  , lookupContext
  , Type(..)
  , LType(..)
  , MType(..)

  -- * States
  , Lab(..)
  , Val(..)
  , File(..)
  , mapFile
  , HVal(..)
  , Heap(..)
  , mapHeap
  , CodeSec(..)
  ) where

import qualified Data.Map.Lazy as Map

newtype Reg = Reg Int
  deriving (Eq, Ord, Show)

newtype CLab = CLab String
  deriving (Eq, Ord, Show)

data Operand
  = Register Reg
  | Int Int
  | Func CLab
  | TApp Operand LType -- op [ty]
  | Pack LType Operand LType -- pack [rep, op] as ty
  | Fold LType Operand -- fold [ty] op
  | Unfold Operand -- unfold op
  deriving Show

data Offset
  = Zero
  | One
  deriving Show

data Inst
  = Mov Reg Operand
  | Add Reg Reg Operand
  | Sub Reg Reg Operand
  | Mul Reg Reg Operand
  | Ld Reg Reg Offset
  | St Reg Offset Reg
  | Bnz Reg Operand
  | Unpack String Reg Operand -- unpack [a, r] op
  deriving Show

data Terminator
  = Jmp Operand
  | Halt
  deriving Show

data Block = Block [Inst] Terminator
  deriving Show


newtype Context = Context { getContext :: Map.Map Reg LType }
  deriving (Eq, Show)

lookupContext :: Reg -> Context -> Maybe LType
lookupContext r (Context m) = Map.lookup r m

data Type
  = Forall String Type
  | TInt
  | Word
  | Code Context
  deriving (Eq, Show)

data LType
  = TVar Int
  | Type Type
  | Nullable MType
  | Ref MType
  | Exist String LType
  | Rec String LType
  deriving (Eq, Show)

data MType = MType LType LType
  deriving (Eq, Show)

newtype Lab = Lab String
  deriving (Eq, Ord, Show)

data Val
  = VInt Int
  | VLab Lab
  | VCLab CLab
  deriving Show

newtype File = File { unFile :: Map.Map Reg Val }
  deriving (Show, Semigroup, Monoid)

mapFile :: (Map.Map Reg Val -> Map.Map Reg Val) -> File -> File
mapFile f = File . f . unFile

data HVal = HVal Val Val
  deriving Show

newtype Heap = Heap { unHeap :: Map.Map Lab HVal }
  deriving (Show, Semigroup, Monoid)

mapHeap :: (Map.Map Lab HVal -> Map.Map Lab HVal) -> Heap -> Heap
mapHeap f = Heap . f . unHeap

newtype CodeSec = CodeSec { unCodeSec :: Map.Map CLab Block }
  deriving Show
