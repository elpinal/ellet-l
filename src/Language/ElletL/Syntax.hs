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
  , Type(..)
  , LType(..)
  , MType(..)
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
  | Pack Type Operand Type -- pack [rep, op] as ty
  | Fold Type Operand -- fold [ty] op
  | Unfold Operand -- unfold op

data Offset
  = Zero
  | One

data Inst
  = Mov Reg Operand
  | Add Reg Reg Operand
  | Sub Reg Reg Operand
  | Mul Reg Reg Operand
  | Ld Reg Reg Offset
  | St Reg Offset Reg
  | Bnz Reg Operand
  | Unpack String Reg Operand -- unpack [a, r] op

data Terminator
  = Jmp Operand
  | Halt

data Block = Block [Inst] Terminator


newtype Context = Context { getContext :: Map.Map Reg LType }

data Type
  = Forall String Type
  | TInt
  | Word
  | Code Context

data LType
  = TVar Int
  | Type Type
  | Nullable MType
  | Ref MType
  | Exist String LType
  | Rec String LType

data MType = MType LType LType
