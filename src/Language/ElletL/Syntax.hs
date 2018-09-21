module Language.ElletL.Syntax
  ( Reg(..)
  , CLab(..)
  , Operand(..)
  , Offset(..)
  , Inst(..)
  , Terminator(..)
  , Block(..)
  ) where

newtype Reg = Reg Int
  deriving (Eq, Ord, Show)

newtype CLab = CLab String
  deriving (Eq, Ord, Show)

data Operand
  = Register Reg
  | Int Int
  | Func CLab

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

data Terminator
  = Jmp Operand
  | Halt

data Block = Block [Inst] Terminator
