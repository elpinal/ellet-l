module Language.ElletL.Interpreter
  ( interpretProgram
  , Env(..)
  ) where

import Control.Exception.Safe
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import qualified Data.Map.Lazy as Map

import Language.ElletL.Syntax

lookupCLab :: MonadThrow m => CLab -> Interpreter m Block
lookupCLab cl = lift (lift ask) >>= maybe (throwI $ NoSuchCLab cl) return . Map.lookup cl . unCodeSec

fromCLab :: MonadThrow m => Val -> Interpreter m CLab
fromCLab (VCLab cl) = return cl
fromCLab v = throwI $ ExpectedCLab v

alterCell :: Offset -> Val -> HVal -> HVal
alterCell Zero v (HVal _ v2) = HVal v v2
alterCell One v (HVal v1 _) = HVal v1 v

lookupLab :: MonadThrow m => Lab -> Interpreter m HVal
lookupLab l = lift (gets heap) >>= maybe (throwI $ NoSuchLab l) return . Map.lookup l . unHeap

fromLab :: MonadThrow m => Val -> Interpreter m Lab
fromLab (VLab l) = return l
fromLab v = throwI $ ExpectedLab v

hValueOf :: MonadThrow m => Val -> Interpreter m HVal
hValueOf v = fromLab v >>= lookupLab

readHVal :: Offset -> HVal -> Val
readHVal Zero (HVal v _) = v
readHVal One (HVal _ v) = v

writeHeap :: MonadThrow m => Lab -> HVal -> Interpreter m ()
writeHeap l hv = lift $ modify $ updateHeap $ mapHeap $ Map.insert l hv

lookupReg :: MonadThrow m => Reg -> Interpreter m Val
lookupReg r = lift (gets file) >>= maybe (throwI $ NoSuchRegister r) return . Map.lookup r . unFile

valueOf :: MonadThrow m => Operand -> Interpreter m Val
valueOf (Register r) = lookupReg r
valueOf (Int i) = return $ VInt i
valueOf (Func cl) = return $ VCLab cl
valueOf (TApp op _) = valueOf op
valueOf (Pack _ op _) = valueOf op
valueOf (Fold _ op) = valueOf op
valueOf (Unfold op) = valueOf op

writeReg :: MonadThrow m => Reg -> Val -> Interpreter m ()
writeReg r v = lift $ modify $ updateFile $ mapFile $ Map.insert r v

data Env = Env
  { heap :: Heap
  , file :: File
  }
  deriving Show

updateHeap :: (Heap -> Heap) -> Env -> Env
updateHeap f e = e { heap = f $ heap e }

updateFile :: (File -> File) -> Env -> Env
updateFile f e = e { file = f $ file e }

type Interpreter m = ContT () (StateT Env (ReaderT CodeSec m))

interpretProgram :: MonadThrow m => Block -> CodeSec -> Env -> m Env
interpretProgram b = runInterpreter $ interpret b

runInterpreter :: MonadThrow m => Interpreter m () -> CodeSec -> Env -> m Env
runInterpreter i c e = (`runReaderT` c) $ (`execStateT` e) $ evalContT i

-- Note that in this interpreter jumping to the code label named "exit"
-- indicates that the program is interpreted successfully
-- (regardless of the existence of the "exit" code block).
-- Moreover, the halt instruction indicates that memory runs out.
-- Integer arithmetic can induce overflow in the sense of Haskell's Int type.
interpret :: MonadThrow m => Block -> Interpreter m ()
interpret (Block is t) = mapM_ interp is >> terminator t >>= interpret

interp :: MonadThrow m => Inst -> Interpreter m ()
interp (Mov r op) = valueOf op >>= writeReg r
interp (Add r1 r2 op) = arith (+) <$> lookupReg r2 <*> valueOf op >>= id >>= writeReg r1
interp (Sub r1 r2 op) = arith (-) <$> lookupReg r2 <*> valueOf op >>= id >>= writeReg r1
interp (Mul r1 r2 op) = arith (*) <$> lookupReg r2 <*> valueOf op >>= id >>= writeReg r1
interp (Ld r1 r2 off) = lookupReg r2 >>= hValueOf >>= writeReg r1 . readHVal off
interp (St r1 off r2) = do
  l <- lookupReg r1 >>= fromLab
  alterCell off <$> lookupReg r2 <*> lookupLab l >>= writeHeap l
interp (Bnz r op) = do
  v <- lookupReg r
  unless (isZero v) $ do
    jmp op >>= interpret
    ContT $ const $ return ()
interp (Unpack _ r op) = valueOf op >>= writeReg r -- same as Mov.

isZero :: Val -> Bool
isZero (VInt 0) = True
isZero _ = False

arith :: MonadThrow m => (Int -> Int -> Int) -> Val -> Val -> Interpreter m Val
arith f (VInt i1) (VInt i2) = return $ VInt $ i1 `f` i2
arith _ (VInt _) v = throwI $ ExpectedInt v
arith _ v (VInt _) = throwI $ ExpectedInt v
arith _ v1 v2 = throwI $ ExpectedInts v1 v2

terminator :: MonadThrow m => Terminator -> Interpreter m Block
terminator (Jmp op) = jmp op
terminator Halt = throwI MemoryRanOut

jmp :: MonadThrow m => Operand -> Interpreter m Block
jmp op = do
  cl <- valueOf op >>= fromCLab
  if isExit cl
    then ContT $ const $ return ()
    else lookupCLab cl

isExit :: CLab -> Bool
isExit (CLab s) = s == "exit"

throwI :: (MonadThrow m, Exception e) => e -> Interpreter m a
throwI = lift . lift . lift . throwM

data InterpreterException
  = MemoryRanOut
  | NoSuchRegister Reg
  | NoSuchLab Lab
  | NoSuchCLab CLab
  | ExpectedLab Val
  | ExpectedCLab Val
  | ExpectedInt Val
  | ExpectedInts Val Val
  deriving Show

instance Exception InterpreterException
