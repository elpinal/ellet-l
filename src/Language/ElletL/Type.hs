{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Language.ElletL.Type
  ( wfProgram
  , Sig(..)
  , Typed(..)
  -- * Errors
  , TypeError(..)
  ) where

import Control.Monad
import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.Reader
import Control.Monad.Freer.State
import Data.Functor.Classes
import qualified Data.Map.Lazy as Map

import Language.ElletL.Subst
import Language.ElletL.Syntax

wfProgram :: Sig -> Heap -> File -> Context -> CodeSec -> Block -> Either TypeError ()
wfProgram s h f ctx cs b = run $ runError $ runReader s $ do
  wfCodeSec cs
  checkFileAndHeap f ctx h
  evalState (TypeContext []) $ evalState ctx $ wfB b

data Sign
  = Plus
  | Minus
  | Neutral
  deriving Show

newtype TypeContext = TypeContext { getTypeContext :: [Sign] }
  deriving Show

getSign :: Member (Error TypeError) r => Int -> TypeContext -> Eff r Sign
getSign i (TypeContext xs)
  | 0 <= i && i < length xs = return $ xs !! i
  | otherwise = throwErrorP $ UnboundTypeVariable (TypeContext xs) i

push :: Sign -> TypeContext -> TypeContext
push s (TypeContext xs) = TypeContext $ s : xs

invert :: TypeContext -> TypeContext
invert (TypeContext xs) = TypeContext $ map f xs
  where
    f Plus = Minus
    f Minus = Plus
    f Neutral = Neutral

-- In the following, "wf" stands for "well-formed".

class WellFormed a where
  wf :: Members '[Reader TypeContext, Error TypeError] r => a -> Eff r ()

instance WellFormed Type where
  wf (Forall _ t) = local (push Neutral) $ wf t
  wf TInt = return ()
  wf Word = return ()
  wf (Code ctx) = local invert $ mapM_ wf $ Map.elems $ getContext ctx

instance WellFormed LType where
  wf (TVar i) = ask >>= getSign i >>= f
    where
      f Minus = throwErrorP $ UnexpectedMinus i
      f _ = return ()
  wf (Type t) = wf t
  wf (Nullable mt) = wf mt
  wf (Ref mt) = wf mt
  wf (Exist _ lt) = local (push Neutral) $ wf lt
  wf (Rec s (TVar 0)) = throwErrorP $ NonContractiveRecType s
  wf (Rec _ lt) = local (push Plus) $ wf lt

instance WellFormed MType where
  wf (MType lt1 lt2) = mapM_ wf [lt1, lt2]

newtype Sig = Sig { getSig :: Map.Map CLab Type }

lookupSig :: CLab -> Sig -> Maybe Type
lookupSig cl (Sig m) = Map.lookup cl m

-- |
-- Note that @wfCodeSec@ checks that the domain of the code section and the
-- domain of the signature coincide.
wfCodeSec :: Members '[Error TypeError, Reader Sig] r => CodeSec -> Eff r ()
wfCodeSec x = evalState x $ do
  m <- asks getSig
  forM_ (Map.toList m) $ \(cl, t) -> do
    (ctx, tctx) <- runState (TypeContext []) $ expectCode t
    runReader (TypeContext []) $ wf t
    csm <- gets unCodeSec
    case dropMap cl csm of
      Found b csm' -> do
        evalState tctx $ evalState ctx $ wfB b
        put $ CodeSec csm'
      Missing -> throwErrorP $ NoSuchCodeLabel cl
  cs <- get
  unless (Map.null $ unCodeSec cs) $
    throwErrorP $ LackingTypeInformation cs

expectCode :: (Members '[State TypeContext, Error TypeError] r) => Type -> Eff r Context
expectCode (Code ctx) = return ctx
expectCode (Forall _ t) = modify (push Neutral) >> expectCode t
expectCode t = throwErrorP $ NonCodeLabelType t

checkFileAndHeap :: Members '[Reader Sig, Error TypeError] r => File -> Context -> Heap -> Eff r ()
checkFileAndHeap file ctx heap = do
  heap' <- execState heap $ check file ctx
  unless (Map.null $ unHeap heap') $
    throwErrorP $ UnusedLabels heap'

check :: Members '[State Heap, Reader Sig, Error TypeError] r => File -> Context -> Eff r ()
check file ctx = do
  f <- execState file $ mapM_ checkFile $ Map.toList $ getContext ctx
  unless (Map.null $ unFile f) $
    throwErrorP $ LackingTypeInformationForFile f

checkFile :: Members '[State File, State Heap, Reader Sig, Error TypeError] r => (Reg, LType) -> Eff r ()
checkFile (r, lt) = do
  File m <- get
  case dropMap r m of
    Found v m' -> checkValue v lt >> put (File m')
    Missing -> throwErrorP $ NoSuchRegister r

checkValue :: Members '[State Heap, Reader Sig, Error TypeError] r => Val -> LType -> Eff r ()
checkValue (VInt n) lt = checkInt n lt
checkValue (VCLab cl) lt = do
  sig <- ask
  t <- lookupSig cl sig !? NoSuchCodeLabel cl
  mustIdentical (Type t) lt
checkValue (VLab l) lt = useLabel l >>= (`checkHeapValue` lt)

checkHeapValue :: Members '[State Heap, Reader Sig, Error TypeError] r => HVal -> LType -> Eff r ()
checkHeapValue (HVal v1 v2) (Ref (MType lt1 lt2)) = checkValue v1 lt1 >> checkValue v2 lt2
checkHeapValue _ lt = throwErrorP $ NonReferenceType lt

data Drop d a
  = Found d a
  | Missing
  deriving Functor

dropMap :: Ord k => k -> Map.Map k a -> Drop a (Map.Map k a)
dropMap k m = Map.alterF (maybe Missing (`Found` Nothing)) k m

dropLabel :: Lab -> Heap -> Drop HVal Heap
dropLabel l (Heap m) = Heap <$> dropMap l m

useLabel :: Members '[State Heap, Error TypeError] r => Lab -> Eff r HVal
useLabel l = do
  d <- gets $ dropLabel l
  case d of
    Found hv heap -> put heap >> return hv
    Missing -> throwErrorP $ UsedOrUnboundLabel l

checkInt :: Members '[Error TypeError] r => Int -> LType -> Eff r ()
checkInt 0 (Nullable mt) = runReader (TypeContext []) $ wf mt
checkInt _ (Type TInt) = return ()
checkInt n lt = throwErrorP $ IllTypedIntValue n lt

(!?) :: Member (Error TypeError) r => Maybe a -> Problem -> Eff r a
(!?) m p = maybe (throwErrorP p) return m

class Typed a where
  typeOf :: Members '[Reader TypeContext, State Context, Reader Sig, Error TypeError] r => a -> Eff r LType

instance Typed Reg where
  typeOf r = gets getContext >>= maybe (throwErrorP $ NoSuchRegister r) return . Map.lookup r

use :: Member (State Context) r => Reg -> LType -> Eff r ()
use _ (Type _) = return ()
use r _ = updateReg r $ Type Word

instance Typed Operand where
  typeOf (Register r)     = typeOf r >>= (<$) <*> use r
  typeOf (Int _)          = return $ Type TInt
  typeOf (Func cl)        = fmap Type $ ask >>= \sig -> lookupSig cl sig !? NoSuchCodeLabel cl
  typeOf (TApp op lt)     = wf lt >> typeOf op >>= instantiate lt
  typeOf (Pack rep op lt) = mustIdentical <$> ((`substTop` rep) <$> fromExist lt) <*> typeOf op >>= id >> return lt
  typeOf (Fold lt op)     = mustIdentical <$> ((`substTop` lt) <$> fromRec lt) <*> typeOf op >>= id >> return lt
  typeOf (Unfold op)      = typeOf op >>= fmap <$> flip substTop <*> fromRec

mustIdentical :: Member (Error TypeError) r => LType -> LType -> Eff r ()
mustIdentical x y
  | identical x y = return ()
  | otherwise = throwErrorP $ NotIdentical x y

-- fromRec (rec X. T) == T.
fromRec :: Member (Error TypeError) r => LType -> Eff r LType
fromRec (Rec _ lt) = return lt
fromRec lt = throwErrorP $ NonRecursiveType lt

fromExist :: Member (Error TypeError) r => LType -> Eff r LType
fromExist (Exist _ lt) = return lt
fromExist lt = throwErrorP $ NonExistentialType lt

instantiate :: Member (Error TypeError) r => LType -> LType -> Eff r LType
instantiate by (Type (Forall _ t)) = return $ Type $ substTop t by
instantiate _ lt = throwErrorP $ NonPolymorphicType lt

insert :: Reg -> LType -> Context -> Context
insert r lt (Context m) = Context $ Map.insert r lt m

updateReg :: Member (State Context) r => Reg -> LType -> Eff r ()
updateReg r lt = modify $ insert r lt

shiftContext :: Member (State Context) r => Eff r ()
shiftContext = modify $ (shift 1 :: Context -> Context)

type InstEffs = '[State TypeContext, State Context, Reader Sig, Error TypeError]

typeOfS :: (Typed a, Members InstEffs r) => a -> Eff r LType
typeOfS x = do
  tctx <- get
  runReader (tctx :: TypeContext) $ typeOf x

wfB :: Members InstEffs r => Block -> Eff r ()
wfB (Block is t) = mapM_ wfInst is >> wfT t

wfT :: Members InstEffs r => Terminator -> Eff r ()
wfT (Jmp op) = match <$> get <*> (typeOfS op >>= fromCode) >>= id
wfT Halt = return ()

wfInst :: Members InstEffs r => Inst -> Eff r ()
wfInst (Mov r op)      = typeOfS r >>= fromUnrestricted >> typeOfS op >>= updateReg r
wfInst (Add r1 r2 op)  = wfArith r1 r2 op
wfInst (Sub r1 r2 op)  = wfArith r1 r2 op
wfInst (Mul r1 r2 op)  = wfArith r1 r2 op
wfInst (Ld r1 r2 off)  = typeOfS r1 >>= fromUnrestricted >> typeOfS r2 >>= withRef off (updateReg r1) (updateReg r2)
wfInst (St r1 off r2)  = store off <$> typeOfS r1 <*> typeOfS r2 >>= id >>= updateReg r1
wfInst (Bnz r op)      = match <$> ((typeOfS r >>= cond r) <*> get) <*> (typeOfS op >>= fromCode) >>= id
wfInst (Unpack _ r op) = typeOfS r >>= fromUnrestricted >> typeOfS op >>= fromExist >>= (shiftContext >>) . (modify (push Neutral) >>) . updateReg r

wfArith :: Members InstEffs r => Reg -> Reg -> Operand -> Eff r ()
wfArith r1 r2 op = typeOfS r1 >>= fromUnrestricted >> typeOfS r2 >>= fromInt >> typeOfS op >>= fromInt >> updateReg r1 (Type TInt)

cond :: Member (Error TypeError) r => Reg -> LType -> Eff r (Context -> Context)
cond _ (Type TInt)   = return id
cond r (Nullable mt) = return $ insert r $ Ref mt
cond _ ltr           = throwErrorP $ Conditional ltr

withRef :: Member (Error TypeError) r => Offset -> (LType -> Eff r ()) -> (LType -> Eff r ()) -> LType -> Eff r ()
withRef Zero f g (Ref (MType x y)) = f x >> g (Ref $ MType (used x) y)
withRef One  f g (Ref (MType x y)) = f y >> g (Ref $ MType x $ used y)
withRef _ _ _ lt = throwErrorP $ NonReferenceType lt

used :: LType -> LType
used (Type t) = Type t
used _ = Type Word

store :: Member (Error TypeError) r => Offset -> LType -> LType -> Eff r LType
store Zero (Ref (MType _ y)) x = return $ Ref $ MType x y
store One  (Ref (MType x _)) y = return $ Ref $ MType x y
store _ lt _ = throwErrorP $ NonReferenceType lt

fromInt :: Member (Error TypeError) r => LType -> Eff r ()
fromInt (Type TInt) = return ()
fromInt lt = throwErrorP $ NonIntType lt

fromUnrestricted :: Member (Error TypeError) r => LType -> Eff r Type
fromUnrestricted (Type t) = return t
fromUnrestricted lt = throwErrorP $ NonUnrestrictedType lt

fromCode :: Member (Error TypeError) r => LType -> Eff r Context
fromCode (Type (Code ctx)) = return ctx
fromCode lt = throwErrorP $ NonCodeType lt

match :: Member (Error TypeError) r => Context -> Context -> Eff r ()
match x y = if identical x y then return () else throwErrorP $ ContextMismatch x y

-- | @identical x y@ returns @True@ if and only if the two terms are alpha-equivalent.
class Identical a where
  identical :: a -> a -> Bool

instance Identical Context where
  identical (Context x) (Context y) = liftEq identical x y

instance Identical Type where
  identical (Forall _ x) (Forall _ y) = identical x y
  identical (Code x) (Code y) = identical x y
  identical x y = x == y

instance Identical LType where
  identical (TVar x) (TVar y) = x == y
  identical (Type x) (Type y) = identical x y
  identical (Nullable x) (Nullable y) = identical x y
  identical (Ref x) (Ref y) = identical x y
  identical (Exist _ x) (Exist _ y) = identical x y
  identical (Rec _ x) (Rec _ y) = identical x y
  identical _ _ = False

instance Identical MType where
  identical (MType x1 x2) (MType y1 y2) = identical x1 y1 && identical x2 y2

throwErrorP :: Member (Error TypeError) r => Problem -> Eff r a
throwErrorP = throwError . TypeError []

data TypeError = TypeError [Reason] Problem

instance Show TypeError where
  show (TypeError [] p) = show p
  show (TypeError _ _) = error "error"

data Problem
  = UnboundTypeVariable TypeContext Int
  | UsedOrUnboundLabel Lab -- the label is either used twice (or more), or unbound in the heap.
  | NoSuchRegister Reg -- no such register in the context.
  | NoSuchCodeLabel CLab

  | UnusedLabels Heap -- forgetting labels, which contain linear values, is forbidden in the linear type system.
  | LackingTypeInformation CodeSec
  | LackingTypeInformationForFile File

  | UnexpectedMinus Int

  | Conditional LType -- the conditional of "bnz" instruction should be an integer or a nullable reference.

  | ContextMismatch Context Context
  | NotIdentical LType LType

  | NonPolymorphicType LType
  | NonExistentialType LType
  | NonContractiveRecType String -- @rec X. X@ is ill-formed.
  | NonRecursiveType LType
  | NonUnrestrictedType LType
  | NonIntType LType
  | NonCodeType LType -- expected @Type (Code ctx)@
  | NonCodeLabelType Type -- expected @Type (Forall ... (Code ctx))@
  | NonReferenceType LType

  | IllTypedIntValue Int LType
  deriving Show

data Reason
