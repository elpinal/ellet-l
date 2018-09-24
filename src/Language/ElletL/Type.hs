{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.ElletL.Type
  ( TypeChecker(..)
  -- * Errors
  , Error(..)
  ) where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Data.Functor.Classes
import qualified Data.Map.Lazy as Map

import Language.ElletL.Subst
import Language.ElletL.Syntax

data Sign
  = Plus
  | Minus
  | Neutral

newtype TypeContext = TypeContext { getTypeContext :: [Sign] }

getSign :: Int -> TypeContext -> TypeChecker Sign
getSign i (TypeContext xs)
  | 0 <= i && i < length xs = return $ xs !! i
  | otherwise = throwP $ UnboundTypeVariable (TypeContext xs) i

push :: Sign -> TypeContext -> TypeContext
push s (TypeContext xs) = TypeContext $ s : xs

invert :: TypeContext -> TypeContext
invert (TypeContext xs) = TypeContext $ map f xs
  where
    f Plus = Minus
    f Minus = Plus
    f Neutral = Neutral

-- In the following, "wf" stands for "well-formed".

newtype TypeChecker a = TypeChecker { runTypeChecker :: ReaderT TypeContext (StateT Context (ReaderT Sig (Either Error))) a }
  deriving (Functor, Applicative, Monad)

localT :: (TypeContext -> TypeContext) -> TypeChecker a -> TypeChecker a
localT f (TypeChecker m) = TypeChecker $ local f m

class WellFormed a where
  wf :: a -> TypeChecker ()

instance WellFormed Type where
  wf (Forall _ t) = localT (push Neutral) $ wf t
  wf TInt = return ()
  wf Word = return ()
  wf (Code ctx) = localT invert $ mapM_ wf $ Map.elems $ getContext ctx

instance WellFormed LType where
  wf (TVar i) = TypeChecker ask >>= getSign i >>= f
    where
      f Minus = throwP $ UnexpectedMinus i
      f _ = return ()
  wf (Type t) = wf t
  wf (Nullable mt) = wf mt
  wf (Ref mt) = wf mt
  wf (Exist _ lt) = localT (push Neutral) $ wf lt
  wf (Rec s (TVar 0)) = throwP $ NonContractiveRecType s
  wf (Rec _ lt) = localT (push Plus) $ wf lt

instance WellFormed MType where
  wf (MType lt1 lt2) = mapM_ wf [lt1, lt2]

newtype Sig = Sig { getSig :: Map.Map CLab Type }

wfSig :: TypeChecker ()
wfSig = (TypeChecker . lift . lift . asks) (Map.elems . getSig) >>= mapM_ (\t -> expectCode t >> wf t)

expectCode :: Type -> TypeChecker ()
expectCode (Code _) = return ()
expectCode (Forall _ t) = expectCode t
expectCode t = throwP $ NonCodeLabelType t

class Typed a where
  typeOf :: a -> TypeChecker LType

instance Typed Reg where
  typeOf r = TypeChecker (lift get) >>= maybe (throwP $ NoSuchRegister r) return . Map.lookup r . getContext

use :: Reg -> LType -> TypeChecker ()
use _ (Type _) = return ()
use r _ = updateReg r $ Type Word

instance Typed Operand where
  typeOf (Register r)     = typeOf r >>= (<$) <*> use r
  typeOf (Int _)          = return $ Type TInt
  typeOf (Func cl)        = fmap Type $ TypeChecker (lift $ lift $ asks $ Map.lookup cl . getSig) >>= maybe (throwP $ NoSuchCodeLabel cl) return
  typeOf (TApp op lt)     = wf lt >> typeOf op >>= instantiate lt
  typeOf (Pack rep op lt) = mustIdentical <$> ((`substTop` rep) <$> fromExist lt) <*> typeOf op >>= id >> return lt
  typeOf (Fold lt op)     = mustIdentical <$> ((`substTop` lt) <$> fromRec lt) <*> typeOf op >>= id >> return lt
  typeOf (Unfold op)      = typeOf op >>= fmap <$> flip substTop <*> fromRec

mustIdentical :: LType -> LType -> TypeChecker ()
mustIdentical x y
  | identical x y = return ()
  | otherwise = throwP $ NotIdentical x y

-- fromRec (rec X. T) == T.
fromRec :: LType -> TypeChecker LType
fromRec (Rec _ lt) = return lt
fromRec lt = throwP $ NonRecursiveType lt

fromExist :: LType -> TypeChecker LType
fromExist (Exist _ lt) = return lt
fromExist lt = throwP $ NonExistentialType lt

instantiate :: LType -> LType -> TypeChecker LType
instantiate by (Type (Forall _ t)) = return $ Type $ substTop t by
instantiate _ lt = throwP $ NonPolymorphicType lt

insert :: Reg -> LType -> Context -> Context
insert r lt (Context m) = Context $ Map.insert r lt m

updateReg :: Reg -> LType -> TypeChecker ()
updateReg r lt = TypeChecker $ lift $ modify $ insert r lt

currentContext :: TypeChecker Context
currentContext = TypeChecker $ lift get

shiftContext :: TypeChecker ()
shiftContext = TypeChecker $ lift $ modify $ shift 1

instance WellFormed Block where
  wf (Block is t) = mapM_ wf is >> wf t

instance WellFormed Terminator where
  wf (Jmp op) = match <$> currentContext <*> (typeOf op >>= fromCode) >>= id
  wf Halt = return ()

instance WellFormed Inst where
  wf (Mov r op) = typeOf r >>= fromUnrestricted >> typeOf op >>= updateReg r
  wf (Add r1 r2 op) = wfArith r1 r2 op
  wf (Sub r1 r2 op) = wfArith r1 r2 op
  wf (Mul r1 r2 op) = wfArith r1 r2 op
  wf (Ld r1 r2 off) = typeOf r1 >>= fromUnrestricted >> typeOf r2 >>= withRef off (updateReg r1) (updateReg r2)
  wf (St r1 off r2) = store off <$> typeOf r1 <*> typeOf r2 >>= id >>= updateReg r1
  wf (Bnz r op) = do
    ltr <- typeOf r
    jmpctx <- typeOf op >>= fromCode
    currentctx <- currentContext
    case ltr of
      Type TInt -> match currentctx jmpctx
      Nullable mt -> match (insert r (Ref mt) currentctx) jmpctx
      _ -> throwP $ Conditional ltr
  wf (Unpack _ r op) = typeOf r >>= fromUnrestricted >> typeOf op >>= fromExist >>= (shiftContext >>) . localT (push Neutral) . updateReg r

withRef :: Offset -> (LType -> TypeChecker ()) -> (LType -> TypeChecker ()) -> LType -> TypeChecker ()
withRef Zero f g (Ref (MType x y)) = f x >> g (Ref $ MType (used x) y)
withRef One  f g (Ref (MType x y)) = f y >> g (Ref $ MType x $ used y)
withRef _ _ _ lt = throwP $ NonReferenceType lt

used :: LType -> LType
used (Type t) = Type t
used _ = Type Word

store :: Offset -> LType -> LType -> TypeChecker LType
store Zero (Ref (MType _ y)) x = return $ Ref $ MType x y
store One  (Ref (MType x _)) y = return $ Ref $ MType x y
store _ lt _ = throwP $ NonReferenceType lt

wfArith :: Reg -> Reg -> Operand -> TypeChecker ()
wfArith r1 r2 op = typeOf r1 >>= fromUnrestricted >> typeOf r2 >>= fromInt >> typeOf op >>= fromInt >> updateReg r1 (Type TInt)

fromInt :: LType -> TypeChecker ()
fromInt (Type TInt) = return ()
fromInt lt = throwP $ NonIntType lt

fromUnrestricted :: LType -> TypeChecker Type
fromUnrestricted (Type t) = return t
fromUnrestricted lt = throwP $ NonUnrestrictedType lt

fromCode :: LType -> TypeChecker Context
fromCode (Type (Code ctx)) = return ctx
fromCode lt = throwP $ NonCodeType lt

match :: Context -> Context -> TypeChecker ()
match x y = if identical x y then return () else throwP $ ContextMismatch x y

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

throwT :: Error -> TypeChecker a
throwT = TypeChecker . lift . lift . lift. Left

throwP :: Problem -> TypeChecker a
throwP = throwT . Error []

data Error = Error [Reason] Problem

data Problem
  = UnboundTypeVariable TypeContext Int
  | NoSuchRegister Reg
  | NoSuchCodeLabel CLab

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

data Reason