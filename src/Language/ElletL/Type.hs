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

-- In the following, "wh" stands for "well-formed".

newtype TypeChecker a = TypeChecker { runTypeChecker :: ReaderT TypeContext (StateT Context (ReaderT Sig (Either Error))) a }
  deriving (Functor, Applicative, Monad)

localT :: (TypeContext -> TypeContext) -> TypeChecker a -> TypeChecker a
localT f (TypeChecker m) = TypeChecker $ local f m

whType :: Type -> TypeChecker ()
whType (Forall _ t) = localT (push Neutral) $ whType t
whType TInt = return ()
whType Word = return ()
whType (Code ctx) = localT invert $ mapM_ whLType $ Map.elems $ getContext ctx

whLType :: LType -> TypeChecker ()
whLType (TVar i) = TypeChecker ask >>= getSign i >>= f
  where
    f Minus = throwP $ UnexpectedMinus i
    f _ = return ()
whLType (Type t) = whType t
whLType (Nullable mt) = whMType mt
whLType (Ref mt) = whMType mt
whLType (Exist _ lt) = localT (push Neutral) $ whLType lt
whLType (Rec s (TVar 0)) = throwP $ NonContractiveRecType s
whLType (Rec _ lt) = localT (push Plus) $ whLType lt

whMType :: MType -> TypeChecker ()
whMType (MType lt1 lt2) = mapM_ whLType [lt1, lt2]

newtype Sig = Sig { getSig :: Map.Map CLab Type }

whSig :: TypeChecker ()
whSig = (TypeChecker . lift . lift . asks) (Map.elems . getSig) >>= mapM_ (\t -> expectCode t >> whType t)

expectCode :: Type -> TypeChecker ()
expectCode (Code _) = return ()
expectCode (Forall _ t) = expectCode t
expectCode t = throwP $ NotCodeType t

class Typed a where
  typeOf :: a -> TypeChecker LType

instance Typed Reg where
  typeOf r = TypeChecker (lift get) >>= maybe (throwP $ NoSuchRegister r) return . Map.lookup r . getContext

remove :: Reg -> Context -> Context
remove r (Context m) = Context $ Map.delete r m

use :: Reg -> LType -> TypeChecker ()
use _ (Type _) = return ()
use r _ = TypeChecker $ lift $ modify $ remove r

instance Typed Operand where
  typeOf (Register r)     = typeOf r >>= (<$) <*> use r -- Note that registers can be typed also as Word.
  typeOf (Int _)          = return $ Type TInt
  typeOf (Func cl)        = fmap Type $ TypeChecker (lift $ lift $ asks $ Map.lookup cl . getSig) >>= maybe (throwP $ NoSuchCodeLabel cl) return
  typeOf (TApp op lt)     = whLType lt >> typeOf op >>= instantiate lt
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
  | UnexpectedMinus Int
  | NonContractiveRecType String -- @rec X. X@ is ill-formed.
  | NotCodeType Type
  | NoSuchRegister Reg
  | NoSuchCodeLabel CLab
  | NonPolymorphicType LType
  | NotIdentical LType LType
  | NonExistentialType LType
  | NonRecursiveType LType

data Reason
