{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound ((>>>=), Scope)
import Bound.Scope (bitraverseScope, instantiateEither)
import qualified Bound
import Bound.TH (makeBound)
import Bound.Var (unvar)
import Control.Monad (ap)
import Data.Bifunctor (Bifunctor(..))
import Data.Bifoldable (Bifoldable(..))
import Data.Bitraversable
  (Bitraversable(..), bifoldMapDefault, bimapDefault)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe as Maybe
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)
import GHC.Exts (IsString)

newtype TMeta = TM Int
  deriving (Eq, Ord, Show)

newtype KMeta = KM Int
  deriving (Eq, Ord, Show)

newtype Name = N { unName :: Text }
  deriving (Eq, Show, IsString)

data Kind
  = KUnsolved (Vector (Name, Kind)) Kind
  | KType
  | KMeta KMeta
  deriving (Eq, Show)

substKMetas :: Map KMeta Kind -> Kind -> Kind
substKMetas s ki =
  case ki of
    KUnsolved ctx rest ->
      KUnsolved
        ((fmap.fmap) (substKMetas s) ctx)
        (substKMetas s rest)
    KType -> KType
    KMeta n -> Maybe.fromMaybe ki $ Map.lookup n s

substKMeta :: (KMeta, Kind) -> Kind -> Kind
substKMeta (n, k) = substKMetas $ Map.singleton n k

occursK :: KMeta -> Kind -> Bool
occursK n ki =
  case ki of
    KType -> False
    KMeta n' -> n == n'
    KUnsolved ctx a -> any (occursK n . snd) ctx || occursK n a

data Type a
  = THole
  | TMeta TMeta
  | TVar a
  | TName Name
  | TForall Name (Scope () Type a)
  | TArr (Type a) (Type a)
  | TUnsolved (Vector (Name, Kind)) (Scope Int Type Void)
  | TSubst (Type a) (Vector (Type a))
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Type
deriveShow1 ''Type

occursT :: TMeta -> Type ty -> Bool
occursT n ty =
  case ty of
    THole -> False
    TMeta n' -> n == n'
    TVar{} -> False
    TName{} -> False
    TForall _ body -> occursT n $ Bound.fromScope body
    TArr a b -> occursT n a || occursT n b
    TUnsolved _ body -> occursT n $ Bound.fromScope body
    TSubst a bs -> occursT n a || any (occursT n) bs

substTMetas :: Map TMeta (Type Void) -> Type ty -> Type ty
substTMetas s ty =
  case ty of
    THole -> THole
    TMeta n -> maybe ty (fmap absurd) (Map.lookup n s)
    TVar{} -> ty
    TName{} -> ty
    TForall name body ->
      TForall name . Bound.toScope $ substTMetas s (Bound.fromScope body)
    TArr a b -> TArr (substTMetas s a) (substTMetas s b)
    TUnsolved ns body ->
      TUnsolved ns . Bound.toScope $ substTMetas s (Bound.fromScope body)
    TSubst a bs -> TSubst (substTMetas s a) (substTMetas s <$> bs)

substTMeta :: (TMeta, Type Void) -> Type ty -> Type ty
substTMeta (n, k) = substTMetas $ Map.singleton n k

instance Applicative Type where; pure = return; (<*>) = ap
instance Monad Type where
  return = TVar
  ty >>= f =
    case ty of
      THole -> THole
      TMeta a -> TMeta a
      TVar a -> f a
      TName a -> TName a
      TForall n body -> TForall n (body >>>= f)
      TArr a b -> TArr (a >>= f) (b >>= f)
      TUnsolved ns body -> TUnsolved ns body
      TSubst a bs -> TSubst (a >>= f) (fmap (>>= f) bs)
instance Eq a => Eq (Type a) where; (==) = eq1
instance Show a => Show (Type a) where; showsPrec = showsPrec1

occursK_Type :: KMeta -> Type ty -> Bool
occursK_Type n ty =
  case ty of
    THole -> False
    TMeta{} -> False
    TVar{} -> False
    TName{} -> False
    TForall _ body -> occursK_Type n $ Bound.fromScope body
    TArr a b -> occursK_Type n a || occursK_Type n b
    TUnsolved _ body -> occursK_Type n $ Bound.fromScope body
    TSubst a bs -> occursK_Type n a || any (occursK_Type n) bs

data Term ty a
  = Hole
  | Var a
  | Name Name
  | App (Term ty a) (Term ty a)
  | Lam Name (Scope () (Term ty) a)
  | LamAnn Name (Type ty) (Scope () (Term ty) a)
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Term
deriveShow1 ''Term
makeBound ''Term
instance (Eq ty, Eq a) => Eq (Term ty a) where; (==) = eq1
instance (Show ty, Show a) => Show (Term ty a) where; showsPrec = showsPrec1
instance Bifunctor Term where; bimap = bimapDefault
instance Bifoldable Term where; bifoldMap = bifoldMapDefault
instance Bitraversable Term where
  bitraverse f g tm =
    case tm of
      Hole -> pure Hole
      Var a -> Var <$> g a
      Name a -> pure $ Name a
      App a b ->
        App <$> bitraverse f g a <*> bitraverse f g b
      Lam n body ->
        Lam n <$> bitraverseScope f g body
      LamAnn n ty body ->
        LamAnn n <$> traverse f ty <*> bitraverseScope f g body

_Lam :: Text -> Maybe (Type ty) -> Term ty (Bound.Var () a) -> Term ty a
_Lam x mty =
  case mty of
    Nothing -> Lam (N x) . Bound.toScope
    Just ty -> LamAnn (N x) ty . Bound.toScope

commaSep :: (a -> Text) -> Vector a -> Text
commaSep f v =
  case Vector.length v of
    0 -> ""
    1 -> f $ Vector.head v
    _ ->
      f (Vector.head v) <>
      foldMap ((", " <>) . f) (Vector.tail v)

printKMeta :: KMeta -> Text
printKMeta (KM n) = Text.pack $ "?" <> show n

printKind :: Kind -> Text
printKind ki =
  case ki of
    KUnsolved ns rest ->
      "Unsolved[" <>
      commaSep (\(n, k) -> unName n <> " : " <> printKind k) ns <>
      "] " <>
      printKind rest
    KType -> "Type"
    KMeta n -> printKMeta n

runSubst :: Type ty -> Type ty
runSubst ty =
  case ty of
    TSubst a bs | Vector.length bs == 0 -> a
    TSubst a bs ->
      case a of
        TUnsolved _ body ->
          instantiateEither (either (bs Vector.!) absurd) body
        _ -> ty
    _ -> ty

printTMeta :: TMeta -> Text
printTMeta (TM n) = Text.pack $ "?" <> show n

printType :: (ty -> Name) -> Type ty -> Text
printType nameTy ty =
  case runSubst ty of
    THole -> "_"
    TMeta n -> printTMeta n
    TVar a -> unName $ nameTy a
    TName n -> unName n
    TForall n body ->
      "forall " <> unName n <> ". " <>
      printType (unvar (\() -> n) nameTy) (Bound.fromScope body)
    TArr a b ->
      printType nameTy a <>
      " -> " <>
      printType nameTy b
    TUnsolved ctx body ->
      "unsolved (" <>
      commaSep (\(n, k) -> unName n <> " : " <> printKind k) ctx <>
      "). " <>
      printType (unvar (fst . (ctx Vector.!)) absurd) (Bound.fromScope body)
    TSubst a bs ->
      "subst(" <>
      printType nameTy a <>
      ", " <>
      commaSep (printType nameTy) bs <>
      ")"
