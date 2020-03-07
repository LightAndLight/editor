{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound (Scope)
import Bound.Scope (bitraverseScope)
import qualified Bound
import Bound.TH (makeBound)
import Control.Monad (ap)
import Data.Bifunctor (Bifunctor(..))
import Data.Bifoldable (Bifoldable(..))
import Data.Bitraversable
  (Bitraversable(..), bifoldMapDefault, bimapDefault)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Void (Void)
import GHC.Exts (IsString)

newtype TMeta = TMeta Int
  deriving (Eq, Ord, Show)

newtype KMeta = KMeta Int
  deriving (Eq, Ord, Show)

newtype Name = Name { unName :: Text }
  deriving (Eq, Show, IsString)

data Kind
  = KUnsolved (Vector (Name, Kind)) Kind
  | KType
  | KHole KMeta
  deriving (Eq, Show)

substKMeta :: (KMeta, Kind) -> Kind -> Kind
substKMeta (n, k) ki =
  case ki of
    KUnsolved ctx rest ->
      KUnsolved
        ((fmap.fmap) (substKMeta (n, k)) ctx)
        (substKMeta (n, k) rest)
    KType -> KType
    KHole n' -> if n == n' then k else ki

occursK :: KMeta -> Kind -> Bool
occursK n ki =
  case ki of
    KType -> False
    KHole n' -> n == n'
    KUnsolved ctx a -> any (occursK n . snd) ctx || occursK n a

data Type a
  = THole TMeta
  | TVar a
  | TForall Name (Scope () Type a)
  | TArr (Type a) (Type a)
  | TUnsolved (Vector Name) (Scope Int Type Void)
  | TSubst (Type a) (Vector (Type a))
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Type
deriveShow1 ''Type

instance Applicative Type where; pure = return; (<*>) = ap
instance Monad Type where
instance Eq a => Eq (Type a) where; (==) = eq1
instance Show a => Show (Type a) where; showsPrec = showsPrec1

occursK_Type :: KMeta -> Type ty -> Bool
occursK_Type n ty =
  case ty of
    THole{} -> False
    TVar{} -> False
    TForall _ body -> occursK_Type n $ Bound.fromScope body
    TArr a b -> occursK_Type n a || occursK_Type n b
    TUnsolved _ body -> occursK_Type n $ Bound.fromScope body
    TSubst a bs -> occursK_Type n a || any (occursK_Type n) bs

data Term ty a
  = Hole
  | Var a
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
      App a b ->
        App <$> bitraverse f g a <*> bitraverse f g b
      Lam n body ->
        Lam n <$> bitraverseScope f g body
      LamAnn n ty body ->
        LamAnn n <$> traverse f ty <*> bitraverseScope f g body

_Lam :: Text -> Maybe (Type ty) -> Term ty (Bound.Var () a) -> Term ty a
_Lam x mty =
  case mty of
    Nothing -> Lam (Name x) . Bound.toScope
    Just ty -> LamAnn (Name x) ty . Bound.toScope
