{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound (Scope)
import qualified Bound
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Text (Text)
import GHC.Exts (IsString)

newtype Name = Name { unName :: Text }
  deriving (Eq, Show, IsString)

data Type a
  = THole
  | TVar a
  | TForall Name (Scope () Type a)
  | TArr (Type a) (Type a)
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Type
deriveShow1 ''Type
makeBound ''Type
instance Eq a => Eq (Type a) where; (==) = eq1
instance Show a => Show (Type a) where; showsPrec = showsPrec1

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

_Lam :: Text -> Maybe (Type ty) -> Term ty (Bound.Var () a) -> Term ty a
_Lam x mty =
  case mty of
    Nothing -> Lam (Name x) . Bound.toScope
    Just ty -> LamAnn (Name x) ty . Bound.toScope
