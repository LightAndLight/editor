{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound (Scope)
import qualified Bound
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Text (Text)

data Term a
  = Hole
  | Var a
  | App (Term a) (Term a)
  | Lam Text (Scope () Term a)
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Term
deriveShow1 ''Term
makeBound ''Term
instance Eq a => Eq (Term a) where; (==) = eq1
instance Show a => Show (Term a) where; showsPrec = showsPrec1

_Lam :: Text -> Term (Bound.Var () a) -> Term a
_Lam x = Lam x . Bound.toScope
