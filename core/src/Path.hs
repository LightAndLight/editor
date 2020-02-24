{-# language GADTs #-}
{-# language RankNTypes #-}
module Path where

import qualified Bound
import Bound.Var (Var)
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid (First(..))
import Data.Text (Text)

import Syntax (Term)
import qualified Syntax

data P a b where
  AppL :: P (Term a) (Term a)
  AppR :: P (Term a) (Term a)
  Var :: P (Term a) a
  LamArg :: P (Term a) Text
  LamBody :: P (Term a) (Term (Var () a))

data Ps a b where
  Nil :: Ps a a
  Cons :: P a b -> Ps b c -> Ps a c

snoc :: Ps a b -> P b c -> Ps a c
snoc Nil a = Cons a Nil
snoc (Cons a b) c = Cons a (snoc b c)

data TargetInfo b where
  TargetTerm :: TargetInfo (Term v)
  TargetIdent :: TargetInfo Text

data Path a b where
  Path :: Ps a b -> TargetInfo b -> Path a b

modifyA ::
  Ps a b ->
  forall f. Applicative f => (b -> f b) -> a -> f (Maybe a)
modifyA path f a =
  case path of
    Nil -> Just <$> f a
    Cons p ps ->
      case p of
        AppL ->
          case a of
            Syntax.App x y ->
              (fmap.fmap) (\x' -> Syntax.App x' y) $
              modifyA ps f x
            _ -> pure Nothing
        AppR ->
          case a of
            Syntax.App x y ->
              (fmap.fmap) (\y' -> Syntax.App x y') $
              modifyA ps f y
            _ -> pure Nothing
        Var ->
          case a of
            Syntax.Var x ->
              (fmap.fmap) Syntax.Var $
              modifyA ps f x
            _ -> pure Nothing
        LamArg ->
          case a of
            Syntax.Lam n x ->
              (fmap.fmap) (\n' -> Syntax.Lam n' x) $
              modifyA ps f n
            _ -> pure Nothing
        LamBody ->
          case a of
            Syntax.Lam n x ->
              (fmap.fmap) (Syntax.Lam n . Bound.toScope) $
              modifyA ps f (Bound.fromScope x)
            _ -> pure Nothing

modify :: Ps a b -> (b -> b) -> a -> Maybe a
modify path f = runIdentity . modifyA path (Identity . f)

get :: Ps a b -> a -> Maybe b
get path = getFirst . getConst . modifyA path (Const . First . Just)

set :: Ps a b -> b -> a -> Maybe a
set path v = modify path (const v)
