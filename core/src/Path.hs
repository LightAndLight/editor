{-# language GADTs #-}
{-# language RankNTypes #-}
module Path where

import qualified Bound
import Bound.Var (Var)
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid (First(..))
import Data.Text (Text)

import Syntax (Term, Type)
import qualified Syntax

data P a b where
  AppL :: P (Term a) (Term a)
  AppR :: P (Term a) (Term a)
  Var :: P (Term a) a
  LamArg :: P (Term a) Text
  LamBody :: P (Term a) (Term (Var () a))

  TVar :: P (Type a) a
  TForallArg :: P (Type a) Text
  TForallBody :: P (Type a) (Type (Var () a))
  TArrL :: P (Type a) (Type a)
  TArrR :: P (Type a) (Type a)

matchP :: P a b -> a -> Maybe (b, b -> a)
matchP p a =
  case p of
    AppL ->
      case a of
        Syntax.App x y ->
          Just (x, \x' -> Syntax.App x' y)
        _ -> Nothing
    AppR ->
      case a of
        Syntax.App x y ->
          Just (y, \y' -> Syntax.App x y')
        _ -> Nothing
    Var ->
      case a of
        Syntax.Var x ->
          Just (x, Syntax.Var)
        _ -> Nothing
    LamArg ->
      case a of
        Syntax.Lam n x ->
          Just (n, \n' -> Syntax.Lam n' x)
        _ -> Nothing
    LamBody ->
      case a of
        Syntax.Lam n x ->
          Just (Bound.fromScope x, Syntax.Lam n . Bound.toScope)
        _ -> Nothing
    TVar ->
      case a of
        Syntax.TVar x ->
          Just (x, Syntax.TVar)
        _ -> Nothing
    TArrL ->
      case a of
        Syntax.TArr x y ->
          Just (x, \x' -> Syntax.TArr x' y)
        _ -> Nothing
    TArrR ->
      case a of
        Syntax.TArr x y ->
          Just (y, \y' -> Syntax.TArr x y')
        _ -> Nothing
    TForallArg ->
      case a of
        Syntax.TForall n x ->
          Just (n, \n' -> Syntax.TForall n' x)
        _ -> Nothing
    TForallBody ->
      case a of
        Syntax.TForall n x ->
          Just (Bound.fromScope x, Syntax.TForall n . Bound.toScope)
        _ -> Nothing


data Ps a b where
  Nil :: Ps a a
  Cons :: P a b -> Ps b c -> Ps a c

snoc :: Ps a b -> P b c -> Ps a c
snoc Nil a = Cons a Nil
snoc (Cons a b) c = Cons a (snoc b c)

appendPs :: Ps a b -> Ps b c -> Ps a c
appendPs Nil a = a
appendPs (Cons a b) c = Cons a (appendPs b c)

data TargetInfo b where
  TargetTerm :: TargetInfo (Term v)
  TargetType :: TargetInfo (Type v)
  TargetIdent :: TargetInfo Text

data Path a b where
  Path :: Ps a b -> TargetInfo b -> Path a b

append :: Path a b -> Path b c -> Path a c
append (Path ps _) (Path qs info) = Path (appendPs ps qs) info

modifyA ::
  Ps a b ->
  forall f. Applicative f => (b -> f b) -> a -> f (Maybe a)
modifyA path f a =
  case path of
    Nil -> Just <$> f a
    Cons p ps ->
      case matchP p a of
        Nothing -> pure Nothing
        Just (x, re) ->
          (fmap.fmap) re $
          modifyA ps f x

modify :: Ps a b -> (b -> b) -> a -> Maybe a
modify path f = runIdentity . modifyA path (Identity . f)

get :: Ps a b -> a -> Maybe b
get path = getFirst . getConst . modifyA path (Const . First . Just)

set :: Ps a b -> b -> a -> Maybe a
set path v = modify path (const v)
