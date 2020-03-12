{-# language FlexibleInstances, StandaloneDeriving #-}
{-# language GADTs #-}
{-# language EmptyCase, LambdaCase #-}
{-# language RankNTypes #-}
{-# language TypeOperators #-}
module Path where

import qualified Bound
import Bound.Var (Var)
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid (First(..))
import Data.Type.Equality ((:~:)(..))
import qualified Data.Vector as Vector
import Data.Void (Void)

import Syntax (Name, Term, Type)
import qualified Syntax

data P a b where
  AppL :: P (Term ty a) (Term ty a)
  AppR :: P (Term ty a) (Term ty a)
  LamArg :: P (Term ty a) Name
  LamBody :: P (Term ty a) (Term ty (Var () a))
  LamAnnArg :: P (Term ty a) Name
  LamAnnType :: P (Term ty a) (Type ty)
  LamAnnBody :: P (Term ty a) (Term ty (Var () a))

  AnnL :: P (Term ty tm) (Term ty tm)
  AnnR :: P (Term ty tm) (Type ty)

  TForallArg :: P (Type a) Name
  TForallBody :: P (Type a) (Type (Var () a))
  TArrL :: P (Type a) (Type a)
  TArrR :: P (Type a) (Type a)
  TUnsolvedBody :: P (Type a) (Type (Var Int Void))
  TSubstL :: P (Type a) (Type a)
  TSubstR :: Int -> P (Type a) (Type a)
deriving instance Show (P a b)

nameLeaf :: P Name a -> Void
nameLeaf = \case

eqP :: P a b -> P a d -> Maybe (b :~: d)
eqP AppL a =
  case a of
    AppL -> Just Refl
    _ -> Nothing
eqP AppR a =
  case a of
    AppR -> Just Refl
    _ -> Nothing
eqP AnnL a =
  case a of
    AnnL -> Just Refl
    _ -> Nothing
eqP AnnR a =
  case a of
    AnnR -> Just Refl
    _ -> Nothing
eqP LamArg a =
  case a of
    LamArg -> Just Refl
    _ -> Nothing
eqP LamBody a =
  case a of
    LamBody -> Just Refl
    _ -> Nothing
eqP LamAnnArg a =
  case a of
    LamAnnArg -> Just Refl
    _ -> Nothing
eqP LamAnnType a =
  case a of
    LamAnnType -> Just Refl
    _ -> Nothing
eqP LamAnnBody a =
  case a of
    LamAnnBody -> Just Refl
    _ -> Nothing
eqP TForallArg a =
  case a of
    TForallArg -> Just Refl
    _ -> Nothing
eqP TForallBody a =
  case a of
    TForallBody -> Just Refl
    _ -> Nothing
eqP TArrL a =
  case a of
    TArrL -> Just Refl
    _ -> Nothing
eqP TArrR a =
  case a of
    TArrR -> Just Refl
    _ -> Nothing
eqP TUnsolvedBody a =
  case a of
    TUnsolvedBody -> Just Refl
    _ -> Nothing
eqP TSubstL a =
  case a of
    TSubstL -> Just Refl
    _ -> Nothing
eqP (TSubstR n) a =
  case a of
    TSubstR n' | n == n' -> Just Refl
    _ -> Nothing

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
    AnnL ->
      case a of
        Syntax.Ann x y ->
          Just (x, \x' -> Syntax.Ann x' y)
        _ -> Nothing
    AnnR ->
      case a of
        Syntax.Ann x y ->
          Just (y, \y' -> Syntax.Ann x y')
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
    LamAnnArg ->
      case a of
        Syntax.LamAnn n ty x ->
          Just (n, \n' -> Syntax.LamAnn n' ty x)
        _ -> Nothing
    LamAnnType ->
      case a of
        Syntax.LamAnn n ty x ->
          Just (ty, \ty' -> Syntax.LamAnn n ty' x)
        _ -> Nothing
    LamAnnBody ->
      case a of
        Syntax.LamAnn n ty x ->
          Just (Bound.fromScope x, Syntax.LamAnn n ty . Bound.toScope)
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
    TUnsolvedBody ->
      case a of
        Syntax.TUnsolved ns x ->
          Just (Bound.fromScope x, Syntax.TUnsolved ns . Bound.toScope)
        _ -> Nothing
    TSubstL ->
      case a of
        Syntax.TSubst x y ->
          Just (x, \x' -> Syntax.TSubst x' y)
        _ -> Nothing
    TSubstR n ->
      case a of
        Syntax.TSubst x y ->
          Just (y Vector.! n, \e' -> Syntax.TSubst x (y Vector.// [(n, e')]))
        _ -> Nothing

data Digit f a b where
  One :: f a b -> Digit f a b
  Two :: f a b -> f b c -> Digit f a c
  Three :: f a b -> f b c -> f c d -> Digit f a d
  Four :: f a b -> f b c -> f c d -> f d e -> Digit f a e

data Node f a b where
  Node2 :: f a b -> f b c -> Node f a c
  Node3 :: f a b -> f b c -> f c d -> Node f a d

data Seq f a b where
  Empty :: Seq f a a
  Single :: f a b -> Seq f a b
  Deep :: Digit f a b -> Seq (Node f) b c -> Digit f c d -> Seq f a d
instance Show (Seq P a b) where
  show ls = "[" <> go ls <> "]"
    where
      go :: Seq P a b -> String
      go ls' =
        case viewl ls' of
          EmptyL -> ""
          a :< as ->
            case viewl as of
              EmptyL -> show a
              _ -> show a <> ", " <> go as

empty :: Seq f a a
empty = Empty

singleton :: f a b -> Seq f a b
singleton = Single

cons :: f a b -> Seq f b c -> Seq f a c
cons a xs =
  case xs of
    Empty -> Single a
    Single x -> Deep (One a) Empty (One x)
    Deep l m r ->
      case l of
        One x1 -> Deep (Two a x1) m r
        Two x1 x2 -> Deep (Three a x1 x2) m r
        Three x1 x2 x3 -> Deep (Four a x1 x2 x3) m r
        Four x1 x2 x3 x4 -> Deep (Two a x1) (Node3 x2 x3 x4 `cons` m) r

snoc :: Seq f a b -> f b c -> Seq f a c
snoc xs a =
  case xs of
    Empty -> Single a
    Single x -> Deep (One x) Empty (One a)
    Deep l m r ->
      case r of
        One x1 -> Deep l m (Two x1 a)
        Two x1 x2 -> Deep l m (Three x1 x2 a)
        Three x1 x2 x3 -> Deep l m (Four x1 x2 x3 a)
        Four x1 x2 x3 x4 -> Deep l (m `snoc` Node3 x1 x2 x3) (Two x4 a)

data Nodes f a b where
  NodeNil :: Nodes f a a
  NodeCons :: f a b -> Nodes f b c -> Nodes f a c

appendNodes :: Nodes f a b -> Nodes f b c -> Nodes f a c
appendNodes a b =
  case a of
    NodeNil -> b
    NodeCons x xs -> NodeCons x (appendNodes xs b)

digitNodes :: Digit f a b -> Nodes f a b
digitNodes (One a) =
  NodeCons a $
  NodeNil
digitNodes (Two a b) =
  NodeCons a $
  NodeCons b $
  NodeNil
digitNodes (Three a b c) =
  NodeCons a $
  NodeCons b $
  NodeCons c $
  NodeNil
digitNodes (Four a b c d) =
  NodeCons a $
  NodeCons b $
  NodeCons c $
  NodeCons d $
  NodeNil

nodes :: Nodes f a b -> Nodes (Node f) a b
nodes ns =
  case ns of
    NodeNil -> undefined
    NodeCons _ NodeNil -> undefined

    NodeCons a (NodeCons b NodeNil) ->
      NodeCons (Node2 a b) NodeNil
    NodeCons a (NodeCons b (NodeCons c NodeNil)) ->
      NodeCons (Node3 a b c) NodeNil
    NodeCons a (NodeCons b (NodeCons c (NodeCons d NodeNil))) ->
      NodeCons (Node2 a b) $
      NodeCons (Node2 c d) $
      NodeNil
    NodeCons a (NodeCons b (NodeCons c cs)) ->
      NodeCons (Node3 a b c) $ nodes cs

consNodes :: Nodes f a b -> Seq f b c -> Seq f a c
consNodes ns s =
  case ns of
    NodeNil -> s
    NodeCons x xs -> cons x $ consNodes xs s

snocNodes :: Seq f a b -> Nodes f b c -> Seq f a c
snocNodes s ns =
  case ns of
    NodeNil -> s
    NodeCons x xs -> snocNodes (snoc s x) xs

append :: Seq f a b -> Seq f b c -> Seq f a c
append xx yy = inner xx NodeNil yy
  where
    inner ::
      Seq f a b ->
      Nodes f b c ->
      Seq f c d ->
      Seq f a d
    inner Empty b c = consNodes b c
    inner a b Empty = snocNodes a b
    inner (Single a) b c = cons a (consNodes b c)
    inner a b (Single c) = snoc (snocNodes a b) c
    inner (Deep l1 m1 r1) b (Deep l2 m2 r2) =
      Deep
        l1
        (inner
           m1
           (nodes $
            appendNodes (digitNodes r1) $
            appendNodes b (digitNodes l2)
           )
           m2
        )
        r2

data ViewL f a b where
  EmptyL :: ViewL f a a
  (:<) :: f a b -> Seq f b c -> ViewL f a c

data ViewR f a b where
  EmptyR :: ViewR f a a
  (:>) :: Seq f a b -> f b c -> ViewR f a c

nodeToDigit :: Node f a b -> Digit f a b
nodeToDigit n =
  case n of
    Node2 a b -> Two a b
    Node3 a b c -> Three a b c

digitToSeq :: Digit f a b -> Seq f a b
digitToSeq dig =
  case dig of
    One a -> Single a
    Two a b -> cons a $ Single b
    Three a b c -> cons a $ cons b $ Single c
    Four a b c d -> cons a $ cons b $ cons c $ Single d

viewl :: Seq f a b -> ViewL f a b
viewl s =
  case s of
    Empty -> EmptyL
    Single x -> x :< Empty
    Deep l m r ->
      case l of
        One a ->
          case viewl m of
            EmptyL -> a :< digitToSeq r
            z :< zs -> a :< Deep (nodeToDigit z) zs r
        Two a b -> a :< Deep (One b) m r
        Three a b c -> a :< Deep (Two b c) m r
        Four a b c d -> a :< Deep (Three b c d) m r

viewr :: Seq f a b -> ViewR f a b
viewr s =
  case s of
    Empty -> EmptyR
    Single x -> Empty :> x
    Deep l m r ->
      case r of
        One a ->
          case viewr m of
            EmptyR -> digitToSeq l :> a
            zs :> z -> Deep l zs (nodeToDigit z) :> a
        Two a b -> Deep l m (One a) :> b
        Three a b c -> Deep l m (Two a b) :> c
        Four a b c d -> Deep l m (Three a b c) :> d

data TargetInfo b where
  TargetTerm :: TargetInfo (Term ty v)
  TargetType :: TargetInfo (Type v)
  TargetName :: TargetInfo Name

class HasTargetInfo a where
  targetInfo :: TargetInfo a

instance HasTargetInfo (Term ty tm) where; targetInfo = TargetTerm
instance HasTargetInfo (Type ty) where; targetInfo = TargetType
instance HasTargetInfo Name where; targetInfo = TargetName

type Path = Seq P

eqPath :: Path a b -> Path a d -> Maybe (b :~: d)
eqPath pa pb =
  case viewl pa of
    EmptyL ->
      case viewl pb of
        EmptyL -> Just Refl
        _ -> Nothing
    a :< as ->
      case viewl pb of
        EmptyL -> Nothing
        b :< bs -> do
          Refl <- eqP a b
          Refl <- eqPath as bs
          pure Refl

{-
targetInfo :: Path a b -> Either (a :~: b) (TargetInfo b)
targetInfo ps =
  case viewr ps of
    EmptyR -> Left Refl
    _ :> p ->
      Right $
      case p of
        AppL -> TargetTerm
        AppR -> TargetTerm
        Var -> undefined
        LamArg -> TargetName
        LamBody -> TargetTerm
        LamAnnArg -> TargetName
        LamAnnType -> TargetType
        LamAnnBody -> TargetTerm
        TVar -> undefined
        TForallArg -> TargetName
        TForallBody -> TargetType
        TArrL -> TargetType
        TArrR -> TargetType
-}

modifyA ::
  Path a b ->
  forall f. Applicative f => (b -> f b) -> a -> f (Maybe a)
modifyA path f a =
  case viewl path of
    EmptyL -> Just <$> f a
    p :< ps ->
      case matchP p a of
        Nothing -> pure Nothing
        Just (x, re) ->
          (fmap.fmap) re $
          modifyA ps f x

modify :: Path a b -> (b -> b) -> a -> Maybe a
modify path f = runIdentity . modifyA path (Identity . f)

get :: Path a b -> a -> Maybe b
get path = getFirst . getConst . modifyA path (Const . First . Just)

set :: Path a b -> b -> a -> Maybe a
set path v = modify path (const v)
