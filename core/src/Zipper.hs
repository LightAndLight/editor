{-# language GADTs #-}
module Zipper where

import Path (Path, P, ViewL(..), KnownTarget, Target, target)
import qualified Path

data Entry a b where
  Entry :: Target a -> (b -> a) -> Entry a b

data History a b where
  Nil :: History a a
  Snoc :: History a b -> Entry b c -> History a c

data Zipper a b
  = Zipper
  { _history :: History a b
  , _target :: Target b
  , _focus :: b
  }

mapFocus :: (b -> b) -> Zipper a b -> Zipper a b
mapFocus f (Zipper hs tgt a) = Zipper hs tgt (f a)

traverseFocus :: Functor f => (b -> f b) -> Zipper a b -> f (Zipper a b)
traverseFocus f (Zipper hs tgt a) = Zipper hs tgt <$> f a

toZipper :: KnownTarget a => a -> Zipper a a
toZipper a = Zipper Nil target a

fromZipper :: Zipper a b -> a
fromZipper (Zipper Nil _ focus) = focus
fromZipper (Zipper (Snoc hist entry) _ focus) =
  let (tgt', focus') = up1 entry focus in
  fromZipper (Zipper hist tgt' focus')

up1 :: Entry a b -> b -> (Target a, a)
up1 (Entry tgt re) x = (tgt, re x)

down1 :: P a b -> Target a -> a -> Maybe (Entry a b, Target b, b)
down1 p tgt a =
  (\(tgt', x, re) -> (Entry tgt re, tgt', x)) <$> Path.matchP p a

down :: P b c -> Zipper a b -> Maybe (Zipper a c)
down p (Zipper history tgt focus) =
  (\(entry, tgt', focus') -> Zipper (Snoc history entry) tgt' focus') <$>
  down1 p tgt focus

downTo :: Path b c -> Zipper a b -> Maybe (Zipper a c)
downTo path z =
  case Path.viewl path of
    EmptyL -> Just z
    p :< ps -> down p z >>= downTo ps
