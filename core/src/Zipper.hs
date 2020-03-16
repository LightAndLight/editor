{-# language GADTs #-}
module Zipper where

import Path (Path, P, ViewL(..))
import qualified Path

newtype Entry a b where
  Entry :: (b -> a) -> Entry a b

data History a b where
  Nil :: History a a
  Snoc :: History a b -> Entry b c -> History a c

data Zipper a b
  = Zipper
  { _history :: History a b
  , _focus :: b
  }

mapFocus :: (b -> b) -> Zipper a b -> Zipper a b
mapFocus f (Zipper hs a) = Zipper hs (f a)

traverseFocus :: Functor f => (b -> f b) -> Zipper a b -> f (Zipper a b)
traverseFocus f (Zipper hs a) = Zipper hs <$> f a

toZipper :: a -> Zipper a a
toZipper a = Zipper Nil a

fromZipper :: Zipper a b -> a
fromZipper (Zipper Nil focus) = focus
fromZipper (Zipper (Snoc hist entry) focus) =
  fromZipper (Zipper hist (up1 entry focus))

up1 :: Entry a b -> b -> a
up1 (Entry re) x = re x

down1 :: P a b -> a -> Maybe (Entry a b, b)
down1 p a =
  (\(x, re) -> (Entry re, x)) <$> Path.matchP p a

down :: P b c -> Zipper a b -> Maybe (Zipper a c)
down p (Zipper history focus) =
  (\(entry, focus') -> Zipper (Snoc history entry) focus') <$>
  down1 p focus

downTo :: Path b c -> Zipper a b -> Maybe (Zipper a c)
downTo path z =
  case Path.viewl path of
    EmptyL -> Just z
    p :< ps -> down p z >>= downTo ps
