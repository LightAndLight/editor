{-# language RankNTypes, GADTs, PolyKinds, KindSignatures  #-}
module Data.GADT.Prism where

data GPrism1 (v :: k) (s :: k -> *) a
  = GPrism1
  { _greview1 :: a -> s v
  , _gpreview1 :: forall x r. (x ~ v => a -> r) -> r -> s x -> r
  }

greview1 :: GPrism1 v s a -> a -> s v
greview1 (GPrism1 f _) a = f a

gpreview1 :: GPrism1 v s a -> forall x. s x -> Maybe a
gpreview1 (GPrism1 _ f) a = f Just Nothing a
