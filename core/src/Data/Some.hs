{-# language GADTs, KindSignatures, PolyKinds #-}
module Data.Some where

data Some :: (k -> *) -> * where
  Some :: f a -> Some f
