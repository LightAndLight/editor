{-# language GADTs #-}
module Path.Map (Map, empty, insert, lookup) where

import Prelude hiding (lookup)

import Data.Type.Equality ((:~:)(..))

import Path (Path)
import qualified Path as Path

data Entry a f where
  Entry :: Path a b -> f b -> Entry a f

data Map a f = Map [Entry a f]

empty :: Map a f
empty = Map []

insert :: Path a b -> f b -> Map a f -> Map a f
insert p v (Map es) = Map (Entry p v : es)

lookup :: Path a b -> Map a f -> Maybe (f b)
lookup p (Map es) =
  foldr
    (\(Entry p' v) rest -> do
       case Path.eqPath p p' of
         Nothing -> rest
         Just Refl -> Just v
    )
    Nothing
    es
