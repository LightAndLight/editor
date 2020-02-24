{-# language GADTs #-}
module Focus where

import Data.Some (Some(..))
import Path (Path(..), Ps(..), TargetInfo(..))
import qualified Path

prevBranch :: Path a b -> Maybe (Some (Path a))
prevBranch (Path path info) =
  case path of
    Nil -> Nothing
    Cons p Nil ->
      case p of
        Path.Var{} ->
          Nothing
        Path.AppL ->
          Nothing
        Path.AppR ->
          Just $ Some (Path (Cons Path.AppL Nil) TargetTerm)
        Path.LamArg ->
          Nothing
        Path.LamBody ->
          Just $ Some (Path (Cons Path.LamArg Nil) TargetIdent)
    Cons p rest ->
      (\(Some (Path rest' info')) ->
         Some (Path (Cons p rest') info')
      ) <$>
      prevBranch (Path rest info)

nextBranch :: Path a b -> Maybe (Some (Path a))
nextBranch (Path path info) =
  case path of
    Nil -> Nothing
    Cons p Nil ->
      case p of
        Path.Var{} ->
          Nothing
        Path.AppL ->
          Just $ Some (Path (Cons Path.AppR Nil) TargetTerm)
        Path.AppR ->
          Nothing
        Path.LamArg ->
          Just $ Some (Path (Cons Path.LamBody Nil) TargetTerm)
        Path.LamBody ->
          Nothing
    Cons p rest ->
      (\(Some (Path rest' info')) ->
         Some (Path (Cons p rest') info')
      ) <$>
      nextBranch (Path rest info)
