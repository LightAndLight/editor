{-# language GADTs #-}
module Focus where

import Data.Some (Some(..))
import Path
  ( PathInfo(..)
  , empty, cons
  , ViewL(..), viewl
  , TargetInfo(..)
  )
import qualified Path

prevBranch :: PathInfo a b -> Maybe (Some (PathInfo a))
prevBranch (PathInfo path info) =
  case viewl path of
    EmptyL -> Nothing
    p :< rest ->
      case viewl rest of
        EmptyL ->
          case p of
            Path.Var{} ->
              Nothing
            Path.AppL ->
              Nothing
            Path.AppR ->
              Just $ Some (PathInfo (cons Path.AppL empty) TargetTerm)
            Path.LamArg ->
              Nothing
            Path.LamBody ->
              Just $ Some (PathInfo (cons Path.LamArg empty) TargetIdent)
            Path.TVar{} ->
              Nothing
            Path.TArrL ->
              Nothing
            Path.TArrR ->
              Just $ Some (PathInfo (cons Path.TArrL empty) TargetType)
            Path.TForallArg ->
              Nothing
            Path.TForallBody ->
              Just $ Some (PathInfo (cons Path.TForallArg empty) TargetIdent)
        _ :< _ ->
          (\(Some (PathInfo rest' info')) ->
            Some (PathInfo (cons p rest') info')
          ) <$>
          prevBranch (PathInfo rest info)

nextBranch :: PathInfo a b -> Maybe (Some (PathInfo a))
nextBranch (PathInfo path info) =
  case viewl path of
    EmptyL -> Nothing
    p :< rest ->
      case viewl rest of
        EmptyL ->
          case p of
            Path.Var{} ->
              Nothing
            Path.AppL ->
              Just $ Some (PathInfo (cons Path.AppR empty) TargetTerm)
            Path.AppR ->
              Nothing
            Path.LamArg ->
              Just $ Some (PathInfo (cons Path.LamBody empty) TargetTerm)
            Path.LamBody ->
              Nothing
            Path.TVar{} ->
              Nothing
            Path.TArrL ->
              Just $ Some (PathInfo (cons Path.TArrR empty) TargetType)
            Path.TArrR ->
              Nothing
            Path.TForallArg ->
              Just $ Some (PathInfo (cons Path.TForallBody empty) TargetType)
            Path.TForallBody ->
              Nothing
        _ :< _ ->
          (\(Some (PathInfo rest' info')) ->
            Some (PathInfo (cons p rest') info')
          ) <$>
          nextBranch (PathInfo rest info)
