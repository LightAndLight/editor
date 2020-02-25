module Typecheck where

import qualified Bound
import Bound.Var (Var(..), unvar)
import Control.Monad (unless)
import Data.Text (Text)

import Syntax

data TypeError
  = NotInScope Text
  | ExpectedArr (Type Text)
  | Can'tInfer (Term Text)
  | NotTArr (Term Text)
  | TypeMismatch (Type Text) (Type Text)

check ::
  Eq ty =>
  (tm -> Text) ->
  (ty -> Text) ->
  (tm -> Maybe (Type ty)) ->
  Term tm ->
  Type ty ->
  Either TypeError ()
check name nameTy ctx tm ty =
  case ty of
    TForall n rest ->
      check name (unvar (\() -> n) nameTy) ((fmap.fmap) F . ctx) tm (Bound.fromScope rest)
    TArr a b ->
      case tm of
        Lam n body ->
          check
            (unvar (\() -> n) name)
            nameTy
            (unvar (\() -> Just a) ctx)
            (Bound.fromScope body)
            b
        _ -> Left . NotTArr $ name <$> tm
    _ -> do
      ty' <- infer name nameTy ctx tm
      unless (ty == ty') . Left $ TypeMismatch (nameTy <$> ty) (nameTy <$> ty')

infer ::
  Eq ty =>
  (tm -> Text) ->
  (ty -> Text) ->
  (tm -> Maybe (Type ty)) ->
  Term tm ->
  Either TypeError (Type ty)
infer name nameTy ctx tm =
  case tm of
    Hole -> pure THole
    Var a ->
      case ctx a of
        Nothing -> Left $ NotInScope (name a)
        Just ty -> pure ty
    App f x -> do
      fTy <- infer name nameTy ctx f
      case fTy of
        TArr a b -> b <$ check name nameTy ctx x a
        _ -> Left . ExpectedArr $ nameTy <$> fTy
    _ -> Left . Can'tInfer $ name <$> tm
