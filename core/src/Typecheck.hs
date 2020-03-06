{-# language GADTs, StandaloneDeriving #-}
module Typecheck where

import qualified Bound
import Bound.Var (Var(..), unvar)
import Control.Monad (unless)
import Data.Void (Void)

import Path (Path)
import qualified Path
import Syntax

data TypeError
  = NotInScope Name
  | ExpectedArr (Type Name)
  | Can'tInfer (Term Name)
  | NotTArr (Term Name)
  | TypeMismatch (Type Name) (Type Name)
  deriving Show

data Holes tm where
  Cons ::
    Show ty =>
    Path (Term tm) (Term tm') ->
    Type ty ->
    Holes tm ->
    Holes tm
  Nil :: Holes tm
deriving instance Show tm => Show (Holes tm)

updateHole ::
  Show ty =>
  Path (Term tm) (Term v) ->
  Type ty ->
  Holes tm ->
  Holes tm
updateHole _ _ Nil = Nil
updateHole p t (Cons p' t' rest) =
  if Path.eqPath p p'
  then Cons p' t (updateHole p t rest)
  else Cons p' t' (updateHole p t rest)

appendHoles :: Holes tm -> Holes tm -> Holes tm
appendHoles Nil a = a
appendHoles (Cons a b c) d = Cons a b $ appendHoles c d

check ::
  Eq ty =>
  (tm -> Name) ->
  (ty -> Name) ->
  (tm -> Maybe (Type ty)) ->
  Path (Term x) (Term tm) ->
  Term tm ->
  Type ty ->
  Either TypeError (Holes x)
check name nameTy ctx path tm ty =
  case ty of
    TForall n rest ->
      check
        name
        (unvar (\() -> n) nameTy)
        ((fmap.fmap) F . ctx)
        path
        tm
        (Bound.fromScope rest)
    TArr a b ->
      case tm of
        Lam n body ->
          check
            (unvar (\() -> n) name)
            nameTy
            (unvar (\() -> Just a) ctx)
            (Path.snoc path Path.LamBody)
            (Bound.fromScope body)
            b
        _ -> Left . NotTArr $ name <$> tm
    _ -> do
      (ty', holes) <- infer name nameTy ctx path tm
      unless (ty == ty') . Left $
        TypeMismatch (nameTy <$> ty) (nameTy <$> ty')
      pure holes

infer ::
  Eq ty =>
  (tm -> Name) ->
  (ty -> Name) ->
  (tm -> Maybe (Type ty)) ->
  Path (Term x) (Term tm) ->
  Term tm ->
  Either TypeError (Type ty, Holes x)
infer name nameTy ctx path tm =
  case tm of
    Hole -> pure (THole, Cons path (THole :: Type Void) Nil)
    Var a ->
      case ctx a of
        Nothing -> Left $ NotInScope (name a)
        Just ty -> pure (ty, Nil)
    App f x -> do
      let fPath = Path.snoc path Path.AppL
      let xPath = Path.snoc path Path.AppR
      (fTy, fHoles) <- infer name nameTy ctx fPath f
      case fTy of
        TArr a b -> do
          xHoles <- check name nameTy ctx xPath x a
          pure (b, appendHoles fHoles xHoles)
        THole -> do
          xHoles <- check name nameTy ctx xPath x THole
          pure
            ( THole
            , appendHoles
                (updateHole fPath (TArr THole THole :: Type Void) fHoles)
                xHoles
            )
        _ -> Left . ExpectedArr $ nameTy <$> fTy
    _ -> Left . Can'tInfer $ name <$> tm
