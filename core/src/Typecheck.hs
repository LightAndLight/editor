{-# language GADTs, StandaloneDeriving #-}
{-# language ScopedTypeVariables #-}
module Typecheck where

import qualified Bound
import Bound.Var (Var(..), unvar)
import Control.Monad (unless)
import Data.Bifunctor (bimap, first)
import Data.Void (Void)

import Path (Path)
import qualified Path
import Syntax

data TypeError
  = NotInScope Name
  | ExpectedArr (Type Name)
  | Can'tInfer (Term Name Name)
  | NotTArr (Term Name Name)
  | TypeMismatch (Type Name) (Type Name)
  deriving Show

data Holes ty tm where
  Cons ::
    Show ty' =>
    Path (Term ty tm) (Term ty' tm') ->
    Type ty' ->
    Holes ty tm ->
    Holes ty tm
  Nil :: Holes ty tm
deriving instance (Show ty, Show tm) => Show (Holes ty tm)

updateHole ::
  Show ty' =>
  Path (Term ty tm) (Term ty' v) ->
  Type ty' ->
  Holes ty tm ->
  Holes ty tm
updateHole _ _ Nil = Nil
updateHole p t (Cons p' t' rest) =
  if Path.eqPath p p'
  then Cons p' t (updateHole p t rest)
  else Cons p' t' (updateHole p t rest)

appendHoles :: Holes ty tm -> Holes ty tm -> Holes ty tm
appendHoles Nil a = a
appendHoles (Cons a b c) d = Cons a b $ appendHoles c d

check ::
  (Eq ty, Show ty) =>
  (tm -> Name) ->
  (ty -> Name) ->
  (tm -> Maybe (Type ty)) ->
  Path (Term y x) (Term ty tm) ->
  Term ty tm ->
  Type ty ->
  Either TypeError (Holes y x)
check name nameTy ctx path tm ty =
  case ty of
    TForall n rest ->
      check
        name
        (unvar (\() -> n) nameTy)
        ((fmap.fmap) F . ctx)
        (_ path)
        (_ $ tm)
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
        _ -> Left . NotTArr $ bimap nameTy name tm
    _ -> do
      (ty', holes) <- infer name nameTy ctx path tm
      case ty' of
        THole -> pure $ updateHole path ty holes
        _ -> do
          unless (ty == ty') . Left $
            TypeMismatch (nameTy <$> ty) (nameTy <$> ty')
          pure holes

infer ::
  forall y x ty tm.
  (Eq ty, Show ty) =>
  (tm -> Name) ->
  (ty -> Name) ->
  (tm -> Maybe (Type ty)) ->
  Path (Term y x) (Term ty tm) ->
  Term ty tm ->
  Either TypeError (Type ty, Holes y x)
infer name nameTy ctx path tm =
  case tm of
    Hole -> pure (THole, Cons path (THole :: Type ty) Nil)
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
                (updateHole fPath (TArr THole THole :: Type ty) fHoles)
                xHoles
            )
        _ -> Left . ExpectedArr $ nameTy <$> fTy
    _ -> Left . Can'tInfer $ bimap nameTy name tm
