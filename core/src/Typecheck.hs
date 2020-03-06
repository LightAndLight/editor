{-# language FlexibleContexts #-}
{-# language GADTs, StandaloneDeriving #-}
{-# language ScopedTypeVariables #-}
module Typecheck where

import qualified Bound
import Bound.Var (unvar)
import Control.Monad (unless)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, gets, modify)
import Data.Bifunctor (bimap)
import Data.Type.Equality ((:~:)(..))

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
  case Path.eqPath p p' of
    Nothing -> Cons p' t' (updateHole p t rest)
    Just Refl -> Cons p' t (updateHole p t rest)

appendHoles :: Holes ty tm -> Holes ty tm -> Holes ty tm
appendHoles Nil a = a
appendHoles (Cons a b c) d = Cons a b $ appendHoles c d

data TCState
  = TCState
  { _tcSupply :: Int
  }

freshMeta :: MonadState TCState m => m Int
freshMeta = do
  n <- gets _tcSupply
  n <$ modify (\tc -> tc { _tcSupply = n + 1 })

check ::
  (Eq ty, Show ty, MonadState TCState m, MonadError TypeError m) =>
  (tm -> Name) ->
  (ty -> Name) ->
  (tm -> Maybe (Type ty)) ->
  Path (Term y x) (Term ty tm) ->
  Term ty tm ->
  Type ty ->
  m (Holes y x)
check name nameTy ctx path tm ty =
  case ty of
{-
    TForall n rest ->
      check
        name
        (unvar (\() -> n) nameTy)
        ((fmap.fmap) F . ctx)
        (_ path)
        (_ tm)
        (Bound.fromScope rest)
-}
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
        _ -> throwError . NotTArr $ bimap nameTy name tm
    _ -> do
      (ty', holes) <- infer name nameTy ctx path tm
      case ty' of
        THole n -> pure $ updateHole path ty holes
        _ -> do
          unless (ty == ty') . throwError $
            TypeMismatch (nameTy <$> ty) (nameTy <$> ty')
          pure holes

infer ::
  forall y x ty tm m.
  (Eq ty, Show ty, MonadState TCState m, MonadError TypeError m) =>
  (tm -> Name) ->
  (ty -> Name) ->
  (tm -> Maybe (Type ty)) ->
  Path (Term y x) (Term ty tm) ->
  Term ty tm ->
  m (Type ty, Holes y x)
infer name nameTy ctx path tm =
  case tm of
    Hole -> do
      t <- THole <$> freshMeta
      pure (t, Cons path (t :: Type ty) Nil)
    Var a ->
      case ctx a of
        Nothing -> throwError $ NotInScope (name a)
        Just ty -> pure (ty, Nil)
    LamAnn n ty body -> do
      let bodyPath = Path.snoc path Path.LamAnnBody
      (bodyTy, bodyHoles) <-
        infer
          (unvar (\() -> n) name)
          nameTy
          (unvar (\() -> Just ty) ctx)
          bodyPath
          (Bound.fromScope body)
      pure (Syntax.TArr ty bodyTy, bodyHoles)
    App f x -> do
      let fPath = Path.snoc path Path.AppL
      let xPath = Path.snoc path Path.AppR
      (fTy, fHoles) <- infer name nameTy ctx fPath f
      case fTy of
        TArr a b -> do
          xHoles <- check name nameTy ctx xPath x a
          pure (b, appendHoles fHoles xHoles)
        THole n -> do
          t1 <- THole <$> freshMeta
          t2 <- THole <$> freshMeta
          xHoles <- check name nameTy ctx xPath x t1
          pure
            ( t2
            , appendHoles
                (updateHole fPath (TArr t1 t2 :: Type ty) fHoles)
                xHoles
            )
        _ -> throwError . ExpectedArr $ nameTy <$> fTy
    _ -> throwError . Can'tInfer $ bimap nameTy name tm
