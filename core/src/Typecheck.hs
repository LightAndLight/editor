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
import Data.Foldable (traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Type.Equality ((:~:)(..))
import qualified Data.Vector as Vector
import Data.Vector (Vector)

import Path (Path)
import qualified Path
import Syntax

data TEntry ty
  = TEntry
  { _tentryMeta :: TMeta
  , _tentryKind :: Kind
  } deriving (Eq, Show)

occursK_TEntry :: KMeta -> TEntry ty -> Bool
occursK_TEntry n (TEntry _ k) = occursK n k

data KEntry
  = KEntry
  { _kentryMeta :: KMeta
  , _kentrySolution :: Maybe Kind
  } deriving (Eq, Show)

occursK_KEntry :: KMeta -> KEntry -> Bool
occursK_KEntry n (KEntry _ sol) = any (occursK n) sol

substKMeta_KEntry :: (KMeta, Kind) -> KEntry -> KEntry
substKMeta_KEntry s (KEntry n sol) = KEntry n $ substKMeta s <$> sol

data TCState a
  = TCState
  { _tcTypeSupply :: Int
  , _tcKindSupply :: Int
  , _tcKindMetas :: Seq KEntry
  , _tcTypeMetas :: Seq (TEntry a)
  }

data TypeError
  = NotInScope Name
  | TMetaNotInScope TMeta
  | ExpectedArr (Type Name)
  | Can'tInfer (Term Name Name)
  | NotTArr (Term Name Name)
  | TypeMismatch (Type Name) (Type Name)
  | KindMismatch Kind Kind
  deriving Show

freshTMeta :: MonadState (TCState ty) m => m TMeta
freshTMeta = do
  n <- gets _tcTypeSupply
  TMeta n <$ modify (\tc -> tc { _tcTypeSupply = n + 1 })

lookupTMeta ::
  (MonadState (TCState ty) m, MonadError TypeError m) =>
  TMeta ->
  m (TEntry ty)
lookupTMeta t = do
  m_entry <-
    gets $
    foldr
      (\x rest -> if _tentryMeta x == t then Just x else rest)
      Nothing .
    _tcTypeMetas
  maybe (throwError $ TMetaNotInScope t) pure m_entry

freshKMeta :: MonadState (TCState ty) m => m KMeta
freshKMeta = do
  n <- gets _tcKindSupply
  KMeta n <$ modify (\tc -> tc { _tcKindSupply = n + 1 })

solveKMeta ::
  MonadState (TCState ty) m =>
  KMeta ->
  Kind ->
  m ()
solveKMeta n' k' = do
  prefix <- gets _tcKindMetas
  let suffix = mempty
  let sig = mempty
  go prefix suffix sig n' k'
  where
    go prefix suffix sig n k =
      case Seq.viewr prefix of
        Seq.EmptyR -> undefined
        prefix' Seq.:> entry
          | _kentryMeta entry == n ->
            let
              appendSolving =
                flip $ foldl (\acc x -> acc Seq.|> substKMeta_KEntry (n, k) x)
            in
            modify $
            \tc ->
              tc
              { _tcKindMetas =
                appendSolving suffix $ appendSolving sig prefix
              }
          | otherwise ->
            if occursK_KEntry n entry
            then go prefix' (entry Seq.<| suffix) sig n k
            else go prefix' suffix (entry Seq.<| sig) n k

unifyKind ::
  (MonadState (TCState ty) m, MonadError TypeError m) =>
  Kind ->
  Kind ->
  m ()
unifyKind expected actual =
  case expected of
    KUnsolved ctx k ->
      case actual of
        KUnsolved ctx' k' ->
          if Vector.length ctx == Vector.length ctx'
          then do
            traverse_
              (\(a, b) ->
                 if fst a == fst b
                 then throwError $ KindMismatch expected actual
                 else unifyKind (snd a) (snd b)
              )
              (Vector.zip ctx ctx')
            unifyKind k k'
          else throwError $ KindMismatch expected actual
        _ -> throwError $ KindMismatch expected actual
    KType ->
      case actual of
        KType -> pure ()
        _ -> throwError $ KindMismatch expected actual
    KHole n -> solveKMeta n actual

checkKind ::
  (MonadState (TCState ty) m, MonadError TypeError m) =>
  (ty' -> Name) ->
  (ty' -> Maybe Kind) ->
  Type ty' ->
  Kind ->
  m ()
checkKind nameTy ctx ty ki = do
  ki' <- inferKind nameTy ctx ty
  unifyKind ki ki'

inferKind ::
  (MonadState (TCState ty) m, MonadError TypeError m) =>
  (ty' -> Name) ->
  (ty' -> Maybe Kind) ->
  Type ty' ->
  m Kind
inferKind nameTy ctx ty =
  case ty of
    THole n -> do
      TEntry _ k <- lookupTMeta n
      pure k
    TVar a ->
      maybe (throwError . NotInScope $ nameTy a) pure (ctx a)
    TForall n body -> do
      k <- KHole <$> freshKMeta
      inferKind
        (unvar (\() -> n) nameTy)
        (unvar (\() -> Just k) ctx)
        (Bound.fromScope body)
    TArr a b -> do
      checkKind nameTy ctx a KType
      checkKind nameTy ctx b KType
      pure KType
    TUnsolved ns body ->
      inferKind
        (unvar (ns Vector.!) _)
        (unvar _ _)
        (Bound.fromScope body)
    TSubst a bs -> _

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

{-
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
-}
