{-# language FlexibleContexts #-}
{-# language GADTs, StandaloneDeriving #-}
{-# language ScopedTypeVariables #-}
module Typecheck where

import Bound (Scope)
import qualified Bound
import qualified Bound.Scope as Scope
import Bound.Var (unvar)
import Control.Monad (unless)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, gets, modify)
import Data.Bifunctor (bimap)
import Data.Foldable (toList, traverse_)
import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Type.Equality ((:~:)(..))
import qualified Data.Vector as Vector
import Data.Vector (Vector)
import Data.Void (Void, absurd)

import Path (Path)
import qualified Path
import Syntax

data Entry
  = TEntry
  { _tentryMeta :: TMeta
  , _tentryKind :: Kind
  }
  | KEntry
  { _kentryMeta :: KMeta
  } deriving (Eq, Show)

occursK_Entry :: KMeta -> Entry -> Bool
occursK_Entry n (TEntry _ k) = occursK n k
occursK_Entry n KEntry{} = False

substKMeta_Entry :: (KMeta, Kind) -> Entry -> Entry
substKMeta_Entry s (TEntry n k) = TEntry n $ substKMeta s k
substKMeta_Entry s (KEntry n) = KEntry n

data TCState ty
  = TCState
  { _tcTypeSupply :: Int
  , _tcKindSupply :: Int
  , _tcEntries :: Seq Entry
  , _tcSubst :: Map TMeta (Type ty)
  }

data TypeError
  = NotInScope Name
  | TMetaNotInScope TMeta
  | ExpectedArr (Type Name)
  | Can'tInfer (Term Name Name)
  | NotTArr (Term Name Name)
  | TypeMismatch (Type Name) (Type Name)
  | KindMismatch Kind Kind
  | ExpectedKUnsolved Kind
  | ArityMismatch Int Int
  | Escape Name
  deriving Show

freshTMeta :: MonadState (TCState ty) m => m TMeta
freshTMeta = do
  n <- gets _tcTypeSupply
  TMeta n <$ modify (\tc -> tc { _tcTypeSupply = n + 1 })

lookupTMeta ::
  (MonadState (TCState ty) m, MonadError TypeError m) =>
  TMeta ->
  m Kind
lookupTMeta t = do
  m_entry <-
    gets $
    foldr
      (\x rest ->
         case x of
           TEntry t' k -> if t == t' then Just k else rest
           _ -> rest
      )
      Nothing .
    _tcEntries
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
  prefix <- gets _tcEntries
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
                flip $ foldl (\acc x -> acc Seq.|> substKMeta_Entry (n, k) x)
            in
            modify $
            \tc ->
              tc
              { _tcEntries =
                appendSolving suffix $ appendSolving sig prefix
              }
          | otherwise ->
            if occursK_Entry n entry
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
        KHole n -> solveKMeta n expected
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
        KHole n -> solveKMeta n expected
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
    THole n -> lookupTMeta n
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
        (unvar (fst . (ns Vector.!)) absurd)
        (unvar (Just . snd . (ns Vector.!)) absurd)
        (Bound.fromScope body)
    TSubst a bs -> do
      aKind <- inferKind nameTy ctx a
      case aKind of
        KUnsolved ns bodyKind ->
          let
            lbs = length bs
            lns = length ns
          in
            if lns == lbs
            then do
              traverse_ (\(x, y) -> checkKind nameTy ctx x (snd y)) (Vector.zip bs ns)
              pure bodyKind
            else throwError $ ArityMismatch lns lbs
        _ -> throwError $ ExpectedKUnsolved aKind

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

solveTMeta ::
  MonadState (TCState ty) m =>
  TMeta ->
  Type Void ->
  m ()
solveTMeta n' t' = do
  prefix <- gets _tcEntries
  let suffix = mempty
  let sig = mempty
  go prefix suffix sig n' t'
  where
    go prefix suffix sig n t =
      case Seq.viewr prefix of
        Seq.EmptyR -> undefined
        prefix' Seq.:> entry
          | _tentryMeta entry == n ->
            modify $
            \tc ->
              tc
              { _tcEntries = prefix <> sig <> suffix
              , _tcSubst = Map.insert n (absurd <$> t) $ substTMeta (n, t) <$> _tcSubst tc
              }
          | otherwise ->
            go prefix' suffix (entry Seq.<| sig) n t

runSubst :: Type ty -> Type ty
runSubst ty =
  case ty of
    TSubst a bs ->
      case a of
        TUnsolved _ body -> Scope.instantiateEither (either (bs Vector.!) absurd) body
        _ -> ty
    _ -> ty

unifyType ::
  ( MonadState (TCState ty) m, MonadError TypeError m
  , Eq ty'
  ) =>
  (ty' -> Name) ->
  (ty' -> Maybe Kind) ->
  Type ty' ->
  Type ty' ->
  m ()
unifyType nameTy ctx expected actual =
  case runSubst expected of
    THole n ->
      case runSubst actual of
        THole n' -> solveTMeta n (THole n')
        _ -> throwError $ TypeMismatch (nameTy <$> expected) (nameTy <$> actual)
    TVar a ->
      case runSubst actual of
        TVar a' | a == a' -> pure ()
        THole n -> error "todo"
        _ -> throwError $ TypeMismatch (nameTy <$> expected) (nameTy <$> actual)
    TForall n body ->
      case runSubst actual of
        TForall n' body' -> do
          k <- KHole <$> freshKMeta
          unifyType
            (unvar (\() -> n') nameTy)
            (unvar (\() -> Just k) ctx)
            (Bound.fromScope body)
            (Bound.fromScope body')
        THole n -> error "todo"
        _ -> throwError $ TypeMismatch (nameTy <$> expected) (nameTy <$> actual)
    TArr a b ->
      case runSubst actual of
        TArr a' b' -> do
          unifyType nameTy ctx a a'
          unifyType nameTy ctx b b'
        THole n -> error "todo"
        _ -> throwError $ TypeMismatch (nameTy <$> expected) (nameTy <$> actual)
    TUnsolved ns body ->
      case runSubst actual of
        TUnsolved ns' body' | length ns == length ns' -> do
          traverse_
            (\(a, b) ->
               if fst a == fst b
               then unifyKind (snd a) (snd b)
               else throwError $ TypeMismatch (nameTy <$> expected) (nameTy <$> actual)
            )
            (Vector.zip ns ns')
          unifyType
            (unvar (fst . (ns' Vector.!)) absurd)
            (unvar (Just . snd . (ns' Vector.!)) absurd)
            (Bound.fromScope body)
            (Bound.fromScope body')
        THole n -> error "todo"
        _ -> throwError $ TypeMismatch (nameTy <$> expected) (nameTy <$> actual)
    TSubst (THole n) bs -> do
      k <- lookupTMeta n
      case k of
        KUnsolved ns bodyK -> do
          let
            actual' =
              TUnsolved ns . Bound.toScope <$>
              traverse
                (\v ->
                   case Vector.findIndex ((nameTy v ==) . fst) ns of
                     Nothing -> Left v
                     Just ix -> Right $ Bound.B ix
                )
                actual
          case actual' of
            Left v -> throwError $ Escape (nameTy v)
            Right sol -> solveTMeta n sol
        KHole kn -> error "todo"
        _ -> undefined
    TSubst{} -> undefined

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
