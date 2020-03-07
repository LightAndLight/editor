{-# language FlexibleContexts #-}
{-# language GADTs, StandaloneDeriving #-}
{-# language ScopedTypeVariables #-}
module Typecheck where

import qualified Bound
import qualified Bound.Scope as Scope
import Bound.Var (unvar)
import Control.Monad (when)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, gets, modify)
import Data.Foldable (traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Type.Equality ((:~:)(..))
import qualified Data.Vector as Vector
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
occursK_Entry _ KEntry{} = False

substKMeta_Entry :: (KMeta, Kind) -> Entry -> Entry
substKMeta_Entry s (TEntry n k) = TEntry n $ substKMeta s k
substKMeta_Entry _ (KEntry n) = KEntry n

data TCState ty
  = TCState
  { _tcTypeSupply :: Int
  , _tcKindSupply :: Int
  , _tcEntries :: Seq Entry
  , _tcSubst :: Map TMeta (Type Void)
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

freshTMeta ::
  MonadState (TCState ty) m =>
  Seq (Name, Type ty', Kind) ->
  Kind ->
  m (Type ty')
freshTMeta boundTyVars k = do
  n <- gets _tcTypeSupply
  let
    m = TMeta n
    bs =
      Vector.generate
        (Seq.length boundTyVars)
        (fromJust . (boundTyVars Seq.!?))
  modify $
    \tc ->
      tc
      { _tcTypeSupply = n + 1
      , _tcEntries =
        _tcEntries tc Seq.|>
        TEntry m (KUnsolved ((\(a, _, b) -> (a, b)) <$> bs) k)
      }
  pure $
    TSubst
      (THole m)
      ((\(_, a, _) -> a) <$> bs)

freshKMeta :: MonadState (TCState ty) m => m KMeta
freshKMeta = do
  n <- gets _tcKindSupply
  let m = KMeta n
  modify $
    \tc ->
      tc
      { _tcKindSupply = n + 1
      , _tcEntries = _tcEntries tc Seq.|> KEntry m
      }
  pure m

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
  (Name -> Maybe Kind) ->
  (ty' -> Maybe Kind) ->
  Type ty' ->
  Kind ->
  m ()
checkKind nameTy ctxG ctx ty ki = do
  ki' <- inferKind nameTy ctxG ctx ty
  unifyKind ki ki'

inferKind ::
  (MonadState (TCState ty) m, MonadError TypeError m) =>
  (ty' -> Name) ->
  (Name -> Maybe Kind) ->
  (ty' -> Maybe Kind) ->
  Type ty' ->
  m Kind
inferKind nameTy ctxG ctx ty =
  case ty of
    THole n -> lookupTMeta n
    TVar a ->
      maybe (throwError . NotInScope $ nameTy a) pure (ctx a)
    TName a ->
      maybe (throwError $ NotInScope a) pure (ctxG a)
    TForall n body -> do
      k <- KHole <$> freshKMeta
      inferKind
        (unvar (\() -> n) nameTy)
        ctxG
        (unvar (\() -> Just k) ctx)
        (Bound.fromScope body)
    TArr a b -> do
      checkKind nameTy ctxG ctx a KType
      checkKind nameTy ctxG ctx b KType
      pure KType
    TUnsolved ns body ->
      inferKind
        (unvar (fst . (ns Vector.!)) absurd)
        ctxG
        (unvar (Just . snd . (ns Vector.!)) absurd)
        (Bound.fromScope body)
    TSubst a bs -> do
      aKind <- inferKind nameTy ctxG ctx a
      case aKind of
        KUnsolved ns bodyKind ->
          let
            lbs = length bs
            lns = length ns
          in
            if lns == lbs
            then
              bodyKind <$
              traverse_
                (\(x, y) -> checkKind nameTy ctxG ctx x (snd y))
                (Vector.zip bs ns)
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

substTMetas_Holes :: Map TMeta (Type Void) -> Holes ty tm -> Holes ty tm
substTMetas_Holes s hs =
  case hs of
    Nil -> Nil
    Cons p ty rest -> Cons p (substTMetas s ty) $ substTMetas_Holes s rest

applySolutions_Holes ::
  MonadState (TCState ty) m =>
  Holes ty' tm' -> m (Holes ty' tm')
applySolutions_Holes hs = do
  substs <- gets _tcSubst
  pure $ substTMetas_Holes substs hs

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
              , _tcSubst = Map.insert n t $ substTMeta (n, t) <$> _tcSubst tc
              }
          | otherwise ->
            go prefix' suffix (entry Seq.<| sig) n t

applySolutions :: MonadState (TCState ty) m => Type ty' -> m (Type ty')
applySolutions ty = do
  subst <- gets _tcSubst
  pure $ substTMetas subst ty

runSubst :: Type ty -> Type ty
runSubst ty =
  case ty of
    TSubst a bs ->
      case a of
        TUnsolved _ body ->
          Scope.instantiateEither (either (bs Vector.!) absurd) body
        _ -> ty
    _ -> ty

typeMismatch ::
  MonadError TypeError m =>
  (ty -> Name) ->
  Type ty ->
  Type ty ->
  m a
typeMismatch nameTy expected actual =
  throwError $ TypeMismatch (nameTy <$> expected) (nameTy <$> actual)

unifyType ::
  ( MonadState (TCState ty) m, MonadError TypeError m
  , Eq ty'
  ) =>
  (ty' -> Name) ->
  (Name -> Maybe Kind) ->
  (ty' -> Maybe Kind) ->
  Type ty' ->
  Type ty' ->
  m ()
unifyType nameTy ctxG ctx expected actual =
  case runSubst expected of
    THole n ->
      case runSubst actual of
        THole n' -> solveTMeta n (THole n')
        _ -> typeMismatch nameTy expected actual
    TVar a ->
      case runSubst actual of
        TVar a' | a == a' -> pure ()
        THole n -> error "todo" n
        _ -> typeMismatch nameTy expected actual
    TName a ->
      case runSubst actual of
        TName a' | a == a' -> pure ()
        THole n -> error "todo" n
        _ -> typeMismatch nameTy expected actual
    TForall _ body ->
      case runSubst actual of
        TForall n' body' -> do
          k <- KHole <$> freshKMeta
          unifyType
            (unvar (\() -> n') nameTy)
            ctxG
            (unvar (\() -> Just k) ctx)
            (Bound.fromScope body)
            (Bound.fromScope body')
        THole n -> error "todo" n
        _ -> typeMismatch nameTy expected actual
    TArr a b ->
      case runSubst actual of
        TArr a' b' -> do
          unifyType nameTy ctxG ctx a a'
          unifyType nameTy ctxG ctx b b'
        THole n -> error "todo" n
        _ -> typeMismatch nameTy expected actual
    TUnsolved ns body ->
      case runSubst actual of
        TUnsolved ns' body' | length ns == length ns' -> do
          traverse_
            (\(a, b) ->
               if fst a == fst b
               then unifyKind (snd a) (snd b)
               else typeMismatch nameTy expected actual
            )
            (Vector.zip ns ns')
          unifyType
            (unvar (fst . (ns' Vector.!)) absurd)
            ctxG
            (unvar (Just . snd . (ns' Vector.!)) absurd)
            (Bound.fromScope body)
            (Bound.fromScope body')
        THole n -> error "todo" n
        _ -> typeMismatch nameTy expected actual
    TSubst (THole n) bs -> do
      k <- lookupTMeta n
      case k of
        KUnsolved ns bodyK -> do
          let
            lbs = length bs
            lns = length ns
          when (lbs /= lns) . throwError $ ArityMismatch lns lbs
          traverse_
            (\(nn, b) -> checkKind nameTy ctxG ctx b (snd nn))
            (Vector.zip ns bs)
          let
            actual' =
              traverse
                (\v ->
                   case Vector.findIndex ((nameTy v ==) . fst) ns of
                     Nothing -> Left v
                     Just ix -> Right $ Bound.B ix
                )
                actual
          case actual' of
            Left v -> throwError $ Escape (nameTy v)
            Right sol -> do
              checkKind
                (unvar (fst . (ns Vector.!)) absurd)
                ctxG
                (unvar (Just . snd . (ns Vector.!)) absurd)
                sol
                bodyK
              solveTMeta n $ TUnsolved ns (Bound.toScope sol)
        KHole kn -> error "todo" kn
        _ -> undefined
    TSubst{} -> undefined

check ::
  (Eq ty', Show ty', MonadState (TCState ty) m, MonadError TypeError m) =>
  (tm' -> Name) ->
  (ty' -> Name) ->
  (Name -> Maybe (Type ty')) ->
  (tm' -> Maybe (Type ty')) ->
  (Name -> Maybe Kind) ->
  (ty' -> Maybe Kind) ->
  Seq (Name, Type ty', Kind) ->
  Path (Term ty tm) (Term ty' tm') ->
  Term ty' tm' ->
  Type ty' ->
  m (Holes ty tm)
check name nameTy ctxG ctx tyctxG tyctx boundTyVars path tm ty = do
  (ty', holes) <- infer name nameTy ctxG ctx tyctxG tyctx boundTyVars path tm
  unifyType nameTy tyctxG tyctx ty ty'
  applySolutions_Holes holes

infer ::
  forall ty tm ty' tm' m.
  (Eq ty', Show ty', MonadState (TCState ty) m, MonadError TypeError m) =>
  (tm' -> Name) ->
  (ty' -> Name) ->
  (Name -> Maybe (Type ty')) ->
  (tm' -> Maybe (Type ty')) ->
  (Name -> Maybe Kind) ->
  (ty' -> Maybe Kind) ->
  Seq (Name, Type ty', Kind) ->
  Path (Term ty tm) (Term ty' tm') ->
  Term ty' tm' ->
  m (Type ty', Holes ty tm)
infer name nameTy ctxG ctx tyctxG tyctx boundTyVars path tm =
  case tm of
    Hole -> do
      t <- freshTMeta boundTyVars KType
      pure (t, Cons path (t :: Type ty') Nil)
    Var a ->
      case ctx a of
        Nothing -> throwError $ NotInScope (name a)
        Just ty -> pure (ty, Nil)
    Name a ->
      case ctxG a of
        Nothing -> throwError $ NotInScope a
        Just ty -> pure (ty, Nil)
    LamAnn n ty body -> do
      let bodyPath = Path.snoc path Path.LamAnnBody
      (bodyTy, bodyHoles) <-
        infer
          (unvar (\() -> n) name)
          nameTy
          ctxG
          (unvar (\() -> Just ty) ctx)
          tyctxG
          tyctx
          boundTyVars
          bodyPath
          (Bound.fromScope body)
      pure (Syntax.TArr ty bodyTy, bodyHoles)
    Lam n body -> do
      ty <- freshTMeta boundTyVars KType
      let bodyPath = Path.snoc path Path.LamBody
      (bodyTy, bodyHoles) <-
        infer
          (unvar (\() -> n) name)
          nameTy
          ctxG
          (unvar (\() -> Just ty) ctx)
          tyctxG
          tyctx
          boundTyVars
          bodyPath
          (Bound.fromScope body)
      pure (Syntax.TArr ty bodyTy, bodyHoles)
    App f x -> do
      let fPath = Path.snoc path Path.AppL
      let xPath = Path.snoc path Path.AppR
      (fTy, fHoles) <-
        infer
          name
          nameTy
          ctxG
          ctx
          tyctxG
          tyctx
          boundTyVars
          fPath
          f
      inTy <- freshTMeta boundTyVars KType
      outTy <- freshTMeta boundTyVars KType
      unifyType nameTy tyctxG tyctx (TArr inTy outTy) fTy
      inTy' <- applySolutions inTy
      xHoles <-
        check
          name
          nameTy
          ctxG
          ctx
          tyctxG
          tyctx
          boundTyVars
          xPath
          x
          inTy'
      outTy' <- applySolutions outTy
      holes <- applySolutions_Holes $ appendHoles fHoles xHoles
      pure
        ( outTy'
        , holes
        )
