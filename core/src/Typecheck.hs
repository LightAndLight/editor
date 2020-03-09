{-# language FlexibleContexts #-}
{-# language GADTs, StandaloneDeriving #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables, TypeApplications #-}
module Typecheck where

import qualified Bound
import Bound.Var (unvar)
import Control.Lens.Indexed (itraverse_)
import Control.Monad (when)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, gets, modify)
import Data.Foldable (toList, traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Vector (Vector)
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

data Holes ty tm where
  ConsHole ::
    Path (Term ty tm) (Term ty' tm') ->
    (ty' -> Name) ->
    Type ty' ->
    Holes ty tm ->
    Holes ty tm
  ConsTHole ::
    Path (Term ty tm) (Term ty' tm') ->
    Path (Type ty') (Type ty'') ->
    Kind ->
    Holes ty tm ->
    Holes ty tm
  Nil :: Holes ty tm

substTMetas_Holes :: Map TMeta (Type Void) -> Holes ty tm -> Holes ty tm
substTMetas_Holes s hs =
  case hs of
    Nil -> Nil
    ConsHole p ns ty rest ->
      ConsHole p ns (substTMetas s ty) $ substTMetas_Holes s rest
    ConsTHole p1 p2 k rest ->
      ConsTHole p1 p2 k $ substTMetas_Holes s rest

substKMetas_Holes :: Map KMeta Kind -> Holes ty tm -> Holes ty tm
substKMetas_Holes s hs =
  case hs of
    Nil -> Nil
    ConsHole p ns ty rest ->
      ConsHole p ns ty $ substKMetas_Holes s rest
    ConsTHole p1 p2 k rest ->
      ConsTHole p1 p2 (substKMetas s k) $ substKMetas_Holes s rest

applySolutions_Holes ::
  MonadState (TCState ty tm) m =>
  m ()
applySolutions_Holes = do
  substs <- gets _tcSubst
  modify $ \tc -> tc { _tcHoles = substTMetas_Holes substs (_tcHoles tc) }

applySolutions_THoles ::
  MonadState (TCState ty tm) m =>
  m ()
applySolutions_THoles = do
  substs <- gets _tcKindSubst
  modify $ \tc -> tc { _tcHoles = substKMetas_Holes substs (_tcHoles tc) }

addHole ::
  MonadState (TCState ty tm) m =>
  Path (Term ty tm) (Term ty' tm') ->
  (ty' -> Name) ->
  Type ty' ->
  m ()
addHole path nameTy t =
  modify $
  \tc -> tc { _tcHoles = ConsHole path nameTy t (_tcHoles tc) }

addTHole ::
  MonadState (TCState ty tm) m =>
  KCEnv ty tm ty' tm' ->
  Kind ->
  m ()
addTHole (KCEnv { _keTmPath = path1, _keTyPath = path2 }) t =
  modify $
  \tc -> tc { _tcHoles = ConsTHole path1 path2 t (_tcHoles tc) }

appendHoles :: Holes ty tm -> Holes ty tm -> Holes ty tm
appendHoles Nil hs = hs
appendHoles (ConsHole p ns ty rest) hs = ConsHole p ns ty $ appendHoles rest hs
appendHoles (ConsTHole p1 p2 k rest) hs = ConsTHole p1 p2 k $ appendHoles rest hs

data TCState ty tm
  = TCState
  { _tcTypeSupply :: Int
  , _tcKindSupply :: Int
  , _tcEntries :: Seq Entry
  , _tcSubst :: Map TMeta (Type Void)
  , _tcKindSubst :: Map KMeta Kind
  , _tcHoles :: Holes ty tm
  }

emptyTCState :: TCState ty tm
emptyTCState =
  TCState
  { _tcTypeSupply = 0
  , _tcKindSupply = 0
  , _tcEntries = mempty
  , _tcSubst = mempty
  , _tcKindSubst = mempty
  , _tcHoles = Nil
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
  MonadState (TCState ty tm) m =>
  Seq (Name, Type ty', Kind) ->
  Kind ->
  m (Type ty')
freshTMeta boundTyVars k = do
  n <- gets _tcTypeSupply
  let
    m = TM n
    bs =
      Vector.generate
        (Seq.length boundTyVars)
        (fromJust . (boundTyVars Seq.!?))
    entry = TEntry m (KUnsolved ((\(a, _, b) -> (a, b)) <$> bs) k)

  modify $
    \tc ->
      tc
      { _tcTypeSupply = n + 1
      , _tcEntries = _tcEntries tc Seq.|> entry
      }
  pure $
    TSubst
      (TMeta m)
      ((\(_, a, _) -> a) <$> bs)

freshKMeta :: MonadState (TCState ty tm) m => m KMeta
freshKMeta = do
  n <- gets _tcKindSupply
  let m = KM n
  modify $
    \tc ->
      tc
      { _tcKindSupply = n + 1
      , _tcEntries = _tcEntries tc Seq.|> KEntry m
      }
  pure m

lookupTMeta ::
  (MonadState (TCState ty tm) m, MonadError TypeError m) =>
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
  MonadState (TCState ty tm) m =>
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
          | KEntry nn <- entry, n == nn ->
            let
              appendSolving =
                flip $ foldl (\acc x -> acc Seq.|> substKMeta_Entry (n, k) x)
            in
            modify $
            \tc ->
              tc
              { _tcEntries =
                appendSolving suffix $ appendSolving sig prefix
              , _tcKindSubst = Map.insert n k $ substKMeta (n, k) <$> _tcKindSubst tc
              }
          | otherwise ->
            if occursK_Entry n entry
            then go prefix' (entry Seq.<| suffix) sig n k
            else go prefix' suffix (entry Seq.<| sig) n k

unifyKind ::
  (MonadState (TCState ty tm) m, MonadError TypeError m) =>
  Kind ->
  Kind ->
  m ()
unifyKind expected actual =
  case expected of
    KUnsolved ctx k ->
      case actual of
        KMeta n -> solveKMeta n expected
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
        KMeta n -> solveKMeta n expected
        KType -> pure ()
        _ -> throwError $ KindMismatch expected actual
    KMeta n -> solveKMeta n actual

data KCEnv a b a' b' where
  KCEnv ::
    { _keName :: ty'' -> Name
    , _keGlobalCtx :: Name -> Maybe Kind
    , _keCtx :: ty'' -> Maybe Kind
    , _keTmPath :: Path (Term ty tm) (Term ty' tm'')
    , _keTyPath :: Path (Type ty') (Type ty'')
    } ->
    KCEnv ty tm ty'' tm''

withTmTyPath ::
  KCEnv ty tm ty' tm' ->
  (forall x.
   Path (Term ty tm) (Term x tm') ->
   Path (Type x) (Type ty') ->
   r
  ) ->
  r
withTmTyPath (KCEnv { _keTmPath = x, _keTyPath = y }) f = f x y

checkKind ::
  (MonadState (TCState ty tm) m, MonadError TypeError m) =>
  KCEnv ty tm ty' tm' ->
  Type ty' ->
  Kind ->
  m ()
checkKind kindEnv ty ki = do
  ki' <- inferKind kindEnv ty
  unifyKind ki ki'
  applySolutions_THoles

inferKind ::
  (MonadState (TCState ty tm) m, MonadError TypeError m) =>
  KCEnv ty tm ty' tm' ->
  Type ty' ->
  m Kind
inferKind kindEnv ty =
  case runSubst ty of
    THole -> do
      k <- KMeta <$> freshKMeta
      addTHole kindEnv k
      pure k
    TMeta n -> lookupTMeta n
    TVar a ->
      maybe (throwError . NotInScope $ _keName kindEnv a) pure (_keCtx kindEnv a)
    TName a ->
      maybe (throwError $ NotInScope a) pure (_keGlobalCtx kindEnv a)
    TForall n body -> do
      k <- KMeta <$> freshKMeta
      withTmTyPath kindEnv $ \tmPath tyPath ->
        inferKind
          (KCEnv
          { _keName = unvar (\() -> n) (_keName kindEnv)
          , _keGlobalCtx = _keGlobalCtx kindEnv
          , _keCtx = unvar (\() -> Just k) (_keCtx kindEnv)
          , _keTmPath = tmPath
          , _keTyPath = Path.snoc tyPath Path.TForallBody
          }
          )
          (Bound.fromScope body)
    TArr a b -> do
      withTmTyPath kindEnv $ \tmPath tyPath -> do
        checkKind
          (KCEnv
           { _keName = _keName kindEnv
           , _keGlobalCtx = _keGlobalCtx kindEnv
           , _keCtx = _keCtx kindEnv
           , _keTmPath = tmPath
           , _keTyPath = Path.snoc tyPath Path.TArrL
           }
          )
          a
          KType
        checkKind
          (KCEnv
           { _keName = _keName kindEnv
           , _keGlobalCtx = _keGlobalCtx kindEnv
           , _keCtx = _keCtx kindEnv
           , _keTmPath = tmPath
           , _keTyPath = Path.snoc tyPath Path.TArrR
           }
          )
          b
          KType
      pure KType
    TUnsolved ns body ->
      withTmTyPath kindEnv $ \tmPath tyPath ->
        KUnsolved ns <$>
        inferKind
          (KCEnv
          { _keName = unvar (fst . (ns Vector.!)) absurd
          , _keGlobalCtx = _keGlobalCtx kindEnv
          , _keCtx = unvar (Just . snd . (ns Vector.!)) absurd
          , _keTmPath = tmPath
          , _keTyPath = Path.snoc tyPath Path.TUnsolvedBody
          }
          )
          (Bound.fromScope body)
    TSubst a bs -> do
      aKind <-
        withTmTyPath kindEnv $ \tmPath tyPath ->
        inferKind
          (KCEnv
           { _keName = _keName kindEnv
           , _keGlobalCtx = _keGlobalCtx kindEnv
           , _keCtx = _keCtx kindEnv
           , _keTmPath = tmPath
           , _keTyPath = Path.snoc tyPath Path.TSubstL
           }
          )
          a
      case aKind of
        KUnsolved ns bodyKind ->
          let
            lbs = length bs
            lns = length ns
          in
            if lns == lbs
            then
              bodyKind <$
              itraverse_
                (\i (x, y) ->
                   withTmTyPath kindEnv $ \tmPath tyPath ->
                   checkKind
                     (KCEnv
                      { _keName = _keName kindEnv
                      , _keGlobalCtx = _keGlobalCtx kindEnv
                      , _keCtx = _keCtx kindEnv
                      , _keTmPath = tmPath
                      , _keTyPath = Path.snoc tyPath $ Path.TSubstR i
                      }
                     )
                     x
                     (snd y)
                )
                (Vector.zip bs ns)
            else throwError $ ArityMismatch lns lbs
        _ -> throwError $ ExpectedKUnsolved aKind

solveTMeta ::
  (MonadError TypeError m, MonadState (TCState ty tm) m) =>
  KCEnv ty tm ty' tm' ->
  TMeta ->
  Type Void ->
  m ()
solveTMeta kindEnv n' t' = do
  prefix <- gets _tcEntries
  let suffix = mempty
  let sig = mempty
  go prefix suffix sig n' t'
  where
    go prefix suffix sig n t =
      case Seq.viewr prefix of
        Seq.EmptyR -> undefined
        prefix' Seq.:> entry
          | TEntry nn k <- entry, n == nn -> do
            checkKind kindEnv (absurd <$> t) k
            modify $
              \tc ->
                tc
                { _tcEntries = prefix <> sig <> suffix
                , _tcSubst = Map.insert n t $ substTMeta (n, t) <$> _tcSubst tc
                }
          | otherwise ->
            go prefix' suffix (entry Seq.<| sig) n t

applySolutions :: MonadState (TCState ty tm) m => Type ty' -> m (Type ty')
applySolutions ty = do
  subst <- gets _tcSubst
  pure $ substTMetas subst ty

typeMismatch ::
  MonadError TypeError m =>
  (ty -> Name) ->
  Type ty ->
  Type ty ->
  m a
typeMismatch nameTy expected actual =
  throwError $ TypeMismatch (nameTy <$> expected) (nameTy <$> actual)

inversion ::
  ( MonadState (TCState ty tm) m, MonadError TypeError m
  ) =>
  KCEnv ty tm ty' tm' ->
  TMeta ->
  Vector (Type ty') ->
  Type ty' ->
  m ()
inversion kindEnv n bs ty = do
  k <- lookupTMeta n
  case k of
    KUnsolved ns _ -> do
      let
        lbs = length bs
        lns = length ns
      when (lbs /= lns) . throwError $ ArityMismatch lns lbs
      itraverse_
        (\i (nn, b) ->
           withTmTyPath kindEnv $ \tmPath tyPath ->
           checkKind
             (KCEnv
              { _keName = _keName kindEnv
              , _keGlobalCtx = _keGlobalCtx kindEnv
              , _keCtx = _keCtx kindEnv
              , _keTmPath = tmPath
              , _keTyPath = Path.snoc tyPath $ Path.TSubstR i
              }
             )
             b
             (snd nn)
        )
        (Vector.zip ns bs)
      let
        ty' =
          TUnsolved ns . Bound.toScope <$>
          traverse
            (\v ->
                case Vector.findIndex ((_keName kindEnv v ==) . fst) ns of
                  Nothing -> Left v
                  Just ix -> Right $ Bound.B ix
            )
            (runSubst ty)
      case ty' of
        Left v -> throwError $ Escape (_keName kindEnv v)
        Right sol -> solveTMeta kindEnv n sol
    KMeta kn -> error "todo" kn
    _ -> undefined

inversion0 ::
  ( MonadState (TCState ty tm) m, MonadError TypeError m
  ) =>
  KCEnv ty tm ty' tm' ->
  TMeta ->
  Type ty' ->
  m ()
inversion0 kindEnv n ty = do
  case TUnsolved mempty . Bound.toScope <$> traverse (const Nothing) ty of
    Nothing -> throwError $ Escape (_keName kindEnv . head $ toList ty)
    Just ty' -> solveTMeta kindEnv n ty'

unifyType ::
  ( MonadState (TCState ty tm) m, MonadError TypeError m
  , Eq ty'
  ) =>
  KCEnv ty tm ty' tm' ->
  Type ty' ->
  Type ty' ->
  m ()
unifyType kindEnv expected actual =
  case runSubst expected of
    THole -> pure ()
    TSubst (TMeta n) bs -> inversion kindEnv n bs actual
    TMeta n -> inversion0 kindEnv n actual
    TVar a ->
      case runSubst actual of
        TVar a' | a == a' -> pure ()
        TSubst (TMeta n) bs -> inversion kindEnv n bs expected
        TMeta n -> inversion0 kindEnv n expected
        THole -> pure ()
        _ -> typeMismatch (_keName kindEnv) expected actual
    TName a ->
      case runSubst actual of
        TName a' | a == a' -> pure ()
        TSubst (TMeta n) bs -> inversion kindEnv n bs expected
        TMeta n -> inversion0 kindEnv n expected
        THole -> pure ()
        _ -> typeMismatch (_keName kindEnv) expected actual
    TForall _ body ->
      case runSubst actual of
        TForall n' body' -> do
          k <- KMeta <$> freshKMeta
          withTmTyPath kindEnv $ \tmPath tyPath ->
            unifyType
              (KCEnv
               { _keName = unvar (\() -> n') (_keName kindEnv)
               , _keGlobalCtx = _keGlobalCtx kindEnv
               , _keCtx = unvar (\() -> Just k) (_keCtx kindEnv)
               , _keTmPath = tmPath
               , _keTyPath = Path.snoc tyPath Path.TForallBody
               }
              )
              (Bound.fromScope body)
              (Bound.fromScope body')
        TSubst (TMeta n) bs -> inversion kindEnv n bs expected
        TMeta n -> inversion0 kindEnv n expected
        THole -> pure ()
        _ -> typeMismatch (_keName kindEnv) expected actual
    TArr a b ->
      case runSubst actual of
        TArr a' b' ->
          withTmTyPath kindEnv $ \tmPath tyPath -> do
            unifyType
              (KCEnv
                { _keName = _keName kindEnv
                , _keGlobalCtx = _keGlobalCtx kindEnv
                , _keCtx = _keCtx kindEnv
                , _keTmPath = tmPath
                , _keTyPath = Path.snoc tyPath Path.TArrL
                }
              )
              a
              a'
            unifyType
              (KCEnv
                { _keName = _keName kindEnv
                , _keGlobalCtx = _keGlobalCtx kindEnv
                , _keCtx = _keCtx kindEnv
                , _keTmPath = tmPath
                , _keTyPath = Path.snoc tyPath Path.TArrR
                }
              )
              b
              b'
        TSubst (TMeta n) bs -> inversion kindEnv n bs expected
        TMeta n -> inversion0 kindEnv n expected
        THole -> pure ()
        _ -> typeMismatch (_keName kindEnv) expected actual
    TUnsolved ns body ->
      case runSubst actual of
        TUnsolved ns' body' | length ns == length ns' -> do
          traverse_
            (\(a, b) ->
               if fst a == fst b
               then do
                 unifyKind (snd a) (snd b)
                 applySolutions_THoles
               else typeMismatch (_keName kindEnv) expected actual
            )
            (Vector.zip ns ns')
          withTmTyPath kindEnv $ \tmPath tyPath ->
            unifyType
              (KCEnv
               { _keName = unvar (fst . (ns' Vector.!)) absurd
               , _keGlobalCtx = _keGlobalCtx kindEnv
               , _keCtx = unvar (Just . snd . (ns' Vector.!)) absurd
               , _keTmPath = tmPath
               , _keTyPath = Path.snoc tyPath Path.TUnsolvedBody
               }
              )
              (Bound.fromScope body)
              (Bound.fromScope body')
        TSubst (TMeta n) bs -> inversion kindEnv n bs expected
        TMeta n -> inversion0 kindEnv n expected
        THole -> pure ()
        _ -> typeMismatch (_keName kindEnv) expected actual
    TSubst{} -> undefined

check ::
  (Eq ty', MonadState (TCState ty tm) m, MonadError TypeError m) =>
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
  m ()
check name nameTy ctxG ctx tyctxG tyctx boundTyVars path tm ty = do
  ty' <- infer name nameTy ctxG ctx tyctxG tyctx boundTyVars path tm
  unifyType
    (KCEnv
     { _keName = nameTy
     , _keGlobalCtx = tyctxG
     , _keCtx = tyctx
     , _keTmPath = path
     , _keTyPath = Path.empty
     })
    ty
    ty'
  applySolutions_Holes

infer ::
  forall ty tm ty' tm' m.
  (Eq ty', MonadState (TCState ty tm) m, MonadError TypeError m) =>
  (tm' -> Name) ->
  (ty' -> Name) ->
  (Name -> Maybe (Type ty')) ->
  (tm' -> Maybe (Type ty')) ->
  (Name -> Maybe Kind) ->
  (ty' -> Maybe Kind) ->
  Seq (Name, Type ty', Kind) ->
  Path (Term ty tm) (Term ty' tm') ->
  Term ty' tm' ->
  m (Type ty')
infer name nameTy ctxG ctx tyctxG tyctx boundTyVars path tm =
  case tm of
    Ann a t -> do
      checkKind
        (KCEnv
          { _keName = nameTy
          , _keGlobalCtx = tyctxG
          , _keCtx = tyctx
          , _keTmPath = path
          , _keTyPath = Path.empty
          }
        )
        t
        KType
      t <$ check name nameTy ctxG ctx tyctxG tyctx boundTyVars (Path.snoc path Path.AnnL) a t
    Hole -> do
      t <- freshTMeta boundTyVars KType
      addHole path nameTy (t :: Type ty')
      pure t
    Var a ->
      case ctx a of
        Nothing -> throwError $ NotInScope (name a)
        Just ty -> pure ty
    Name a ->
      case ctxG a of
        Nothing -> throwError $ NotInScope a
        Just ty -> pure ty
    LamAnn n ty body -> do
      let bodyPath = Path.snoc path Path.LamAnnBody
      bodyTy <-
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
      pure $ Syntax.TArr ty bodyTy
    Lam n body -> do
      ty <- freshTMeta boundTyVars KType
      let bodyPath = Path.snoc path Path.LamBody
      bodyTy <-
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
      pure $ Syntax.TArr ty bodyTy
    App f x -> do
      let fPath = Path.snoc path Path.AppL
      let xPath = Path.snoc path Path.AppR
      fTy <-
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
      unifyType
        (KCEnv
         { _keName = nameTy
         , _keGlobalCtx = tyctxG
         , _keCtx = tyctx
         , _keTmPath = fPath
         , _keTyPath = Path.empty
         })
        (TArr inTy outTy)
        fTy
      inTy' <- applySolutions inTy
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
      applySolutions_Holes
      pure outTy'
