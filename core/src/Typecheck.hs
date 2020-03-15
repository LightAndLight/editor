{-# language FlexibleContexts #-}
{-# language GADTs, StandaloneDeriving #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables, TypeApplications #-}
module Typecheck where

import qualified Bound
import Bound.Var (unvar)
import Control.Lens.Indexed (ifoldr, itraverse_)
import Control.Monad (when)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, gets, modify)
import Data.Foldable (toList, traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)

import Path (Path)
import qualified Path
import qualified Path.Map
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

data Holes a where
  ConsHole ::
    Path a (Term ty' tm') ->
    (ty' -> Name) ->
    Type ty' ->
    Holes a ->
    Holes a
  ConsTHoleTerm ::
    Path a (Term ty' tm') ->
    Path (Type ty') (Type ty'') ->
    Kind ->
    Holes a ->
    Holes a
  ConsTHoleType ::
    Path a (Type ty'') ->
    Kind ->
    Holes a ->
    Holes a
  Nil :: Holes a

substTMetas_Holes :: Map TMeta (Type Void) -> Holes a -> Holes a
substTMetas_Holes s hs =
  case hs of
    Nil -> Nil
    ConsHole p ns ty rest ->
      ConsHole p ns (substTMetas s ty) $ substTMetas_Holes s rest
    ConsTHoleTerm p1 p2 k rest ->
      ConsTHoleTerm p1 p2 k $ substTMetas_Holes s rest
    ConsTHoleType p1 k rest ->
      ConsTHoleType p1 k $ substTMetas_Holes s rest

substKMetas_Holes :: Map KMeta Kind -> Holes a -> Holes a
substKMetas_Holes s hs =
  case hs of
    Nil -> Nil
    ConsHole p ns ty rest ->
      ConsHole p ns ty $ substKMetas_Holes s rest
    ConsTHoleTerm p1 p2 k rest ->
      ConsTHoleTerm p1 p2 (substKMetas s k) $ substKMetas_Holes s rest
    ConsTHoleType p1 k rest ->
      ConsTHoleType p1 (substKMetas s k) $ substKMetas_Holes s rest

data Info a where
  TermInfo :: (ty -> Name) -> Type ty -> Info (Term ty tm)
  TypeInfo :: Kind -> Info (Type ty)

data TCState a
  = TCState
  { _tcTypeSupply :: Int
  , _tcKindSupply :: Int
  , _tcEntries :: Seq Entry
  , _tcSubst :: Map TMeta (Type Void)
  , _tcKindSubst :: Map KMeta Kind
  , _tcHoles :: Holes a
  , _tcInfo :: Path.Map.Map a Info
  , _tcCheckedDecls :: Map Name Decl
  }

emptyTCState :: TCState a
emptyTCState =
  TCState
  { _tcTypeSupply = 0
  , _tcKindSupply = 0
  , _tcEntries = mempty
  , _tcSubst = mempty
  , _tcKindSubst = mempty
  , _tcHoles = Nil
  , _tcInfo = Path.Map.empty
  , _tcCheckedDecls = mempty
  }

addInfo ::
  MonadState (TCState a) m =>
  Path a b ->
  Info b ->
  m ()
addInfo p i =
  modify $ \tc -> tc { _tcInfo = Path.Map.insert p i $ _tcInfo tc }

applySolutions_Holes ::
  MonadState (TCState a) m =>
  m ()
applySolutions_Holes = do
  substs <- gets _tcSubst
  modify $ \tc -> tc { _tcHoles = substTMetas_Holes substs (_tcHoles tc) }

applySolutions_THoles ::
  MonadState (TCState a) m =>
  m ()
applySolutions_THoles = do
  substs <- gets _tcKindSubst
  modify $ \tc -> tc { _tcHoles = substKMetas_Holes substs (_tcHoles tc) }

addHole ::
  MonadState (TCState a) m =>
  Path a (Term ty' tm') ->
  (ty' -> Name) ->
  Type ty' ->
  m ()
addHole path nameTy t =
  modify $
  \tc -> tc { _tcHoles = ConsHole path nameTy t (_tcHoles tc) }

data KCEnv a a' b' where
  KCEnvTerm ::
    { _keName :: ty'' -> Name
    , _keGlobalCtx :: Name -> Maybe Kind
    , _keCtx :: ty'' -> Maybe Kind
    , _keTmPath :: Path a (Term ty' tm'')
    , _keTermTyPath :: Path (Type ty') (Type ty'')
    } ->
    KCEnv a ty'' tm''
  KCEnvType ::
    { _keName :: ty'' -> Name
    , _keGlobalCtx :: Name -> Maybe Kind
    , _keCtx :: ty'' -> Maybe Kind
    , _keTypeTyPath :: Path a (Type ty'')
    } ->
    KCEnv a ty'' tm''

updateKCEnv ::
  ((ty -> Name) -> (ty' -> Name)) ->
  ((ty -> Maybe Kind) -> (ty' -> Maybe Kind)) ->
  (forall x. Path x (Type ty) -> Path x (Type ty')) ->
  KCEnv a ty tm ->
  KCEnv a ty' tm
updateKCEnv fName fCtx fPath ke =
  case ke of
    KCEnvTerm
      { _keName = name
      , _keGlobalCtx = ctxG
      , _keCtx = ctx
      , _keTmPath = tmPath
      , _keTermTyPath = tyPath
      } ->
        KCEnvTerm
        { _keName = fName name
        , _keGlobalCtx = ctxG
        , _keCtx = fCtx ctx
        , _keTmPath = tmPath
        , _keTermTyPath = fPath tyPath
        }
    KCEnvType
      { _keName = name
      , _keGlobalCtx = ctxG
      , _keCtx = ctx
      , _keTypeTyPath = tyPath
      } ->
        KCEnvType
        { _keName = fName name
        , _keGlobalCtx = ctxG
        , _keCtx = fCtx ctx
        , _keTypeTyPath = fPath tyPath
        }

addTHole ::
  MonadState (TCState a) m =>
  KCEnv a ty' tm' ->
  Kind ->
  m ()
addTHole (KCEnvTerm { _keTmPath = path1, _keTermTyPath = path2 }) t =
  modify $
  \tc -> tc { _tcHoles = ConsTHoleTerm path1 path2 t (_tcHoles tc) }
addTHole (KCEnvType { _keTypeTyPath = path2 }) t =
  modify $
  \tc -> tc { _tcHoles = ConsTHoleType path2 t (_tcHoles tc) }

appendHoles :: Holes a -> Holes a -> Holes a
appendHoles Nil hs = hs
appendHoles (ConsHole p ns ty rest) hs = ConsHole p ns ty $ appendHoles rest hs
appendHoles (ConsTHoleTerm p1 p2 k rest) hs = ConsTHoleTerm p1 p2 k $ appendHoles rest hs
appendHoles (ConsTHoleType p1 k rest) hs = ConsTHoleType p1 k $ appendHoles rest hs

data TypeError
  = NotInScope Name
  | TMetaNotInScope TMeta
  | Can'tInfer (Term Name Name)
  | NotTArr (Term Name Name)
  | TypeMismatch (Type Name) (Type Name)
  | KindMismatch Kind Kind
  | ExpectedKUnsolved Kind
  | ArityMismatch Int Int
  | Escape Name
  deriving Show

printTypeError :: TypeError -> Text
printTypeError te =
  case te of
    KindMismatch k1 k2 -> "Expected kind: '" <> printKind k1 <> "' but got '" <> printKind k2 <> "'"
    TypeMismatch t1 t2 -> "Expected type: '" <> printType id t1 <> "' but got '" <> printType id t2 <> "'"
    _ -> Text.pack $ show te

freshTMeta ::
  MonadState (TCState a) m =>
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

freshKMeta :: MonadState (TCState a) m => m KMeta
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
  (MonadState (TCState a) m, MonadError TypeError m) =>
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
  MonadState (TCState a) m =>
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
  (MonadState (TCState a) m, MonadError TypeError m) =>
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
                 then
                   unifyKind (snd a) (snd b)
                 else
                   throwError $ KindMismatch expected actual
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

checkKind ::
  (MonadState (TCState a) m, MonadError TypeError m) =>
  KCEnv a ty' tm' ->
  Type ty' ->
  Kind ->
  m ()
checkKind kindEnv ty ki = do
  ki' <- inferKind kindEnv ty
  unifyKind ki ki'
  applySolutions_THoles

inferKind ::
  (MonadState (TCState a) m, MonadError TypeError m) =>
  KCEnv a ty' tm' ->
  Type ty' ->
  m Kind
inferKind kindEnv ty = do
  k <- inferKind' kindEnv ty
  case kindEnv of
    KCEnvType { _keTypeTyPath = tyPath }->
      addInfo tyPath $ TypeInfo KType
    _ -> pure ()
  pure k

inferKind' ::
  (MonadState (TCState a) m, MonadError TypeError m) =>
  KCEnv a ty' tm' ->
  Type ty' ->
  m Kind
inferKind' kindEnv ty =
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
      inferKind
        (updateKCEnv
          (\name -> unvar (\() -> n) name)
          (\ctx -> unvar (\() -> Just k) ctx)
          (\tyPath -> Path.snoc tyPath Path.TForallBody)
          kindEnv
        )
        (Bound.fromScope body)
    TArr a b -> do
      checkKind
        (updateKCEnv id id (\tyPath -> Path.snoc tyPath Path.TArrL) kindEnv)
        a
        KType
      checkKind
        (updateKCEnv id id (\tyPath -> Path.snoc tyPath Path.TArrR) kindEnv)
        b
        KType
      pure KType
    TUnsolved ns body ->
      KUnsolved ns <$>
      inferKind
        (updateKCEnv
          (\_ -> unvar (fst . (ns Vector.!)) absurd)
          (\_ -> unvar (Just . snd . (ns Vector.!)) absurd)
          (\tyPath -> Path.snoc tyPath Path.TUnsolvedBody)
          kindEnv
        )
        (Bound.fromScope body)
    TSubst a bs -> do
      aKind <-
        inferKind
          (updateKCEnv id id (\tyPath -> Path.snoc tyPath Path.TSubstL) kindEnv)
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
                   checkKind
                     (updateKCEnv id id (\tyPath -> Path.snoc tyPath $ Path.TSubstR i) kindEnv)
                     x
                     (snd y)
                )
                (Vector.zip bs ns)
            else throwError $ ArityMismatch lns lbs
        _ -> throwError $ ExpectedKUnsolved aKind

solveTMeta ::
  (MonadError TypeError m, MonadState (TCState a) m) =>
  KCEnv a ty' tm' ->
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

applySolutions :: MonadState (TCState a) m => Type ty' -> m (Type ty')
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
  ( MonadState (TCState a) m, MonadError TypeError m
  ) =>
  KCEnv a ty' tm' ->
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
           checkKind
             (updateKCEnv id id (\tyPath -> Path.snoc tyPath $ Path.TSubstR i) kindEnv)
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
  ( MonadState (TCState a) m, MonadError TypeError m
  ) =>
  KCEnv a ty' tm' ->
  TMeta ->
  Type ty' ->
  m ()
inversion0 kindEnv n ty = do
  case TUnsolved mempty . Bound.toScope <$> traverse (const Nothing) ty of
    Nothing -> throwError $ Escape (_keName kindEnv . head $ toList ty)
    Just ty' -> solveTMeta kindEnv n ty'

unifyType ::
  ( MonadState (TCState a) m, MonadError TypeError m
  , Eq ty'
  ) =>
  KCEnv a ty' tm' ->
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
          unifyType
            (updateKCEnv
                (\name -> unvar (\() -> n') name)
                (\ctx -> unvar (\() -> Just k) ctx)
                (\tyPath -> Path.snoc tyPath Path.TForallBody)
                kindEnv
            )
            (Bound.fromScope body)
            (Bound.fromScope body')
        TSubst (TMeta n) bs -> inversion kindEnv n bs expected
        TMeta n -> inversion0 kindEnv n expected
        THole -> pure ()
        _ -> typeMismatch (_keName kindEnv) expected actual
    TArr a b ->
      case runSubst actual of
        TArr a' b' -> do
          unifyType
            (updateKCEnv id id (\tyPath -> Path.snoc tyPath Path.TArrL) kindEnv)
            a
            a'
          unifyType
            (updateKCEnv id id (\tyPath -> Path.snoc tyPath Path.TArrR) kindEnv)
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
               else
                 typeMismatch (_keName kindEnv) expected actual
            )
            (Vector.zip ns ns')
          unifyType
            (updateKCEnv
              (\_ -> unvar (fst . (ns' Vector.!)) absurd)
              (\_ -> unvar (Just . snd . (ns' Vector.!)) absurd)
              (\tyPath -> Path.snoc tyPath Path.TUnsolvedBody)
              kindEnv
            )
            (Bound.fromScope body)
            (Bound.fromScope body')
        TSubst (TMeta n) bs -> inversion kindEnv n bs expected
        TMeta n -> inversion0 kindEnv n expected
        THole -> pure ()
        _ -> typeMismatch (_keName kindEnv) expected actual
    TSubst{} -> undefined

data TCEnv a ty' tm'
  = TCEnv
  { _teName :: tm' -> Name
  , _teNameTy :: ty' -> Name
  , _teGlobalCtx :: Name -> Maybe (Type ty')
  , _teCtx :: tm' -> Maybe (Type ty')
  , _teGlobalTyCtx :: Name -> Maybe Kind
  , _teTyCtx :: ty' -> Maybe Kind
  , _teBoundTyVars :: Seq (Name, Type ty', Kind)
  , _tePath :: Path a (Term ty' tm')
  }

check ::
  (Eq ty', MonadState (TCState a) m, MonadError TypeError m) =>
  TCEnv a ty' tm' ->
  Term ty' tm' ->
  Type ty' ->
  m ()
check tcEnv tm ty = do
  ty' <- infer tcEnv tm
  unifyType
    (KCEnvTerm
     { _keName = _teNameTy tcEnv
     , _keGlobalCtx = _teGlobalTyCtx tcEnv
     , _keCtx = _teTyCtx tcEnv
     , _keTmPath = _tePath tcEnv
     , _keTermTyPath = Path.empty
     })
    ty
    ty'
  applySolutions_Holes

infer ::
  forall a ty' tm' m.
  (Eq ty', MonadState (TCState a) m, MonadError TypeError m) =>
  TCEnv a ty' tm' ->
  Term ty' tm' ->
  m (Type ty')
infer tcEnv tm = do
  ty <- infer' tcEnv tm
  addInfo (_tePath tcEnv) $ TermInfo (_teNameTy tcEnv) ty
  pure ty

infer' ::
  forall a ty' tm' m.
  (Eq ty', MonadState (TCState a) m, MonadError TypeError m) =>
  TCEnv a ty' tm' ->
  Term ty' tm' ->
  m (Type ty')
infer' tcEnv tm =
  case tm of
    Ann a t -> do
      checkKind
        (KCEnvType
          { _keName = _teNameTy tcEnv
          , _keGlobalCtx = _teGlobalTyCtx tcEnv
          , _keCtx = _teTyCtx tcEnv
          , _keTypeTyPath = Path.snoc (_tePath tcEnv) Path.AnnR
          }
        )
        t
        KType
      t <$ check (tcEnv { _tePath = Path.snoc (_tePath tcEnv) Path.AnnL }) a t
    Hole -> do
      t <- freshTMeta (_teBoundTyVars tcEnv) KType
      addHole (_tePath tcEnv) (_teNameTy tcEnv) (t :: Type ty')
      pure t
    Var a ->
      case _teCtx tcEnv a of
        Nothing -> throwError $ NotInScope (_teName tcEnv a)
        Just ty -> pure ty
    Name a ->
      case _teGlobalCtx tcEnv a of
        Nothing -> throwError $ NotInScope a
        Just ty -> pure ty
    LamAnn n ty body -> do
      let tyPath = Path.snoc (_tePath tcEnv) Path.LamAnnType
      checkKind
        (KCEnvType
          { _keName = _teNameTy tcEnv
          , _keGlobalCtx = _teGlobalTyCtx tcEnv
          , _keCtx = _teTyCtx tcEnv
          , _keTypeTyPath = Path.snoc (_tePath tcEnv) Path.LamAnnType
          }
        )
        ty
        KType
      addInfo tyPath $ TypeInfo KType
      let bodyPath = Path.snoc (_tePath tcEnv) Path.LamAnnBody
      bodyTy <-
        infer
          (tcEnv
           { _teName = unvar (\() -> n) (_teName tcEnv)
           , _teCtx = unvar (\() -> Just ty) (_teCtx tcEnv)
           , _tePath = bodyPath
           }
          )
          (Bound.fromScope body)
      pure $ Syntax.TArr ty bodyTy
    Lam n body -> do
      ty <- freshTMeta (_teBoundTyVars tcEnv) KType
      let bodyPath = Path.snoc (_tePath tcEnv) Path.LamBody
      bodyTy <-
        infer
          (tcEnv
           { _teName = unvar (\() -> n) (_teName tcEnv)
           , _teCtx = unvar (\() -> Just ty) (_teCtx tcEnv)
           , _tePath = bodyPath
           }
          )
          (Bound.fromScope body)
      pure $ Syntax.TArr ty bodyTy
    App f x -> do
      let fPath = Path.snoc (_tePath tcEnv) Path.AppL
      let xPath = Path.snoc (_tePath tcEnv) Path.AppR
      fTy <- infer (tcEnv { _tePath = fPath }) f
      inTy <- freshTMeta (_teBoundTyVars tcEnv) KType
      outTy <- freshTMeta (_teBoundTyVars tcEnv) KType
      unifyType
        (KCEnvTerm
         { _keName = _teNameTy tcEnv
         , _keGlobalCtx = _teGlobalTyCtx tcEnv
         , _keCtx = _teTyCtx tcEnv
         , _keTmPath = fPath
         , _keTermTyPath = Path.empty
         })
        (TArr inTy outTy)
        fTy
      inTy' <- applySolutions inTy
      check (tcEnv { _tePath = xPath }) x inTy'
      outTy' <- applySolutions outTy
      applySolutions_Holes
      pure outTy'

checkDeclBody ::
  forall a m ty tm.
  (MonadState (TCState a) m, MonadError TypeError m, Eq ty) =>
  (tm -> Name) ->
  (ty -> Name) ->
  (Name -> Maybe (Type ty)) ->
  (tm -> Maybe (Type ty)) ->
  (Name -> Maybe Kind) ->
  (ty -> Maybe Kind) ->
  Seq (Name, Type ty, Kind) ->
  Path a (DeclBody ty tm) ->
  DeclBody ty tm ->
  m (DeclBody ty tm)
checkDeclBody name nameTy ctxG ctx tyCtxG tyCtx boundTyVars path d =
  case d of
    Syntax.Done ty tm -> do
      let tyPath = Path.snoc path Path.DBType
      checkKind
        (KCEnvType
        { _keName = nameTy
        , _keGlobalCtx = tyCtxG
        , _keCtx = tyCtx
        , _keTypeTyPath = tyPath
        }
        )
        ty
        KType
      addInfo tyPath $ TypeInfo KType
      check
        (TCEnv
        { _teName = name
        , _teNameTy = nameTy
        , _teGlobalCtx = ctxG
        , _teCtx = ctx
        , _teGlobalTyCtx = tyCtxG
        , _teTyCtx = tyCtx
        , _teBoundTyVars = boundTyVars
        , _tePath = Path.snoc path Path.DBTerm
        }
        )
        tm
        ty
      pure $ Syntax.Done ty tm
    Syntax.Forall n body -> do
      k <- KMeta <$> freshKMeta
      Syntax.Forall n <$>
        checkDeclBody
          name
          (unvar (\() -> n) nameTy)
          ((fmap.fmap) Bound.F . ctxG)
          ((fmap.fmap) Bound.F . ctx)
          tyCtxG
          (unvar (\() -> Just k) tyCtx)
          (fmap (\(a, b, c) -> (a, Bound.F <$> b, c)) boundTyVars Seq.|>
           (n, Syntax.TVar $ Bound.B (), k)
          )
          (Path.snoc path Path.DBForallBody)
          body

checkDecl ::
  forall a m.
  (MonadState (TCState a) m, MonadError TypeError m) =>
  (Name -> Maybe (Type Void)) ->
  (Name -> Maybe Kind) ->
  Path a Decl ->
  Decl ->
  m (Name, Decl)
checkDecl ctxG tyCtxG path (Decl name body) =
  (,) name . Decl name <$>
  checkDeclBody
    absurd
    absurd
    ctxG
    absurd
    tyCtxG
    absurd
    mempty
    (Path.snoc path Path.DBody)
    body

checkDecls ::
  forall a m.
  (MonadState (TCState a) m, MonadError TypeError m) =>
  (Name -> Maybe (Type Void)) ->
  (Name -> Maybe Kind) ->
  Path a Decls ->
  Decls ->
  m ()
checkDecls ctxG tyCtxG path (Decls ds) =
  ifoldr
    (\i d rest -> do
      (dname, d') <- checkDecl ctxG tyCtxG (Path.snoc path $ Path.Decl i) d
      modify $ \tc -> tc { _tcCheckedDecls = Map.insert dname d' $ _tcCheckedDecls tc }
      rest
    )
    (pure ())
    ds
