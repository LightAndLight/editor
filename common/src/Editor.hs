{-# language GADTs, StandaloneDeriving #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language TemplateHaskell #-}
module Editor where

import Data.Dependent.Map (DMap)
import Data.Functor.Identity (Identity(..))
-- import Data.Dependent.Sum (ShowTag(..))
import Data.GADT.Compare (GEq(..), GCompare(..), GOrdering(..))
import Data.GADT.Compare.TH (deriveGEq, deriveGCompare)
import Data.GADT.Show.TH (deriveGShow)
import Data.Map (Map)
import Data.Set (Set, (\\))

import qualified Data.Dependent.Map as DMap
import qualified Data.Map as Map
import qualified Data.Set as Set

data ID a where
  ID_Expr :: Int -> ID Expr
  ID_Bound :: Int -> ID Bound
  ID_Binding :: Int -> ID Binding
-- fuckn 8.4
instance Eq (ID a) where
  (==) a b =
    case geq a b of
      Nothing -> False
      Just{} -> True
instance Ord (ID a) where
  compare a b =
    case gcompare a b of
      GLT -> LT
      GEQ{} -> EQ
      GGT -> GT
{-
deriving instance Eq (ID a)
deriving instance Ord (ID a)
-}
deriving instance Show (ID a)

data SomeID where
  SomeID :: ID a -> SomeID
instance Eq SomeID where
  (==) (SomeID a) (SomeID b) =
    case geq a b of
      Nothing -> False
      Just{} -> True
instance Ord SomeID where
  compare (SomeID a) (SomeID b) =
    case gcompare a b of
      GLT -> LT
      GEQ{} -> EQ
      GGT -> GT
deriving instance Show SomeID

data Bound = Bound { unBound :: String }
  deriving (Eq, Ord, Show)

data Binding = Binding { unBinding :: String }
  deriving (Eq, Ord, Show)

data Expr
  = Var Bound
  | Hole
  | App Expr Expr
  | Lam Binding Expr
  deriving (Eq, Show)

data Context f
  = Context
  { _ctxParent :: Maybe SomeID
  , _ctxLocalScope :: f (Map Binding (ID Binding))
  }

data NodeInfo f a where
  BoundInfo ::
    Context f ->
    f String ->
    NodeInfo f Bound

  BindingInfo ::
    Context f ->
    f String ->
    NodeInfo f Binding

  VarInfo ::
    Context f ->
    ID Bound ->
    f (Set (ID Bound)) ->
    NodeInfo f Expr

  HoleInfo ::
    Context f ->
    NodeInfo f Expr

  AppInfo ::
    Context f ->
    ID Expr ->
    ID Expr ->
    f (Set (ID Bound)) ->
    NodeInfo f Expr

  LamInfo ::
    Context f ->
    ID Binding ->
    ID Expr ->
    f (Set (ID Bound)) ->
    NodeInfo f Expr
{-
deriving instance Eq (NodeInfo a)
deriving instance Ord (NodeInfo a)
-}
-- deriving instance Show1 f => Show (NodeInfo f a)

context :: NodeInfo f a -> Context f
context ni =
  case ni of
    BindingInfo c _ -> c
    BoundInfo c _ -> c
    HoleInfo c -> c
    VarInfo c _ _ -> c
    AppInfo c _ _ _ -> c
    LamInfo c _ _ _ -> c

freeVars :: Applicative f => NodeInfo f a -> f (Set (ID Bound))
freeVars ni =
  case ni of
    BindingInfo{} -> pure mempty
    BoundInfo{} -> pure mempty
    HoleInfo{} -> pure mempty
    VarInfo _ _ a -> a
    AppInfo _ _ _ a -> a
    LamInfo _ _ _ a -> a

parent :: NodeInfo f a -> Maybe SomeID
parent = _ctxParent . context
deriveGEq ''ID
deriveGCompare ''ID
deriveGShow ''ID

{-
instance ShowTag ID NodeInfo where
  showTaggedPrec ID_Expr{} = showsPrec
  showTaggedPrec ID_Bound{} = showsPrec
  showTaggedPrec ID_Binding{} = showsPrec
-}

class Unbuild a where
  unbuild ::
    Applicative f =>
    DMap ID (NodeInfo f) ->
    Context f ->
    a ->
    (ID a, DMap ID (NodeInfo f), f (Set (ID Bound)))

instance Unbuild Bound where
  unbuild m ctx (Bound a) =
    let
      i' = (ID_Bound $ DMap.size m)
    in
      ( i'
      , DMap.insert i' (BoundInfo ctx $ pure a) m
      , pure mempty
      )

instance Unbuild Binding where
  unbuild m ctx (Binding a) =
    let
      i' = (ID_Binding $ DMap.size m)
    in
      (i', DMap.insert i' (BindingInfo ctx $ pure a) m, pure mempty)

instance Unbuild Expr where
  unbuild m ctx (Var a) =
    let
      (a', m', _) = unbuild m (ctx { _ctxParent = Just $ SomeID i'}) a
      i' = (ID_Expr $ DMap.size m')
      fvs = pure $ Set.singleton a'
    in
      ( i'
      , DMap.insert i' (VarInfo ctx a' fvs) m'
      , fvs
      )
  unbuild m ctx Hole =
    let
      i' = (ID_Expr $ DMap.size m)
    in
      (i', DMap.insert i' (HoleInfo ctx) m, pure mempty)
  unbuild m ctx (App a b) =
    let
      (a', m', fvs') = unbuild m (ctx { _ctxParent = Just $ SomeID i'}) a
      (b', m'', fvs'') = unbuild m' (ctx { _ctxParent = Just $ SomeID i'}) b
      i' = (ID_Expr $ DMap.size m'')
      fvs''' = (<>) <$> fvs' <*> fvs''
    in
      (i', DMap.insert i' (AppInfo ctx a' b' fvs''') m'', fvs''')
  unbuild m ctx (Lam a b) =
    let
      (a', m', _) = unbuild m (ctx { _ctxParent = Just $ SomeID i'}) a
      (b', m'', fvs') = unbuild m' (Context (Just $ SomeID i') (Map.insert a a' <$> _ctxLocalScope ctx)) b
      i' = (ID_Expr $ DMap.size m'')
      fvs'' = (\bbs ffs -> ffs \\ Set.fromList bbs) <$> getBounds m'' a' <*> fvs'
    in
      (i', DMap.insert i' (LamInfo ctx a' b' fvs'') m'', fvs'')

rebuild :: DMap ID (NodeInfo Identity) -> ID a -> Maybe a
rebuild m i =
  DMap.lookup i m >>=
  \case
    BindingInfo _ a -> Just $ Binding $ runIdentity a
    BoundInfo _ a -> Just $ Bound $ runIdentity a
    HoleInfo _ -> Just Hole
    VarInfo _ val _ -> Var <$> rebuild m val
    AppInfo _ a b _ -> App <$> rebuild m a <*> rebuild m b
    LamInfo _ a b _ -> Lam <$> rebuild m a <*> rebuild m b

getBounds :: Applicative f => DMap ID (NodeInfo f) -> ID Binding -> f [ID Bound]
getBounds m i =
  DMap.foldrWithKey
    (\k v rest ->
       case v of
         BoundInfo ctx val ->
           (\vv cc rr -> case Map.lookup (Binding vv) cc of
             -- this variable is not bound by local scope
             Nothing -> rr
             -- this variable is bound by local scope
             Just b ->
               if b == i
               -- this variable is bound by the one we're interested in
               then k : rr
               -- this variable is bound by another variable
               else rr) <$>
           val <*>
           _ctxLocalScope ctx <*>
           rest
         _ -> rest)
    (pure [])
    m

getBinding ::
  DMap ID (NodeInfo Identity) ->
  ID Bound ->
  Maybe (ID Binding)
getBinding m i =
  DMap.lookup i m >>=
  \case
    BoundInfo ctx val ->
      Map.lookup
        (Binding $ runIdentity val)
        (runIdentity $ _ctxLocalScope ctx)
