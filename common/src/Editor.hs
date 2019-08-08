{-# language GADTs, StandaloneDeriving #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language TemplateHaskell #-}
module Editor where

import Data.Dependent.Map (DMap)
-- import Data.Dependent.Sum (ShowTag(..))
import Data.GADT.Compare (geq, gcompare, GOrdering(..))
import Data.GADT.Compare.TH (deriveGEq, deriveGCompare)
import Data.GADT.Show.TH (deriveGShow)
import Data.Map (Map)

import qualified Data.Dependent.Map as DMap
import qualified Data.Map as Map

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

data Context
  = Context
  { _ctxParent :: Maybe SomeID
  , _ctxLocalScope :: Map Binding (ID Binding)
  } deriving (Eq, Ord, Show)

data NodeInfo a where
  BoundInfo ::
    Context ->
    String ->
    NodeInfo Bound

  BindingInfo ::
    Context ->
    String ->
    NodeInfo Binding

  VarInfo ::
    Context ->
    ID Bound ->
    NodeInfo Expr

  HoleInfo ::
    Context ->
    NodeInfo Expr

  AppInfo ::
    Context ->
    ID Expr ->
    ID Expr ->
    NodeInfo Expr

  LamInfo ::
    Context ->
    ID Binding ->
    ID Expr ->
    NodeInfo Expr
-- fuckn 8.4
instance Eq (NodeInfo a) where
  (==) a b =
    case geq a b of
      Nothing -> False
      Just{} -> True
instance Ord (NodeInfo a) where
  compare a b =
    case gcompare a b of
      GLT -> LT
      GEQ{} -> EQ
      GGT -> GT
{-
deriving instance Eq (NodeInfo a)
deriving instance Ord (NodeInfo a)
-}
deriving instance Show (NodeInfo a)

parent :: NodeInfo a -> Maybe SomeID
parent ni =
  case ni of
    BindingInfo c _ -> _ctxParent c
    BoundInfo c _ -> _ctxParent c
    HoleInfo c -> _ctxParent c
    VarInfo c _ -> _ctxParent c
    AppInfo c _ _ -> _ctxParent c
    LamInfo c _ _ -> _ctxParent c

deriveGEq ''NodeInfo
deriveGCompare ''NodeInfo
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
    DMap ID NodeInfo ->
    Context ->
    a ->
    (ID a, DMap ID NodeInfo)

instance Unbuild Bound where
  unbuild m ctx (Bound a) =
    let
      i' = (ID_Bound $ DMap.size m)
    in
      ( i'
      , DMap.insert i' (BoundInfo ctx a) m
      )

instance Unbuild Binding where
  unbuild m ctx (Binding a) =
    let
      i' = (ID_Binding $ DMap.size m)
    in
      (i', DMap.insert i' (BindingInfo ctx a) m)

instance Unbuild Expr where
  unbuild m ctx (Var a) =
    let
      (a', m') = unbuild m (ctx { _ctxParent = Just $ SomeID i'}) a
      i' = (ID_Expr $ DMap.size m')
    in
      (i', DMap.insert i' (VarInfo ctx a') m')
  unbuild m ctx Hole =
    let
      i' = (ID_Expr $ DMap.size m)
    in
      (i', DMap.insert i' (HoleInfo ctx) m)
  unbuild m ctx (App a b) =
    let
      (a', m') = unbuild m (ctx { _ctxParent = Just $ SomeID i'}) a
      (b', m'') = unbuild m' (ctx { _ctxParent = Just $ SomeID i'}) b
      i' = (ID_Expr $ DMap.size m'')
    in
      (i', DMap.insert i' (AppInfo ctx a' b') m'')
  unbuild m ctx (Lam a b) =
    let
      (a', m') = unbuild m (ctx { _ctxParent = Just $ SomeID i'}) a
      (b', m'') = unbuild m' (Context (Just $ SomeID i') (Map.insert a a' $ _ctxLocalScope ctx)) b
      i' = (ID_Expr $ DMap.size m'')
    in
      (i', DMap.insert i' (LamInfo ctx a' b') m'')

rebuild :: DMap ID NodeInfo -> ID a -> Maybe a
rebuild m i =
  DMap.lookup i m >>=
  \case
    BindingInfo _ a -> Just $ Binding a
    BoundInfo _ a -> Just $ Bound a
    HoleInfo _ -> Just Hole
    VarInfo _ val -> Var <$> rebuild m val
    AppInfo _ a b -> App <$> rebuild m a <*> rebuild m b
    LamInfo _ a b -> Lam <$> rebuild m a <*> rebuild m b

getBounds :: DMap ID NodeInfo -> ID Binding -> [ID Bound]
getBounds m i =
  DMap.foldrWithKey
    (\k v rest ->
       case v of
         BoundInfo ctx val ->
           case Map.lookup (Binding val) (_ctxLocalScope ctx) of
             -- this variable is not bound by local scope
             Nothing -> rest
             -- this variable is bound by local scope
             Just b ->
               if b == i
               -- this variable is bound by the one we're interested in
               then k : rest
               -- this variable is bound by another variable
               else rest
         _ -> rest)
    []
    m

getBinding :: DMap ID NodeInfo -> ID Bound -> Maybe (ID Binding)
getBinding m i =
  DMap.lookup i m >>=
  \case
    BoundInfo ctx val ->
      Map.lookup (Binding val) (_ctxLocalScope ctx)
