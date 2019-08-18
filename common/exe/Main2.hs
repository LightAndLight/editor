{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
module Main2 where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Control.Monad.Fix (MonadFix)
import Data.Dependent.Map (DMap)
import Data.Functor.Identity (Identity(..))
import Data.Map.Monoidal (MonoidalMap)
import Data.Monoid (Endo(..))
import Data.String (fromString)
import Data.Text (Text)
import GHCJS.DOM.KeyboardEvent (getKey)
import JSDOM.EventM (event, on)
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex
import Reflex.Dom

import qualified Data.Dependent.Map as DMap
import qualified Data.Map.Monoidal as MonoidalMap
import qualified GHCJS.DOM.GlobalEventHandlers as Event

import Editor
  ( Context(..), emptyContext, NodeInfo(..), ID(..)
  , SomeID(..), Expr(..), Binding(..)
  , unbuild
  , parent
  )

data Deco
  = Deco
  { _decoWarn :: Bool
  , _decoInfo :: Bool
  , _decoCursor :: Bool
  }

emptyDeco :: Deco
emptyDeco = Deco False False False

info :: Endo Deco
info = Endo $ \d -> d { _decoInfo = True }

uninfo :: Endo Deco
uninfo = Endo $ \d -> d { _decoInfo = False }

cursor :: Endo Deco
cursor = Endo $ \d -> d { _decoCursor = True }

uncursor :: Endo Deco
uncursor = Endo $ \d -> d { _decoCursor = False }

decoStyle :: Deco -> Text
decoStyle d = bg <> border
  where
    bg
      | _decoWarn d = "background-color: red;"
      | _decoInfo d = "background-color: gray;"
      | otherwise = mempty

    border
      | _decoCursor d = "border: 1px dotted black;"
      | otherwise = mempty

type LiveGraph t = DMap ID (NodeInfo (Dynamic t))
type Graph = DMap ID (NodeInfo Identity)

isLeaf :: Reflex t => Dynamic t (LiveGraph t) -> ID a -> Dynamic t Bool
isLeaf dGraph i = do
  ws <- dGraph
  pure $
    case DMap.lookup i ws of
      Nothing -> False
      Just node ->
        case node of
          BindingInfo{} -> True
          VarInfo{} -> True
          HoleInfo{} -> True
          AppInfo{} -> False
          LamInfo{} -> False

mkDynamicContext ::
  (Reflex t, Applicative m) =>
  Context Identity ->
  m (Context (Dynamic t))
mkDynamicContext (Context p (Identity sc)) =
  pure $ Context p (pure sc)

mkDynamicContent ::
  (Reflex t, Monad m) =>
  NodeInfo Identity a ->
  m (NodeInfo (Dynamic t) a)
mkDynamicContent node =
  case node of
    BindingInfo ctx (Identity val) -> do
      ctx' <- mkDynamicContext ctx
      pure $ BindingInfo ctx' (pure val)
    VarInfo ctx (Identity val) (Identity vars) -> do
      ctx' <- mkDynamicContext ctx
      pure $ VarInfo ctx' (pure val) (pure vars)
    HoleInfo ctx -> do
      ctx' <- mkDynamicContext ctx
      pure $ HoleInfo ctx'
    AppInfo ctx c1 c2 (Identity vars) -> do
      ctx' <- mkDynamicContext ctx
      pure $ AppInfo ctx' c1 c2 (pure vars)
    LamInfo ctx c1 c2 (Identity vars) -> do
      ctx' <- mkDynamicContext ctx
      pure $ LamInfo ctx' c1 c2 (pure vars)

mkDynamicNode ::
  forall t m a.
  ( DomBuilder t m, MonadHold t m, MonadFix m, PostBuild t m
  , EventWriter t (MonoidalMap SomeID (Endo Deco)) m
  ) =>
  ID a ->
  NodeInfo Identity a ->
  m (NodeInfo (Dynamic t) a)
mkDynamicNode _ node = mkDynamicContent node

mkLiveGraph ::
  ( DomBuilder t m, MonadHold t m, MonadFix m, PostBuild t m
  , EventWriter t (MonoidalMap SomeID (Endo Deco)) m
  ) =>
  Event t (Endo (LiveGraph t)) ->
  Graph ->
  m (Dynamic t (LiveGraph t))
mkLiveGraph eGraphUpdate g = do
  g' <- DMap.traverseWithKey mkDynamicNode g
  foldDyn (($) . appEndo) g' eGraphUpdate

renderID ::
  forall t m a.
  ( DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m
  , EventWriter t (MonoidalMap SomeID (Endo Deco)) m
  ) =>
  Dynamic t (LiveGraph t) ->
  Event t (MonoidalMap SomeID (Endo Deco)) ->
  ID a ->
  m ()
renderID dGraph eDecos i = do
  let bIsLeaf :: Behavior t Bool = current $ isLeaf dGraph i
  dStyle <-
    foldDyn (($) . appEndo) emptyDeco $
    fmapMaybe (MonoidalMap.lookup $ SomeID i) eDecos
  let
    dAttrs =
      (\deco ->
         "id" =: fromString (show i) <>
         "style" =: decoStyle deco) <$>
      dStyle
  (theSpan, _) <-
    elDynAttr' "span" dAttrs .
    dyn_ $ do
      ws <- dGraph
      case DMap.lookup i ws of
        Nothing -> pure $ text "NOT FOUND"
        Just node -> pure $ renderNode dGraph eDecos node
  let eEnter :: Event t () = domEvent Mouseenter theSpan
  let eLeave :: Event t () = domEvent Mouseleave theSpan
  tellEvent $ MonoidalMap.singleton (SomeID i) info <$ gate bIsLeaf eEnter
  tellEvent $ MonoidalMap.singleton (SomeID i) uninfo <$ gate bIsLeaf eLeave

renderNode ::
  ( DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m
  , EventWriter t (MonoidalMap SomeID (Endo Deco)) m
  ) =>
  Dynamic t (LiveGraph t) ->
  Event t (MonoidalMap SomeID (Endo Deco)) ->
  NodeInfo (Dynamic t) a ->
  m ()
renderNode dGraph eDecos node = do
  case node of
    BindingInfo _ dVal ->
      dynText $ fromString <$> dVal
    VarInfo _ dVal _ ->
      dynText $ fromString <$> dVal
    HoleInfo _ -> text "_"
    AppInfo _ c1 c2 _ -> do
      renderID dGraph eDecos c1
      text " "
      renderID dGraph eDecos c2
    LamInfo _ c1 c2 _ -> do
      text "\\"
      renderID dGraph eDecos c1
      text " -> "
      renderID dGraph eDecos c2

deleteNode :: SomeID -> Endo (LiveGraph t)
deleteNode (SomeID i) =
  Endo $
  DMap.alter
    (fmap $
     \case
       n@BindingInfo{} -> n
       n@HoleInfo{} -> n
       VarInfo ctx _ _ -> HoleInfo ctx
       LamInfo ctx _ _ _ -> HoleInfo ctx
       AppInfo ctx _ _ _ -> HoleInfo ctx)
    i

appNode :: Reflex t => SomeID -> Endo (LiveGraph t)
appNode (SomeID i) =
  Endo $ \ws ->
  case DMap.lookup i ws of
    Nothing -> ws
    Just node ->
      case node of
        HoleInfo ctx ->
          let
            sz = DMap.size ws
            i1 = ID_Expr sz
            i2 = ID_Expr $ sz+1
          in
            DMap.insert i (AppInfo ctx i1 i2 (pure mempty)) $
            DMap.insert i1 (HoleInfo $ ctx { _ctxParent = Just (SomeID i) }) $
            DMap.insert i2 (HoleInfo $ ctx { _ctxParent = Just (SomeID i) }) $
            ws
        BindingInfo{} -> ws
        VarInfo{} -> ws
        LamInfo{} -> ws
        AppInfo{} -> ws

headWidget :: DomBuilder t m => m ()
headWidget = do
  el "title" $ text "Testing"
  el "style" $ text "html { font-family: monospace; }"

documentKey ::
  ( Reflex t, HasDocument m, TriggerEvent t m, MonadJSM m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  Text -> m (Event t ())
documentKey k' = do
  document <- askDocument
  fmapMaybe (\k -> guard $ k == k') <$>
    wrapDomEvent document (`on` Event.keyDown) (getKey =<< event)

parentNode :: LiveGraph t -> SomeID -> Maybe SomeID
parentNode graph (SomeID i) = do
  node <- DMap.lookup i graph
  parent node

childNode :: LiveGraph t -> SomeID -> Maybe SomeID
childNode graph (SomeID i) = do
  node <- DMap.lookup i graph
  case node of
    HoleInfo{} -> Nothing
    BindingInfo{} -> Nothing
    VarInfo{} -> Nothing
    LamInfo _ i' _ _ -> Just $ SomeID i'
    AppInfo _ i' _ _ -> Just $ SomeID i'

nextSibling :: LiveGraph t -> SomeID -> Maybe SomeID
nextSibling graph (SomeID i) = do
  node <- DMap.lookup i graph
  SomeID p <- parent node
  node' <- DMap.lookup p graph
  case node' of
    HoleInfo{} -> Nothing
    BindingInfo{} -> Nothing
    VarInfo{} -> Nothing
    LamInfo _ a b _
      | SomeID a == SomeID i -> Just $ SomeID b
      | SomeID b == SomeID i -> Nothing
      | otherwise -> undefined
    AppInfo _ a b _
      | SomeID a == SomeID i -> Just $ SomeID b
      | SomeID b == SomeID i -> Nothing
      | otherwise -> undefined

prevSibling :: LiveGraph t -> SomeID -> Maybe SomeID
prevSibling graph (SomeID i) = do
  node <- DMap.lookup i graph
  SomeID p <- parent node
  node' <- DMap.lookup p graph
  case node' of
    HoleInfo{} -> Nothing
    BindingInfo{} -> Nothing
    VarInfo{} -> Nothing
    LamInfo _ a b _
      | SomeID a == SomeID i -> Nothing
      | SomeID b == SomeID i -> Just $ SomeID a
      | otherwise -> undefined
    AppInfo _ a b _
      | SomeID a == SomeID i -> Nothing
      | SomeID b == SomeID i -> Just $ SomeID a
      | otherwise -> undefined

nextLeaf :: forall t. LiveGraph t -> SomeID -> Maybe SomeID
nextLeaf graph = starting
  where
    starting :: SomeID -> Maybe SomeID
    starting (SomeID i) = do
      node <- DMap.lookup i graph
      let
        leafOrBranch =
          case node of
            HoleInfo ctx -> Left ctx
            BindingInfo ctx _ -> Left ctx
            VarInfo ctx _ _ -> Left ctx
            LamInfo _ i' _ _ -> Right $ SomeID i'
            AppInfo _ i' _ _ -> Right $ SomeID i'
      case leafOrBranch of
        Left ctx -> uppity (SomeID i) ctx
        Right i' -> downity i'

    downity :: SomeID -> Maybe SomeID
    downity (SomeID i) = do
      node <- DMap.lookup i graph
      case node of
        HoleInfo{} -> Just $ SomeID i
        BindingInfo{} -> Just $ SomeID i
        VarInfo{} -> Just $ SomeID i
        LamInfo _ i' _ _ -> downity $ SomeID i'
        AppInfo _ i' _ _ -> downity $ SomeID i'

    uppity :: SomeID -> Context (Dynamic t) -> Maybe SomeID
    uppity i ctx = do
      SomeID p <- _ctxParent ctx
      node' <- DMap.lookup p graph
      case node' of
        HoleInfo{} -> undefined
        BindingInfo{} -> undefined
        VarInfo{} -> undefined
        LamInfo ctx' a b _
          | SomeID a == i -> downity $ SomeID b
          | SomeID b == i -> uppity (SomeID p) ctx'
          | otherwise -> undefined
        AppInfo ctx' a b _
          | SomeID a == i -> downity $ SomeID b
          | SomeID b == i -> uppity (SomeID p) ctx'
          | otherwise -> undefined

prevLeaf :: forall t. LiveGraph t -> SomeID -> Maybe SomeID
prevLeaf graph = starting
  where
    starting :: SomeID -> Maybe SomeID
    starting (SomeID i) = do
      node <- DMap.lookup i graph
      let
        leafOrBranch =
          case node of
            HoleInfo ctx -> Left ctx
            BindingInfo ctx _ -> Left ctx
            VarInfo ctx _ _ -> Left ctx
            LamInfo _ _ i' _ -> Right $ SomeID i'
            AppInfo _ _ i' _ -> Right $ SomeID i'
      case leafOrBranch of
        Left ctx -> uppity (SomeID i) ctx
        Right i' -> downity i'

    downity :: SomeID -> Maybe SomeID
    downity (SomeID i) = do
      node <- DMap.lookup i graph
      case node of
        HoleInfo{} -> Just $ SomeID i
        BindingInfo{} -> Just $ SomeID i
        VarInfo{} -> Just $ SomeID i
        LamInfo _ _ i' _ -> downity $ SomeID i'
        AppInfo _ _ i' _ -> downity $ SomeID i'

    uppity :: SomeID -> Context (Dynamic t) -> Maybe SomeID
    uppity i ctx = do
      SomeID p <- _ctxParent ctx
      node' <- DMap.lookup p graph
      case node' of
        HoleInfo{} -> undefined
        BindingInfo{} -> undefined
        VarInfo{} -> undefined
        LamInfo ctx' a b _
          | SomeID b == i -> downity $ SomeID a
          | SomeID a == i -> uppity (SomeID p) ctx'
          | otherwise -> undefined
        AppInfo ctx' a b _
          | SomeID b == i -> downity $ SomeID a
          | SomeID a == i -> uppity (SomeID p) ctx'
          | otherwise -> undefined

main :: IO ()
main =
  mainWidgetWithHead headWidget $ do
    let e = Lam (Binding "f") $ Lam (Binding "x") $ App (App (Var "f") (Var "x")) (Var "x")
    let (i, g, _) = unbuild mempty emptyContext e
    eKeyD <- documentKey "d"
    eKeyA <- documentKey "a"
    eKeyHH <- documentKey "H"
    eKeyH <- documentKey "h"
    eKeyJ <- documentKey "j"
    eKeyK <- documentKey "k"
    eKeyLL <- documentKey "L"
    eKeyL <- documentKey "l"
    ePostBuild <- getPostBuild
    rec
      let
        eDecos = eDecos_ <> eCursorDeco
        eDelete = deleteNode <$> current dCursor <@ eKeyD
        eApp = appNode <$> current dCursor <@ eKeyA
      (dGraph, eDecos_) <-
        runEventWriterT $
          mkLiveGraph (eApp <> eDelete) g <*
          renderID dGraph eDecos i
      dCursor <-
        holdDyn (SomeID i) . fmapMaybe id $
        mergeWith (<|>)
        [ nextLeaf <$> current dGraph <*> current dCursor <@ eKeyL
        , prevLeaf <$> current dGraph <*> current dCursor <@ eKeyH
        , parentNode <$> current dGraph <*> current dCursor <@ eKeyK
        , childNode <$> current dGraph <*> current dCursor <@ eKeyJ
        , nextSibling <$> current dGraph <*> current dCursor <@ eKeyLL
        , prevSibling <$> current dGraph <*> current dCursor <@ eKeyHH
        ]
      let
        eCursorDeco =
          (MonoidalMap.singleton (SomeID i) cursor <$ ePostBuild) <>
          attachWithMaybe
            (\old new ->
              if old /= new
              then Just $ MonoidalMap.fromList [(old, uncursor), (new, cursor)]
              else Nothing)
            (current dCursor)
            (updated dCursor)
    pure ()