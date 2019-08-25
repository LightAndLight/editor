{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
{-# language UndecidableInstances #-}
{-# language PolyKinds, KindSignatures #-}
module Main where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Control.Monad.Fix (MonadFix)
import Data.Dependent.Map (DMap, GCompare)
import Data.Dependent.Sum (DSum(..))
import Data.Functor.Identity (Identity(..))
import Data.GADT.Compare.TH (deriveGEq, deriveGCompare)
import Data.Map (Map)
import Data.Map.Monoidal (MonoidalMap(..))
import Data.Maybe (fromMaybe)
import Data.Monoid (Endo(..))
import Data.String (fromString)
import Data.Text (Text)
import GHCJS.DOM.KeyboardEvent (getKey)
import GHCJS.DOM.EventM (event, on, mouseClientXY, preventDefault)
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex
import Reflex.Dom hiding (preventDefault)
import Data.Functor.Misc

import qualified Data.Dependent.Map as DMap
import qualified Data.Map as Map
import qualified Data.Map.Monoidal as MonoidalMap
import qualified Data.Map.Merge.Lazy as Map
import qualified Data.Text as Text
import qualified GHCJS.DOM.GlobalEventHandlers as Event
import qualified GHCJS.DOM.HTMLElement as Element (focus)
import qualified GHCJS.DOM.HTMLInputElement as InputElement (select)

import Editor
  ( Context(..), emptyContext, NodeInfo(..), ID(..)
  , SomeID(..), Expr(..), Binding(..)
  , unbuild
  , parent
  )
import Data.GADT.Prism

lookupIncremental ::
  (GCompare k, Reflex t, MonadHold t m) =>
  Incremental t (PatchDMap k v) ->
  k a ->
  m (Dynamic t (Maybe (Dynamic t (v a))))
lookupIncremental iMap key = do
  buildDynamic
    (sample (currentIncremental iMap) >>=
     maybe (pure Nothing) dynPart . DMap.lookup key)
    (push
       (\(PatchDMap patch) ->
          case DMap.lookup key patch of
            Nothing -> pure Nothing
            Just (ComposeMaybe mv) -> do
              old <- sample $ currentIncremental iMap
              case mv of
                Just v ->
                  if DMap.member key old
                  then pure Nothing
                  else Just <$> dynPart v
                Nothing ->
                  pure $
                  if DMap.member key old
                  then Just Nothing
                  else Nothing)
       (updatedIncremental iMap))
  where
    dynPart v =
      Just <$> do
        eUpdate <-
          takeWhileJustE getComposeMaybe $
          fmapMaybe (DMap.lookup key . unPatchDMap) (updatedIncremental iMap)
        holdDyn v eUpdate

contextMenu ::
  (TriggerEvent t m, MonadJSM m) =>
  Element er GhcjsDomSpace t ->
  m (Event t (Int, Int))
contextMenu e =
  wrapDomEvent (_element_raw e) (elementOnEventName Contextmenu) $ do
    preventDefault
    mouseClientXY

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

type UpdateLiveGraph t = PatchDMap ID (NodeInfo (Dynamic t))
type LiveGraph t = DMap ID (NodeInfo (Dynamic t))
type Graph = DMap ID (NodeInfo Identity)

isLeaf :: NodeInfo f a -> Bool
isLeaf node =
  case node of
    BindingInfo{} -> True
    VarInfo{} -> True
    HoleInfo{} -> True
    AppInfo{} -> False
    LamInfo{} -> False

mkDynamicContext ::
  (Reflex t, MonadHold t m) =>
  Context Identity ->
  m (Context (Dynamic t))
mkDynamicContext (Context p (Identity sc)) = do
  pure $ Context p (pure sc)

data Action a where
  EditBinding :: Action Binding
  CommitBinding :: String -> Action Binding
deriving instance Show (Action a)

isEditStart :: Action a -> Bool
isEditStart a =
  case a of
    EditBinding -> True
    CommitBinding{} -> False

isEditStop :: Action a -> Bool
isEditStop a =
  case a of
    EditBinding -> False
    CommitBinding{} -> True

mkDynamicNode ::
  (Reflex t, MonadHold t m) =>
  Incremental t (UpdateLiveGraph t) ->
  Event t (DMap ID Action) ->
  ID a ->
  NodeInfo Identity a ->
  m (NodeInfo (Dynamic t) a)
mkDynamicNode _ eActions i node =
  let
    eAction = fmapMaybe (DMap.lookup i) eActions
  in
  case node of
    BindingInfo ctx (Identity val) -> do
      ctx' <- mkDynamicContext ctx
      dVal <-
        holdDyn val $
        fmapMaybe
          (\case; CommitBinding val' -> Just val'; _ -> Nothing)
          eAction
      pure $ BindingInfo ctx' dVal
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

mkLiveGraph ::
  ( DomBuilder t m, MonadHold t m, MonadFix m, PostBuild t m
  , EventWriter t (DMap k Identity) m
  ) =>
  Event t (DMap ID Action) ->
  Event t (UpdateLiveGraph t) ->
  Graph ->
  m (Incremental t (UpdateLiveGraph t))
mkLiveGraph eActions eGraphUpdate g = do
  rec
    g' <- DMap.traverseWithKey (mkDynamicNode g'' eActions) g
    g'' <- holdIncremental g' eGraphUpdate
  pure g''

data NodeSort
  = BindingSort
  | AppSort
  | LamSort
  | VarSort
  | HoleSort

nodeSort ::
  NodeInfo f a ->
  NodeSort
nodeSort node =
  case node of
    BindingInfo{} -> BindingSort
    VarInfo{} -> VarSort
    HoleInfo{} -> HoleSort
    AppInfo{} -> AppSort
    LamInfo{} -> LamSort

class GCompare k => ActionsKey k where
  actionsK :: GPrism1 (DMap ID Action) k ()

class GCompare k => DecosKey k where
  decosK :: GPrism1 (MonoidalMap SomeID (Endo Deco)) k ()

class GCompare k => ContextMenuKey k where
  contextMenuK :: GPrism1 (SomeID, Int, Int) k ()

data AppEventK a where
  ActionsK :: AppEventK (DMap ID Action)
  DecosK :: AppEventK (MonoidalMap SomeID (Endo Deco))
  ContextMenuK :: AppEventK (SomeID, Int, Int)
deriveGEq ''AppEventK
deriveGCompare ''AppEventK

instance ActionsKey AppEventK where
  actionsK = GPrism1 (\() -> ActionsK) (\r1 r2 -> \case; ActionsK -> r1 (); _ -> r2)
instance DecosKey AppEventK where
  decosK = GPrism1 (\() -> DecosK) (\r1 r2 -> \case; DecosK -> r1 (); _ -> r2)
instance ContextMenuKey AppEventK where
  contextMenuK = GPrism1 (\() -> ContextMenuK) (\r1 r2 -> \case; ContextMenuK -> r1 (); _ -> r2)

tellActions ::
  (Reflex t, ActionsKey k, EventWriter t (DMap k Identity) m) =>
  Event t (DMap ID Action) ->
  m ()
tellActions = tellEvent . fmap (DMap.singleton (greview1 actionsK ()) . pure)

tellDecos ::
  (Reflex t, DecosKey k, EventWriter t (DMap k Identity) m) =>
  Event t (MonoidalMap SomeID (Endo Deco)) ->
  m ()
tellDecos = tellEvent . fmap (DMap.singleton (greview1 decosK ()) . pure)

tellContextMenu ::
  (Reflex t, ContextMenuKey k, EventWriter t (DMap k Identity) m) =>
  Event t (SomeID, Int, Int) ->
  m ()
tellContextMenu = tellEvent . fmap (DMap.singleton (greview1 contextMenuK ()) . pure)

renderID ::
  forall t k m a.
  ( DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m
  , DomBuilderSpace m ~ GhcjsDomSpace, MonadJSM m
  , PerformEvent t m, MonadJSM (Performable m), TriggerEvent t m
  , ActionsKey k, DecosKey k, ContextMenuKey k, EventWriter t (DMap k Identity) m
  ) =>
  Incremental t (UpdateLiveGraph t) ->
  Dynamic t (Map SomeID Deco) ->
  Event t (DMap ID Action) ->
  ID a ->
  m (Dynamic t (Maybe NodeSort))
renderID dGraph dDecos eActions i = do
  dm_node <- lookupIncremental dGraph i
  bIsLeaf <-
    fmap current . holdUniqDyn $
    dm_node >>= maybe (pure False) (fmap isLeaf)
  let dStyle = maybe mempty decoStyle . Map.lookup (SomeID i) <$> dDecos
  let
    dAttrs =
      (\deco ->
         "id" =: fromString (show i) <>
         "style" =: deco) <$>
      dStyle
  (theSpan, _) <-
    elDynAttr' "span" dAttrs . dyn_ $
    maybe
      (text "NOT FOUND")
      (dyn_ . fmap (renderNode dGraph dDecos eActions i)) <$>
    dm_node
  eContextMenu <- contextMenu theSpan
  tellContextMenu $ (\(x, y) -> (SomeID i, x, y)) <$> eContextMenu
  let eEnter :: Event t () = domEvent Mouseenter theSpan
  let eLeave :: Event t () = domEvent Mouseleave theSpan
  tellDecos $ MonoidalMap.singleton (SomeID i) info <$ gate bIsLeaf eEnter
  tellDecos $ MonoidalMap.singleton (SomeID i) uninfo <$ gate bIsLeaf eLeave
  pure $ dm_node >>= maybe (pure Nothing) (fmap (Just . nodeSort))

renderNode ::
  ( DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m
  , DomBuilderSpace m ~ GhcjsDomSpace, MonadJSM m
  , PerformEvent t m, MonadJSM (Performable m), TriggerEvent t m
  , ActionsKey k, DecosKey k, ContextMenuKey k, EventWriter t (DMap k Identity) m
  ) =>
  Incremental t (UpdateLiveGraph t) ->
  Dynamic t (Map SomeID Deco) ->
  Event t (DMap ID Action) ->
  ID a ->
  NodeInfo (Dynamic t) a ->
  m ()
renderNode dGraph dDecos eActions i node = do
  let eAction = fmapMaybe (DMap.lookup i) eActions
  case node of
    BindingInfo _ dVal -> do
      deCommit <-
        widgetHold txt $
        attachWithMaybe
          (\val ->
            \case
              EditBinding ->
                Just $ do
                  ti <-
                    textInput $
                    TextInputConfig
                    { _textInputConfig_inputType = "text"
                    , _textInputConfig_initialValue = fromString val
                    , _textInputConfig_setValue = never
                    , _textInputConfig_attributes = mempty
                    }
                  ePostBuild <- delay 0.05 =<< getPostBuild
                  performEvent_ $
                    (do
                       Element.focus $ _inputElement_raw $ _textInput_builderElement ti
                       InputElement.select $ _inputElement_raw $ _textInput_builderElement ti) <$
                    ePostBuild
                  pure $ current (value ti) <@ keypress Enter ti
              CommitBinding{} ->
                Just txt)
          (current dVal)
          eAction
      let eCommit = switchDyn deCommit
      tellActions $ DMap.singleton i . CommitBinding . Text.unpack <$> eCommit
      where
        txt = never <$ dynText (fromString <$> dVal)
    VarInfo _ dVal _ ->
      dynText $ fromString <$> dVal
    HoleInfo _ -> text "_"
    AppInfo _ c1 c2 _ -> do
      rec
        dyn_ $ maybe (pure ()) (brckt1 "(") <$> dSort1
        dSort1 <- renderID dGraph dDecos eActions c1
        dyn_ $ maybe (pure ()) (brckt1 ")") <$> dSort1
      text " "
      rec
        dyn_ $ maybe (pure ()) (brckt2 "(") <$> dSort2
        dSort2 <- renderID dGraph dDecos eActions c2
        dyn_ $ maybe (pure ()) (brckt2 ")") <$> dSort2
      pure ()
      where
        brckt1 str nd =
          case nd of
            LamSort{} -> text str
            _ -> pure ()

        brckt2 str nd =
          case nd of
            LamSort{} -> text str
            AppSort{} -> text str
            _ -> pure ()
    LamInfo _ c1 c2 _ -> do
      text "\\"
      _ <- renderID dGraph dDecos eActions c1
      text " -> "
      _ <- renderID dGraph dDecos eActions c2
      pure ()

deleteNode :: SomeID -> LiveGraph t -> UpdateLiveGraph t
deleteNode (SomeID i) graph =
  case DMap.lookup i graph of
    Nothing -> mempty
    Just node ->
      PatchDMap . DMap.singleton i . ComposeMaybe . Just $
      case node of
         n@BindingInfo{} -> n
         n@HoleInfo{} -> n
         VarInfo ctx _ _ -> HoleInfo ctx
         LamInfo ctx _ _ _ -> HoleInfo ctx
         AppInfo ctx _ _ _ -> HoleInfo ctx

appNode :: Reflex t => SomeID -> LiveGraph t -> (UpdateLiveGraph t, Maybe SomeID)
appNode (SomeID i) graph =
  case DMap.lookup i graph of
    Just (HoleInfo ctx) ->
      let
        sz = DMap.size graph
        i1 = ID_Expr sz
        i2 = ID_Expr $ sz+1
      in
        ( PatchDMap . DMap.fromList $
          [ i :=> ComposeMaybe (Just $ AppInfo ctx i1 i2 $ pure mempty)
          , i1 :=> ComposeMaybe (Just $ HoleInfo $ ctx { _ctxParent = Just (SomeID i) })
          , i2 :=> ComposeMaybe (Just $ HoleInfo $ ctx { _ctxParent = Just (SomeID i) })
          ]
        , Just $ SomeID i1
        )
    _ -> (mempty, Nothing)

lamNode :: Reflex t => SomeID -> LiveGraph t -> (UpdateLiveGraph t, Maybe SomeID)
lamNode (SomeID i) graph =
  case DMap.lookup i graph of
    Just (HoleInfo ctx) ->
      let
        sz = DMap.size graph
        i1 = ID_Binding sz
        i2 = ID_Expr $ sz+1
      in
        ( PatchDMap . DMap.fromList $
          [ i :=>
              ComposeMaybe (Just $ LamInfo ctx i1 i2 (pure mempty))
          , i1 :=>
              ComposeMaybe (Just $ BindingInfo (ctx { _ctxParent = Just (SomeID i) }) (pure "x"))
          , i2 :=>
              ComposeMaybe (Just $ HoleInfo $ ctx { _ctxParent = Just (SomeID i) })
          ]
        , Just $ SomeID i1
        )
    _ -> (mempty, Nothing)

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

documentClick ::
  ( Reflex t, HasDocument m, TriggerEvent t m, MonadJSM m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  m (Event t ())
documentClick = do
  document <- askDocument
  wrapDomEvent document (`on` Event.click) (pure ())

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

editBinding :: forall t. LiveGraph t -> SomeID -> DMap ID Action
editBinding graph (SomeID i) =
  fromMaybe mempty $ do
    node <- DMap.lookup i graph
    case node of
      BindingInfo{} -> pure $ DMap.singleton i EditBinding
      _ -> Nothing

data MenuItems

menuContent ::
  (MonadHold t m, MonadFix m, DomBuilder t m, PostBuild t m) =>
  [MenuItems] ->
  m ()
menuContent _ = do
  rec
    let eEnter = domEvent Mouseenter theSpan
    let eExit = domEvent Mouseleave theSpan
    dStyle <- holdDyn "" (leftmost ["background-color: gray" <$ eEnter, "" <$ eExit])
    (theSpan, res) <- elDynAttr' "span" (("style" =:) <$> dStyle) $ text "No Items"
  pure res

mkContextMenu ::
  (MonadHold t m, MonadFix m, DomBuilder t m, PostBuild t m) =>
  Event t (SomeID, Int, Int) ->
  Event t () ->
  m ()
mkContextMenu eMenu eMenuClose = do
  dMenuContent <- holdDyn [] $ (\(ii, _, _) -> const [] ii) <$> eMenu
  dMenuDisplay <-
    holdDyn "display: none;" $
    leftmost ["" <$ eMenu, "display: none;" <$ eMenuClose]
  dMenuPosition <-
    holdDyn "" $
    (\(_, x, y) ->
        "left: " <> fromString (show x) <> "px;" <>
        "top: " <> fromString (show y) <> "px;") <$>
    eMenu
  let
    mkStyle d =
      (=:) "style" $
      "border: 1px solid black;" <>
      "background-color: white;" <>
      "position: absolute;" <>
      d
  elDynAttr "div" (mkStyle <$> (dMenuDisplay <> dMenuPosition)) $
    dyn_ $ menuContent <$> dMenuContent

main :: IO ()
main =
  mainWidgetWithHead headWidget $ do
    let e = Lam (Binding "f") $ Lam (Binding "x") $ App (App (Var "f") (Var "x")) (Var "x")
    let (i, g, _) = unbuild mempty emptyContext e
    ePostBuild <- getPostBuild
    rec
      eKeyD <- gate bNotEditing <$> documentKey "d"
      eKeyA <- gate bNotEditing <$> documentKey "a"
      eKeyHH <- gate bNotEditing <$> documentKey "H"
      eKeyH <- gate bNotEditing <$> documentKey "h"
      eKeyJ <- gate bNotEditing <$> documentKey "j"
      eKeyK <- gate bNotEditing <$> documentKey "k"
      eKeyLL <- gate bNotEditing <$> documentKey "L"
      eKeyL <- gate bNotEditing <$> documentKey "l"
      eKeyBackslash <- gate bNotEditing <$> documentKey "\\"
      eKeyE <- gate bNotEditing <$> documentKey "e"
      let
        eDecos = select appEventSelector DecosK <> eCursorDeco
        eDelete = deleteNode <$> current dCursor <*> currentIncremental dGraph <@ eKeyD
        (eAppGraph, eAppCursor) =
          splitE $
          appNode <$>
          current dCursor <*>
          currentIncremental dGraph <@
          eKeyA
        (eLamGraph, eLamCursor) =
          splitE $
          lamNode <$>
          current dCursor <*>
          currentIncremental dGraph <@
          eKeyBackslash
        eEditBinding =
          editBinding <$>
          currentIncremental dGraph <*>
          current dCursor <@
          eKeyE
        eActions =
          eEditBinding <>
          select appEventSelector ActionsK
      dDecos <-
        foldDyn
          (\(MonoidalMap new) old ->
             Map.merge
               (Map.mapMissing $ \_ (Endo v) -> v emptyDeco)
               Map.preserveMissing
               (Map.zipWithMatched $ \_ (Endo v1) v2 -> v1 v2)
               new
               old)
          mempty
          eDecos
      (dGraph, appEvents) <-
        runEventWriterT $
          mkLiveGraph eActions (eLamGraph <> eAppGraph <> eDelete) g <*
          renderID dGraph dDecos eActions i
      let appEventSelector = fan appEvents
      let
        eStartEditing =
          ffilter (DMap.foldrWithKey (\_ v rest -> isEditStart v || rest) False) eActions
        eStopEditing =
          ffilter (DMap.foldrWithKey (\_ v rest -> isEditStop v || rest) False) eActions
      bNotEditing <- hold True $ leftmost [False <$ eStartEditing, True <$ eStopEditing]
      dCursor <-
        holdDyn (SomeID i) . fmapMaybe id $
        mergeWith (<|>)
        [ nextLeaf <$> currentIncremental dGraph <*> current dCursor <@ eKeyL
        , prevLeaf <$> currentIncremental dGraph <*> current dCursor <@ eKeyH
        , parentNode <$> currentIncremental dGraph <*> current dCursor <@ eKeyK
        , childNode <$> currentIncremental dGraph <*> current dCursor <@ eKeyJ
        , nextSibling <$> currentIncremental dGraph <*> current dCursor <@ eKeyLL
        , prevSibling <$> currentIncremental dGraph <*> current dCursor <@ eKeyHH
        , eAppCursor
        , eLamCursor
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
    let eMenu = select appEventSelector ContextMenuK
    eMenuClose <- documentClick
    mkContextMenu eMenu eMenuClose
    pure ()
