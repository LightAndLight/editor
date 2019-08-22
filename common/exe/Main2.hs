{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
module Main where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Control.Monad.Fix (MonadFix)
import Data.Dependent.Map (DMap, GCompare)
import Data.Dependent.Sum (DSum(..))
import Data.Functor.Identity (Identity(..))
import Data.Map (Map)
import Data.Map.Monoidal (MonoidalMap(..))
import Data.Maybe (fromMaybe)
import Data.Monoid (Endo(..))
import Data.String (fromString)
import Data.Text (Text)
import GHCJS.DOM.KeyboardEvent (getKey)
import GHCJS.DOM.EventM (event, on)
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex
import Reflex.Dom
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
  , context, parent
  )

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
  Incremental t (UpdateLiveGraph t) ->
  Context Identity ->
  m (Context (Dynamic t))
mkDynamicContext dGraph (Context p (Identity sc)) = do
  dm_dNode <-
    case p of
      Nothing -> pure $ constDyn Nothing
      Just pid -> lookupIncremental pid dGraph
  edParentScope <-
    networkView $ do
      m_dNode <- dm_dNode
      case m_dNode of
        Just (LamInfo ctx bid _ _) -> do
          dBinding <- lookupIncremental bid dGraph
          let
            dBindingVal =
              dBinding >>= \(BindingInfo _ dVal) -> fmap Binding dVal
          pure $
            Map.insert <$>
            dBindingVal <*>
            _ctxLocalScope ctx
        Just dNode -> pure $ dNode >>= _ctxLocalScope . context
        Nothing -> pure $ constDyn mempty
  dScope <-
    holdDyn sc $ push (fmap Just . sample . current) edParentScope
  pure $ Context p dScope

data Action a where
  EditBinding :: Action Binding
  CommitBinding :: String -> Action Binding
deriving instance Show (Action a)

mkDynamicNode ::
  (Reflex t, MonadHold t m) =>
  Incremental t (UpdateLiveGraph t) ->
  Event t (DMap ID Action) ->
  ID a ->
  NodeInfo Identity a ->
  m (NodeInfo (Dynamic t) a)
mkDynamicNode dGraph eActions i node =
  let
    eAction = fmapMaybe (DMap.lookup i) eActions
  in
  case node of
    BindingInfo ctx (Identity val) -> do
      ctx' <- mkDynamicContext dGraph ctx
      dVal <-
        holdDyn val $
        fmapMaybe
          (\case; CommitBinding val' -> Just val'; _ -> Nothing)
          eAction
      pure $ BindingInfo ctx' dVal
    VarInfo ctx (Identity val) (Identity vars) -> do
      ctx' <- mkDynamicContext dGraph ctx
      pure $ VarInfo ctx' (pure val) (pure vars)
    HoleInfo ctx -> do
      ctx' <- mkDynamicContext dGraph ctx
      pure $ HoleInfo ctx'
    AppInfo ctx c1 c2 (Identity vars) -> do
      ctx' <- mkDynamicContext dGraph ctx
      pure $ AppInfo ctx' c1 c2 (pure vars)
    LamInfo ctx c1 c2 (Identity vars) -> do
      ctx' <- mkDynamicContext dGraph ctx
      pure $ LamInfo ctx' c1 c2 (pure vars)

mkLiveGraph ::
  ( DomBuilder t m, MonadHold t m, MonadFix m, PostBuild t m
  , EventWriter t (MonoidalMap SomeID (Endo Deco), DMap ID Action) m
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

renderID ::
  forall t m a.
  ( DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m
  , DomBuilderSpace m ~ GhcjsDomSpace, MonadJSM m
  , PerformEvent t m, MonadJSM (Performable m), TriggerEvent t m
  , EventWriter t (MonoidalMap SomeID (Endo Deco), DMap ID Action) m
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
  let eEnter :: Event t () = domEvent Mouseenter theSpan
  let eLeave :: Event t () = domEvent Mouseleave theSpan
  tellEvent $ (MonoidalMap.singleton (SomeID i) info, mempty) <$ gate bIsLeaf eEnter
  tellEvent $ (MonoidalMap.singleton (SomeID i) uninfo, mempty) <$ gate bIsLeaf eLeave
  pure $ dm_node >>= maybe (pure Nothing) (fmap (Just . nodeSort))

renderNode ::
  ( DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m
  , DomBuilderSpace m ~ GhcjsDomSpace, MonadJSM m
  , PerformEvent t m, MonadJSM (Performable m), TriggerEvent t m
  , EventWriter t (MonoidalMap SomeID (Endo Deco), DMap ID Action) m
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
      tellEvent $ (,) mempty . DMap.singleton i . CommitBinding . Text.unpack <$> eCommit
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
    eKeyBackslash <- documentKey "\\"
    eKeyE <- documentKey "e"
    ePostBuild <- getPostBuild
    rec
      let
        eDecos = eDecos_ <> eCursorDeco
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
          eActions_
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
      (dGraph, allEvents) <-
        runEventWriterT $
          mkLiveGraph eActions (eLamGraph <> eAppGraph <> eDelete) g <*
          renderID dGraph dDecos eActions i
      let (eDecos_, eActions_) = splitE allEvents
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
    pure ()
