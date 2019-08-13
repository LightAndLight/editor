{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses, TypeFamilies, UndecidableInstances #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
module Main where

import Editor

import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader (MonadReader, runReaderT, asks, local)
import Data.Char (ord)
import Data.Foldable (fold)
import Data.Functor.Identity (Identity(..))
import Data.Functor.Misc (Const2(..))
import Data.GADT.Compare.TH (deriveGEq, deriveGCompare)
import Data.Map (Map)
import Data.Map.Monoidal (MonoidalMap(..))
import Data.Maybe (fromMaybe)
import Data.Monoid (Endo(..))
import Data.Dependent.Map (DMap, GCompare)
import Data.Dependent.Sum (DSum(..))
import Data.String (fromString)
import Data.Semigroup (First(..))
import Data.Set (Set)
import GHCJS.DOM.EventM (preventDefault, mouseClientXY, on)
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex
import Reflex.Dom hiding (preventDefault)

import qualified GHCJS.DOM.GlobalEventHandlers as Events
import qualified Data.Dependent.Map as DMap
import qualified Data.Map as Map
import qualified Data.Text as Text

data Deco
  = Deco
  { _decoWarn :: Bool
  , _decoInfo :: Bool
  , _decoDotted :: Bool
  }

emptyDeco :: Deco
emptyDeco = Deco False False False

warn :: Deco -> Deco
warn d = d { _decoWarn = True }

unwarn :: Deco -> Deco
unwarn d = d { _decoWarn = False }

info :: Deco -> Deco
info d = d { _decoInfo = True }

uninfo :: Deco -> Deco
uninfo d = d { _decoInfo = False }

dotted :: Deco -> Deco
dotted d = d { _decoDotted = True }

undotted :: Deco -> Deco
undotted d = d { _decoDotted = False }

data Change
  = RenameBinding
  | UpdateBinding String
  | CommitBinding
  deriving Show

data ChangeK a where
  RenameBindingK :: ChangeK ()
  UpdateBindingK :: ChangeK String
  CommitBindingK :: ChangeK ()
deriveGEq ''ChangeK
deriveGCompare ''ChangeK

data ChangeIdK a where
  ChangeIdK :: SomeID -> ChangeK a -> ChangeIdK a
deriveGEq ''ChangeIdK
deriveGCompare ''ChangeIdK

data MenuItem = Rename
data Action
  = OpenMenu SomeID Int Int [MenuItem]
  | CloseMenu

data NodeEditInfo t a where
  VarEditInfo ::
    Event t Bool -> -- is this edit causing it to be captured
    NodeEditInfo t Expr

data RenderInfo t
  = RenderInfo
  { _ri_liveGraph :: DMap ID (NodeInfo (Dynamic t))
  , _ri_editInfo :: DMap ID (NodeEditInfo t)
  , _ri_eAction :: Event t [Action]
  , _ri_decos :: MonoidalMap SomeID (Event t (Endo Deco))
  , _ri_changes :: MonoidalMap SomeID (Event t (DMap ChangeK Identity))
  , _ri_eCursorTo :: Event t (First SomeID)
  }

instance Reflex t => Semigroup (RenderInfo t) where
  RenderInfo a b c d e f <> RenderInfo a' b' c' d' e' f' =
    RenderInfo (a <> a') (b <> b') (c <> c') (d <> d') (e <> e') (f <> f')
instance Reflex t => Monoid (RenderInfo t) where
  mempty = RenderInfo mempty mempty mempty mempty mempty mempty

data RenderEnv t
  = RenderEnv
  { _re_eEnter :: Event t ()
  , _re_eLeave :: Event t ()
  , _re_eCursorLeafRight :: Event t ()
  , _re_eCursorLeafLeft :: Event t ()
  , _re_eCursorSiblingRight :: Event t ()
  , _re_eCursorSiblingLeft :: Event t ()
  , _re_eCursorParent :: Event t ()
  , _re_eCursorChild :: Event t ()
  , _re_eOpenMenu :: Event t (Int, Int)
  , _re_cursor :: Dynamic t SomeID
  , _re_liveGraph :: DMap ID (NodeInfo (Dynamic t))
  , _re_editInfo :: DMap ID (NodeEditInfo t)
  , _re_localScope :: Dynamic t (Map Binding (ID Binding))
  , _re_changes :: EventSelector t ChangeIdK
  , _re_decos :: EventSelector t (Const2 SomeID (Endo Deco))
  }

renderBindingInfo ::
  forall t m.
  ( DomBuilder t m, MonadHold t m, MonadFix m
  , PostBuild t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  , MonadReader (RenderEnv t) m
  ) =>
  ID Binding {- ^ node id -} ->
  DMap ID (NodeInfo Identity) -> -- static graph
  Context Identity -> -- node context
  String -> -- node value
  m (NodeInfo (Dynamic t) Binding, RenderInfo t)
renderBindingInfo root nodes ctx a = do
  liveGraph <- asks _re_liveGraph
  let
    support :: Dynamic t (Set (ID Expr)) =
      fromMaybe (pure mempty) $ do
        SomeID par <- _ctxParent ctx
        res <- DMap.lookup par liveGraph
        case res of
          LamInfo _ _ bdy _ -> do
            res' <- DMap.lookup bdy liveGraph
            pure $ freeVars res'
          _ -> error "binding not attached to lambda"

  editInfo <- asks _re_editInfo
  let
    eAnyCaptured :: Event t Bool =
      switchDyn $
      mergeWith (||) .
      fmap (\(VarEditInfo eCap) -> eCap) .
      fromMaybe [] .
      foldr
        (\b rest -> (:) <$> DMap.lookup b editInfo <*> rest)
        (Just []) <$>
      support
  bNotCaptured <- hold True $ fmapCheap not eAnyCaptured
  eChanges <- asks _re_changes
  let eRenameBinding = select eChanges $ ChangeIdK (SomeID root) RenameBindingK
  rec
    let dContent = dControls >>= fst
    let eCommit = switchDyn $ snd <$> dControls
    let eUpdate = updated dContent
    dControls :: Dynamic t (Dynamic t String, Event t ()) <-
      widgetHold
        ((pure a, never) <$ text (fromString a))
        (leftmost
          [ (\val -> (pure val, never) <$ text (fromString val)) <$>
            current dContent <@
            gate bNotCaptured eCommit
          , (\val ->
              fmap
              (\ti -> (Text.unpack <$> _textInput_value ti, keypress Enter ti))
              (textInput $
                TextInputConfig "text" (fromString val) never (constDyn mempty))) <$>
            current dContent <@
            eRenameBinding
          ])

  eOpenMenu <- asks _re_eOpenMenu
  eEnter <- asks _re_eEnter
  eLeave <- asks _re_eLeave
  dScope <- asks _re_localScope
  let
    Identity bounds = getBounds nodes root
    ni' = BindingInfo (ctx { _ctxLocalScope = dScope }) dContent

    ri =
      RenderInfo
      { _ri_liveGraph = DMap.singleton root ni'
      , _ri_editInfo = mempty
      , _ri_eAction =
        (\(x, y) -> [OpenMenu (SomeID root) x y [Rename]]) <$>
        eOpenMenu
      , _ri_decos =
        MonoidalMap $
        Map.insert
          (SomeID root)
          (fold [Endo info <$ eEnter, Endo uninfo <$ eLeave]) $
        foldr
          (\b ->
              Map.insert
                (SomeID b)
                (fold [Endo info <$ eEnter, Endo uninfo <$ eLeave]))
          mempty
          bounds
      , _ri_changes =
        MonoidalMap $
        Map.singleton
          (SomeID root)
          (merge . DMap.fromList $
            [ UpdateBindingK :=> eUpdate
            , CommitBindingK :=> eCommit
            ])
      , _ri_eCursorTo = never
      }

  pure (ni', ri)

renderVarInfo ::
  forall t m.
  ( DomBuilder t m, MonadHold t m
  , PostBuild t m
  , MonadReader (RenderEnv t) m
  ) =>
  ID Expr ->
  DMap ID (NodeInfo Identity) -> -- static graph
  Context Identity -> -- node context
  String -> -- node value
  Set (ID Expr) -> -- fre vars
  m (NodeInfo (Dynamic t) Expr, RenderInfo t)
renderVarInfo root nodes ctx a vars = do
  let binding :: Maybe (ID Binding) = getBinding nodes root

  liveGraph <- asks _re_liveGraph
  let
    dLocalScope :: Dynamic t (Map Binding (ID Binding)) =
      fromMaybe (error "local scope missing") $ do
        VarInfo c _ _ <- DMap.lookup root liveGraph
        pure $ _ctxLocalScope c

  eChanges <- asks _re_changes
  let
    eUpdateBinding :: Event t String =
      fromMaybe never $ do
        b <- binding
        Just $ select eChanges (ChangeIdK (SomeID b) UpdateBindingK)

  dContent <- holdDyn a eUpdateBinding

  dynText $ fromString <$> dContent

  eEnter <- asks _re_eEnter
  eLeave <- asks _re_eLeave
  let
    eCaptured :: Event t Bool =
      updated $
      (\val ls ->
          fromMaybe False $ do
            found <- Map.lookup (Binding val) ls
            b <- binding
            pure $ found /= b) <$>
      dContent <*>
      dLocalScope

  dScope <- asks _re_localScope
  let
    ni' = VarInfo (ctx { _ctxLocalScope = dScope }) dContent (pure vars)
    ri =
      RenderInfo
      { _ri_liveGraph = DMap.singleton root ni'
      , _ri_editInfo = DMap.singleton root $ VarEditInfo eCaptured
      , _ri_eAction = never
      , _ri_decos =
        MonoidalMap $
        maybe
          id
          (\b ->
              Map.insert
                (SomeID b)
                (fold [Endo info <$ eEnter, Endo uninfo <$ eLeave]))
          binding $
        Map.singleton
          (SomeID root)
          (fold
            [ (\b -> Endo $ if b then warn else unwarn) <$> eCaptured
            , Endo info <$ eEnter
            , Endo uninfo <$ eLeave
            ])
      , _ri_changes = mempty
      , _ri_eCursorTo = never
      }

  pure (ni', ri)

renderHoleInfo ::
  (DomBuilder t m, MonadReader (RenderEnv t) m) =>
  ID Expr ->
  Context Identity ->
  m (NodeInfo (Dynamic t) Expr, RenderInfo t)
renderHoleInfo root ctx = do
  text "_"

  dScope <- asks _re_localScope
  let ni' = HoleInfo (ctx { _ctxLocalScope = dScope })

  let
    ri =
      RenderInfo
      { _ri_liveGraph = DMap.singleton root ni'
      , _ri_editInfo = mempty
      , _ri_eAction = never
      , _ri_decos = mempty
      , _ri_changes = mempty
      , _ri_eCursorTo = never
      }

  pure (ni', ri)

renderAppInfo ::
  ( DomBuilder t m, MonadHold t m, MonadFix m, MonadJSM m
  , PostBuild t m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  , MonadReader (RenderEnv t) m
  ) =>
  ID Expr ->
  DMap ID (NodeInfo Identity) ->
  Context Identity ->
  ID Expr ->
  ID Expr ->
  Set (ID Expr) ->
  m (NodeInfo (Dynamic t) Expr, RenderInfo t)
renderAppInfo root nodes ctx a b vars = do
  (_, ri1) <- renderExpr a nodes
  text " "
  (_, ri2) <- renderExpr b nodes

  dScope <- asks _re_localScope
  let ni' = AppInfo (ctx { _ctxLocalScope = dScope }) a b (pure vars)

  let
    ri3 = ri1 <> ri2
    ri' = ri3 { _ri_liveGraph = DMap.insert root ni' (_ri_liveGraph ri3) }

  pure (ni', ri')

renderLamInfo ::
  ( DomBuilder t m, MonadHold t m, MonadFix m, MonadJSM m
  , PostBuild t m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  , MonadReader (RenderEnv t) m
  ) =>
  ID Expr ->
  DMap ID (NodeInfo Identity) ->
  Context Identity ->
  ID Binding ->
  ID Expr ->
  Set (ID Expr) ->
  m (NodeInfo (Dynamic t) Expr, RenderInfo t)
renderLamInfo root nodes ctx a b vars = do
  text "\\"
  (BindingInfo _ dBindingVal, ri1) <- renderExpr a nodes
  text " -> "
  (_, ri2) <-
    local
      (\re ->
       re
         { _re_localScope =
           flip Map.insert a . Binding <$> dBindingVal <*> _re_localScope re
         })
      (renderExpr b nodes)

  dScope <- asks _re_localScope
  let ni' = LamInfo (ctx { _ctxLocalScope = dScope }) a b (pure vars)

  let
    ri3 = ri1 <> ri2
    ri' = ri3 { _ri_liveGraph = DMap.insert root ni' (_ri_liveGraph ri3) }

  pure (ni', ri')

renderExpr ::
  forall t m a.
  ( DomBuilder t m
  , PostBuild t m, TriggerEvent t m, MonadHold t m
  , MonadJSM m
  , DomBuilderSpace m ~ GhcjsDomSpace
  , MonadFix m
  , MonadReader (RenderEnv t) m
  ) =>
  ID a ->
  DMap ID (NodeInfo Identity) ->
  m (NodeInfo (Dynamic t) a, RenderInfo t)
renderExpr root nodes =
  case DMap.lookup root nodes of
    Nothing -> do
      text $ fromString (show root) <> "Not found"
      pure (error "missing node info", mempty)
    Just ni -> do
      eDecos <- asks _re_decos
      rec
        let eEnter :: Event t () = domEvent Mouseenter theSpan
        let eLeave :: Event t () = domEvent Mouseleave theSpan
        eOpenMenu :: Event t (Int, Int) <-
          wrapDomEvent (_element_raw theSpan) (elementOnEventName Contextmenu) $ do
            preventDefault
            mouseClientXY

        dDeco <-
          foldDyn
            (($) . appEndo)
            emptyDeco
            (select eDecos (Const2 $ SomeID root))

        let
          dStyling =
            (\(Deco w i d) ->
               let
                 bg =
                   if w
                   then "background-color: red;"
                   else
                     if i
                     then "background-color: grey;"
                     else mempty
                 border = if d then "border: 1px dotted black;" else mempty
               in
                 "style" =: (bg <> border)) <$>
            dDeco

        (theSpan, (nni, ri')) <-
          elDynAttr' "span" (("id" =: fromString (show root) <>) <$> dStyling) .
          local
            (\re ->
             re
             { _re_eEnter = eEnter
             , _re_eLeave = eLeave
             , _re_eOpenMenu = eOpenMenu
             }) $
          case ni of
            BindingInfo ctx (Identity a) ->
              renderBindingInfo root nodes ctx a
            HoleInfo ctx -> renderHoleInfo root ctx
            VarInfo ctx (Identity val) (Identity vars) ->
              renderVarInfo root nodes ctx val vars
            AppInfo ctx a b (Identity vars) ->
              renderAppInfo root nodes ctx a b vars
            LamInfo ctx a b (Identity vars) ->
              renderLamInfo root nodes ctx a b vars
      dCursor <- asks _re_cursor
      liveGraph <- asks _re_liveGraph
      eCursorLeafRight <- asks _re_eCursorLeafRight
      eCursorLeafLeft <- asks _re_eCursorLeafLeft
      eCursorSiblingRight <- asks _re_eCursorSiblingRight
      eCursorSiblingLeft <- asks _re_eCursorSiblingLeft
      eCursorParent <- asks _re_eCursorParent
      eCursorChild <- asks _re_eCursorChild
      let
        doSiblingRight = do
          SomeID p <- parent ni
          res <- DMap.lookup p liveGraph
          case res of
            BindingInfo{} -> error "impossible - binding is not a parent"
            HoleInfo{} -> error "impossible - hole is not a parent"
            VarInfo{} -> error "impossible - var is not a parent"
            AppInfo _ a b _ ->
              if SomeID a == SomeID root
              then pure $ SomeID b
              else Nothing
            LamInfo _ a b _ ->
              if SomeID a == SomeID root
              then pure $ SomeID b
              else Nothing
        doSiblingLeft = do
          SomeID p <- parent ni
          res <- DMap.lookup p liveGraph
          case res of
            BindingInfo{} -> error "impossible - binding is not a parent"
            HoleInfo{} -> error "impossible - hole is not a parent"
            VarInfo{} -> error "impossible - var is not a parent"
            AppInfo _ a b _ ->
              if SomeID b == SomeID root
              then pure $ SomeID a
              else Nothing
            LamInfo _ a b _ ->
              if SomeID b == SomeID root
              then pure $ SomeID a
              else Nothing
        doParent = parent ni
        doChild =
          case ni of
            BindingInfo{} -> Nothing
            HoleInfo{} -> Nothing
            VarInfo{} -> Nothing
            AppInfo _ a _ _ -> Just $ SomeID a
            LamInfo _ a _ _ -> Just $ SomeID a

        rightmostLeaf :: forall x. ID x -> Maybe SomeID
        rightmostLeaf i = do
          res <- DMap.lookup i liveGraph
          case res of
            BindingInfo{} -> Just $ SomeID i
            HoleInfo{} -> Just $ SomeID i
            VarInfo{} -> Just $ SomeID i
            AppInfo _ _ a _ -> rightmostLeaf a
            LamInfo _ _ a _ -> rightmostLeaf a

        doLeafLeft :: forall x f. ID x -> NodeInfo f x -> Maybe SomeID
        doLeafLeft from nnni = do
          SomeID p <- parent nnni
          res <- DMap.lookup p liveGraph
          case res of
            BindingInfo{} -> error "impossible - binding is not a parent"
            HoleInfo{} -> error "impossible - hole is not a parent"
            VarInfo{} -> error "impossible - var is not a parent"
            AppInfo _ a b _ ->
              if SomeID from == SomeID b
              then rightmostLeaf a
              else
                if SomeID from == SomeID a
                then doLeafLeft p res
                else error "bad child ID"
            LamInfo _ a b _ ->
              if SomeID from == SomeID b
              then rightmostLeaf a
              else
                if SomeID from == SomeID a
                then doLeafLeft p res
                else error "bad child ID"

        leftmostLeaf :: forall x. ID x -> Maybe SomeID
        leftmostLeaf i = do
          res <- DMap.lookup i liveGraph
          case res of
            BindingInfo{} -> Just $ SomeID i
            HoleInfo{} -> Just $ SomeID i
            VarInfo{} -> Just $ SomeID i
            AppInfo _ a _ _ -> leftmostLeaf a
            LamInfo _ a _ _ -> leftmostLeaf a

        doLeafRight :: forall x f. ID x -> NodeInfo f x -> Maybe SomeID
        doLeafRight from nnni = do
          SomeID p <- parent nnni
          res <- DMap.lookup p liveGraph
          case res of
            BindingInfo{} -> error "impossible - binding is not a parent"
            HoleInfo{} -> error "impossible - hole is not a parent"
            VarInfo{} -> error "impossible - var is not a parent"
            AppInfo _ a b _ ->
              if SomeID from == SomeID a
              then leftmostLeaf b
              else
                if SomeID from == SomeID b
                then doLeafRight p res
                else error "bad child ID"
            LamInfo _ a b _ ->
              if SomeID from == SomeID a
              then leftmostLeaf b
              else
                if SomeID from == SomeID b
                then doLeafRight p res
                else error "bad child ID"
        ri'' =
          ri'
          { _ri_eCursorTo =
            (attachWithMaybe
               (\i _ -> if i == SomeID root then fmap First doSiblingRight else Nothing)
               (current dCursor)
               eCursorSiblingRight) <>
            (attachWithMaybe
               (\i _ -> if i == SomeID root then fmap First doSiblingLeft else Nothing)
               (current dCursor)
               eCursorSiblingLeft) <>
            (attachWithMaybe
               (\i _ -> if i == SomeID root then fmap First doParent else Nothing)
               (current dCursor)
               eCursorParent) <>
            (attachWithMaybe
               (\i _ -> if i == SomeID root then fmap First doChild else Nothing)
               (current dCursor)
               eCursorChild) <>
            (attachWithMaybe
               (\i _ -> if i == SomeID root then fmap First (doLeafRight root ni) else Nothing)
               (current dCursor)
               eCursorLeafRight) <>
            (attachWithMaybe
               (\i _ -> if i == SomeID root then fmap First (doLeafLeft root ni) else Nothing)
               (current dCursor)
               eCursorLeafLeft) <>
            _ri_eCursorTo ri'
          }
      pure (nni, ri'')

data Menu
  = Menu
  { _menu_object :: Maybe SomeID
  , _menu_x :: Int
  , _menu_y :: Int
  , _menu_display :: Bool
  , _menu_items :: [MenuItem]
  }

menuItem ::
  forall t m.
  ( DomBuilder t m, PostBuild t m, MonadHold t m
  , MonadFix m
  ) =>
  SomeID ->
  MenuItem ->
  m (Event t (DMap ChangeIdK Identity))
menuItem i mi =
  case mi of
    Rename -> do
      rec
        let eEnter :: Event t () = domEvent Mouseenter theSpan
        let eLeave :: Event t () = domEvent Mouseleave theSpan
        let eClick :: Event t () = domEvent Click theSpan
        dAttrs <-
          holdDyn mempty $
          leftmost
          [ ("style" =: "background-color: gray") <$ eEnter
          , ("style" =: "background-color: none") <$ eLeave
          ]
        (theSpan, _) <- elDynAttr' "span" dAttrs $ text "rename"
      pure $
        case i of
          SomeID ID_Binding{} -> DMap.singleton (ChangeIdK i RenameBindingK) (pure ()) <$ eClick
          _ -> never

menu ::
  forall t m.
  (DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m) =>
  Event t [Action] ->
  m (Event t (DMap ChangeIdK Identity))
menu eAction = do
  dState :: Dynamic t Menu <-
    foldDyn
      (\acts prev ->
         foldr
           (\act rest ->
              case act of
                OpenMenu obj x y is -> Menu (Just obj) x y True is
                CloseMenu -> rest { _menu_object = Nothing, _menu_display = False })
           prev acts)
      (Menu Nothing 0 0 False [])
      eAction
  let
    dAttrs =
      (\(Menu _ x y disp _) ->
         "id" =: "menu" <>
         "style" =:
         ("position: absolute;" <>
          "background-color: white;" <>
          "border: 1px solid black;" <>
          "left: " <> fromString (show x) <>
          "px; top: " <> fromString (show y) <>
          "px;" <> if disp then "" else "display: none")) <$>
      dState

  es <-
    elDynAttr "div" dAttrs . dyn $
    (\m ->
       maybe
         (pure [])
         (\i -> traverse (menuItem i) (_menu_items m))
         (_menu_object m)) <$>
    dState

  eChange :: Event t (DMap ChangeIdK Identity) <- switchHold never $ fold <$> es
  pure eChange

headWidget :: DomBuilder t m => m ()
headWidget = do
  el "title" $ text "Testing"
  el "style" $ text "html { font-family: monospace; }"

nestingMaps ::
  GCompare g =>
  (forall x. a -> f x -> g x) ->
  Map a (DMap f Identity) ->
  DMap g Identity
nestingMaps comb =
  Map.foldrWithKey
    (\k v rest -> DMap.foldrWithKey (\kk -> DMap.insert (comb k kk)) rest v)
    mempty

main :: IO ()
main =
  mainWidgetWithHead headWidget $ do
    let
      e =
        Lam (Binding "f") $
        Lam (Binding "x") $
        App (App (Var "f") (Var "x")) (Var "x")
      (eid, enodes, _) = unbuild mempty (Context Nothing mempty) e
    document <- askDocument
    eCloseMenu <- wrapDomEvent document (`on` Events.click) $ pure [CloseMenu]
    eDocumentKeyDown <- wrapDomEvent document (`on` Events.keyUp) $ getKeyEvent
    let
      eKeyK =
        fmapMaybe
          (\c -> if c == fromIntegral (ord 'K') then Just () else Nothing)
          eDocumentKeyDown
      eKeyJ =
        fmapMaybe
          (\c -> if c == fromIntegral (ord 'J') then Just () else Nothing)
          eDocumentKeyDown
      eKeyLeft =
        fmapMaybe
          (\c -> if c == 37 then Just () else Nothing)
          eDocumentKeyDown
      eKeyRight =
        fmapMaybe
          (\c -> if c == 39 then Just () else Nothing)
          eDocumentKeyDown
      eKeyH =
        fmapMaybe
          (\c -> if c == fromIntegral (ord 'H') then Just () else Nothing)
          eDocumentKeyDown
      eKeyL =
        fmapMaybe
          (\c -> if c == fromIntegral (ord 'L') then Just () else Nothing)
          eDocumentKeyDown
    ePostBuild <- getPostBuild
    rec
      let
        re =
          RenderEnv
          { _re_eEnter = never
          , _re_eLeave = never
          , _re_eCursorLeafRight = eKeyL
          , _re_eCursorLeafLeft = eKeyH
          , _re_eCursorSiblingRight = eKeyRight
          , _re_eCursorSiblingLeft = eKeyLeft
          , _re_eCursorParent = eKeyK
          , _re_eCursorChild = eKeyJ
          , _re_eOpenMenu = never
          , _re_cursor = dCursor
          , _re_liveGraph = _ri_liveGraph ri
          , _re_editInfo = _ri_editInfo ri
          , _re_localScope = pure mempty
          , _re_changes =
            fan $
            fmap
              (nestingMaps ChangeIdK)
              (mergeMap $ getMonoidalMap $ _ri_changes ri) <>
            eMenuChanges
          , _re_decos =
            fanMap $
            mergeMap (getMonoidalMap $ _ri_decos ri) <>
            ((\i i' ->
                if i /= i'
                then Map.fromList [(i, Endo undotted), (i', Endo dotted)]
                else mempty) <$>
             current dCursor <@>
             updated dCursor) <>
            (Map.singleton (SomeID eid) (Endo dotted) <$ ePostBuild)
          }
      (_, ri) <- flip runReaderT re $ renderExpr eid enodes
      eMenuChanges <- menu (eCloseMenu <> _ri_eAction ri)
      dCursor <- holdDyn (SomeID eid) (coerceEvent $ _ri_eCursorTo ri)
    pure ()
