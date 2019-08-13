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
import Data.Text (Text)
import Data.Set (Set)
import GHCJS.DOM.EventM (preventDefault, mouseClientXY, on)
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex
import Reflex.Dom hiding (preventDefault)

import qualified GHCJS.DOM.GlobalEventHandlers as Events
import qualified Data.Dependent.Map as DMap
import qualified Data.Map as Map
import qualified Data.Text as Text

data Color = Grey | Red
  deriving Show

renderColor :: Color -> Text
renderColor Grey = "gray"
renderColor Red = "red"

data Deco = Deco { _decoWarn :: Bool, _decoInfo :: Bool }

emptyDeco :: Deco
emptyDeco = Deco False False

warn :: Deco -> Deco
warn d = d { _decoWarn = True }

unwarn :: Deco -> Deco
unwarn d = d { _decoWarn = False }

info :: Deco -> Deco
info d = d { _decoInfo = True }

uninfo :: Deco -> Deco
uninfo d = d { _decoInfo = False }

data Change
  = EditBinding
  | UpdateBinding String
  | CommitBinding
  deriving Show

data ChangeK a where
  EditBindingK :: ChangeK ()
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
  BoundEditInfo ::
    Event t Bool -> -- is this edit causing it to be captured
    NodeEditInfo t Bound

data RenderState t
  = RenderState
  { _rsLiveGraph :: DMap ID (NodeInfo (Dynamic t))
  , _rsEditInfo :: DMap ID (NodeEditInfo t)
  }
instance Semigroup (RenderState t) where
  RenderState a b <> RenderState a' b' = RenderState (a <> a') (b <> b')
instance Monoid (RenderState t) where
  mempty = RenderState mempty mempty

renderBindingInfo ::
  forall t m.
  ( DomBuilder t m, MonadHold t m, MonadFix m
  , PostBuild t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  ID Binding -> -- node id
  DMap ID (NodeInfo Identity) -> -- static graph
  EventSelector t ChangeIdK -> -- change events
  Event t () -> -- mouse over node
  Event t () -> -- mouse exit node
  Event t (Int, Int) -> -- right click
  Dynamic t (Map Binding (ID Binding)) -> -- local scope
  RenderState t ->
  Context Identity -> -- node context
  String -> -- node value
  m
    ( NodeInfo (Dynamic t) Binding
    , RenderState t
    , Event t [Action]
    , MonoidalMap SomeID (Event t (Endo Deco))
    , MonoidalMap SomeID (Event t (DMap ChangeK Identity))
    )
renderBindingInfo root nodes eChanges eEnter eLeave eOpenMenu dScope rs ctx a = do
  let
    support :: Dynamic t (Set (ID Bound)) =
      fromMaybe (pure mempty) $ do
        SomeID par <- _ctxParent ctx
        res <- DMap.lookup par (_rsLiveGraph rs)
        case res of
          LamInfo _ _ bdy _ -> do
            res' <- DMap.lookup bdy (_rsLiveGraph rs)
            pure $ freeVars res'
          _ -> error "binding not attached to lambda"

  let
    eAnyCaptured :: Event t Bool =
      switchDyn $
      mergeWith (||) .
      fmap (\(BoundEditInfo eCap) -> eCap) .
      fromMaybe [] .
      foldr
        (\b rest -> (:) <$> DMap.lookup b (_rsEditInfo rs) <*> rest)
        (Just []) <$>
      support
  bNotCaptured <- hold True $ fmapCheap not eAnyCaptured
  let eEditBinding = select eChanges $ ChangeIdK (SomeID root) EditBindingK
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
            eEditBinding
          ])
  let
    changes1 =
      MonoidalMap $
      Map.singleton
        (SomeID root)
        (merge . DMap.fromList $
          [ UpdateBindingK :=> eUpdate
          , CommitBindingK :=> eCommit
          ])

    Identity bounds = getBounds nodes root
    decos1 =
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

    eAction' =
      (\(x, y) -> [OpenMenu (SomeID root) x y [Rename]]) <$>
      eOpenMenu

  let ni' = BindingInfo (ctx { _ctxLocalScope = dScope }) dContent

  let
    rs' =
      RenderState
      { _rsLiveGraph = DMap.singleton root ni'
      , _rsEditInfo = mempty
      }

  pure
    ( ni'
    , rs'
    , eAction'
    , decos1
    , changes1
    )

renderBoundInfo ::
  forall t m.
  ( DomBuilder t m, MonadHold t m
  , PostBuild t m
  ) =>
  ID Bound ->
  DMap ID (NodeInfo Identity) -> -- static graph
  EventSelector t ChangeIdK -> -- change events
  Event t () -> -- mouse over
  Event t () -> -- mouse exit
  Dynamic t (Map Binding (ID Binding)) -> -- local scope
  RenderState t ->
  Context Identity -> -- node context
  String -> -- node value
  m
    ( NodeInfo (Dynamic t) Bound
    , RenderState t
    , Event t [Action]
    , MonoidalMap SomeID (Event t (Endo Deco))
    , MonoidalMap SomeID (Event t (DMap ChangeK Identity))
    )
renderBoundInfo root nodes eChanges eEnter eLeave dScope rs ctx a = do
  let binding :: Maybe (ID Binding) = getBinding nodes root

  let
    dLocalScope :: Dynamic t (Map Binding (ID Binding)) =
      fromMaybe (error "local scope missing") $ do
        BoundInfo c _ <- DMap.lookup root (_rsLiveGraph rs)
        pure $ _ctxLocalScope c

  let
    eUpdateBinding :: Event t String =
      fromMaybe never $ do
        b <- binding
        Just $ select eChanges (ChangeIdK (SomeID b) UpdateBindingK)

  dContent <- holdDyn a eUpdateBinding

  dynText $ fromString <$> dContent

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

    decos1 =
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

  let ni' = BoundInfo (ctx { _ctxLocalScope = dScope }) dContent

  let
    rs' =
      RenderState
      { _rsLiveGraph = DMap.singleton root ni'
      , _rsEditInfo = DMap.singleton root $ BoundEditInfo eCaptured
      }

  pure
    ( ni'
    , rs'
    , never
    , decos1
    , mempty
    )

renderHoleInfo ::
  DomBuilder t m =>
  ID Expr ->
  Dynamic t (Map Binding (ID Binding)) ->
  RenderState t ->
  Context Identity ->
  m
    ( NodeInfo (Dynamic t) Expr
    , RenderState t
    , Event t [Action]
    , MonoidalMap SomeID (Event t (Endo Deco))
    , MonoidalMap SomeID (Event t (DMap ChangeK Identity))
    )
renderHoleInfo root dScope _ ctx = do
  text "_"

  let ni' = HoleInfo (ctx { _ctxLocalScope = dScope })

  let rs' = RenderState { _rsLiveGraph = DMap.singleton root ni', _rsEditInfo = mempty }

  pure (ni', rs', never, mempty, mempty)

renderVarInfo ::
  ( DomBuilder t m, MonadHold t m, MonadFix m, MonadJSM m
  , PostBuild t m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  ID Expr ->
  DMap ID (NodeInfo Identity) ->
  EventSelector t ChangeIdK ->
  EventSelector t (Const2 SomeID (Endo Deco)) ->
  Dynamic t (Map Binding (ID Binding)) ->
  RenderState t ->
  Context Identity ->
  ID Bound ->
  Set (ID Bound) ->
  m
    ( NodeInfo (Dynamic t) Expr
    , RenderState t
    , Event t [Action]
    , MonoidalMap SomeID (Event t (Endo Deco))
    , MonoidalMap SomeID (Event t (DMap ChangeK Identity))
    )
renderVarInfo root nodes eChanges eDecos dScope rs ctx val vars = do
  (_, rs1, eActions1, decos1, changes1) <-
    renderExpr (val, nodes) eDecos eChanges dScope rs

  let ni' = VarInfo (ctx { _ctxLocalScope = dScope }) val (pure vars)

  let rs' = rs1 { _rsLiveGraph = DMap.insert root ni' (_rsLiveGraph rs1) }

  pure (ni', rs', eActions1, decos1, changes1)

renderAppInfo ::
  ( DomBuilder t m, MonadHold t m, MonadFix m, MonadJSM m
  , PostBuild t m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  ID Expr ->
  DMap ID (NodeInfo Identity) ->
  EventSelector t ChangeIdK ->
  EventSelector t (Const2 SomeID (Endo Deco)) ->
  Dynamic t (Map Binding (ID Binding)) ->
  RenderState t ->
  Context Identity ->
  ID Expr ->
  ID Expr ->
  Set (ID Bound) ->
  m
    ( NodeInfo (Dynamic t) Expr
    , RenderState t
    , Event t [Action]
    , MonoidalMap SomeID (Event t (Endo Deco))
    , MonoidalMap SomeID (Event t (DMap ChangeK Identity))
    )
renderAppInfo root nodes eChanges eDecos dScope rs ctx a b vars = do
  (_, rs1, eActions1, decos1, changes1) <-
    renderExpr (a, nodes) eDecos eChanges dScope rs
  text " "
  (_, rs2, eActions2, decos2, changes2) <-
    renderExpr (b, nodes) eDecos eChanges dScope rs

  let ni' = AppInfo (ctx { _ctxLocalScope = dScope }) a b (pure vars)

  let
    rs3 = rs1 <> rs2
    rs' = rs3 { _rsLiveGraph = DMap.insert root ni' (_rsLiveGraph rs3) }

  pure
    ( ni'
    , rs'
    , eActions1 <> eActions2
    , decos1 <> decos2
    , changes1 <> changes2
    )

renderLamInfo ::
  ( DomBuilder t m, MonadHold t m, MonadFix m, MonadJSM m
  , PostBuild t m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  ID Expr ->
  DMap ID (NodeInfo Identity) ->
  EventSelector t ChangeIdK ->
  EventSelector t (Const2 SomeID (Endo Deco)) ->
  Dynamic t (Map Binding (ID Binding)) ->
  RenderState t ->
  Context Identity ->
  ID Binding ->
  ID Expr ->
  Set (ID Bound) ->
  m
    ( NodeInfo (Dynamic t) Expr
    , RenderState t
    , Event t [Action]
    , MonoidalMap SomeID (Event t (Endo Deco))
    , MonoidalMap SomeID (Event t (DMap ChangeK Identity))
    )
renderLamInfo root nodes eChanges eDecos dScope rs ctx a b vars = do
  text "\\"
  (BindingInfo _ dBindingVal, rs1, eActions1, decos1, changes1) <-
    renderExpr (a, nodes) eDecos eChanges dScope rs
  text " -> "
  (_, rs2, eActions2, decos2, changes2) <-
    renderExpr
      (b, nodes)
      eDecos
      eChanges
      (flip Map.insert a . Binding <$> dBindingVal <*> dScope)
      rs

  let ni' = LamInfo (ctx { _ctxLocalScope = dScope }) a b (pure vars)

  let
    rs3 = rs1 <> rs2
    rs' = rs3 { _rsLiveGraph = DMap.insert root ni' (_rsLiveGraph rs3) }

  pure
    ( ni'
    , rs'
    , eActions1 <> eActions2
    , decos1 <> decos2
    , changes1 <> changes2
    )

renderExpr ::
  forall t m a.
  ( DomBuilder t m
  , PostBuild t m, TriggerEvent t m, MonadHold t m
  , MonadJSM m
  , DomBuilderSpace m ~ GhcjsDomSpace
  , MonadFix m
  ) =>
  (ID a, DMap ID (NodeInfo Identity)) ->
  EventSelector t (Const2 SomeID (Endo Deco)) ->
  EventSelector t ChangeIdK ->
  Dynamic t (Map Binding (ID Binding)) -> -- localscope
  RenderState t ->
  m
    ( NodeInfo (Dynamic t) a
    , RenderState t
    , Event t [Action]
    , MonoidalMap SomeID (Event t (Endo Deco))
    , MonoidalMap SomeID (Event t (DMap ChangeK Identity))
    )
renderExpr (root, nodes) eDecos eChanges dScope rs = do
  case DMap.lookup root nodes of
    Nothing -> do
      text $ fromString (show root) <> "Not found"
      let rs' = RenderState { _rsLiveGraph = mempty, _rsEditInfo = mempty }
      pure (error "missing node info", rs', never, mempty, mempty)
    Just ni -> do
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
            (\(Deco w i) ->
                if w
                then "style" =: "background-color: red"
                else
                  if i
                  then "style" =: "background-color: grey"
                  else mempty) <$>
            dDeco
        (theSpan, (nni, rs', eActions, decos', changes')) <-
          elDynAttr' "span" (("id" =: fromString (show root) <>) <$> dStyling) $
          case ni of
            BindingInfo ctx (Identity a) ->
              renderBindingInfo root nodes eChanges eEnter eLeave eOpenMenu dScope rs ctx a
            BoundInfo ctx (Identity a) ->
              renderBoundInfo root nodes eChanges eEnter eLeave dScope rs ctx a
            HoleInfo ctx -> renderHoleInfo root dScope rs ctx
            VarInfo ctx val (Identity vars) ->
              renderVarInfo root nodes eChanges eDecos dScope rs ctx val vars
            AppInfo ctx a b (Identity vars) ->
              renderAppInfo root nodes eChanges eDecos dScope rs ctx a b vars
            LamInfo ctx a b (Identity vars) ->
              renderLamInfo root nodes eChanges eDecos dScope rs ctx a b vars
      pure (nni, rs', eActions, decos', changes')

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
          SomeID ID_Binding{} -> DMap.singleton (ChangeIdK i EditBindingK) (pure ()) <$ eClick
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
        App (App (Var $ Bound "f") (Var $ Bound "x")) (Var $ Bound "x")
      (eid, enodes, _) = unbuild mempty (Context Nothing mempty) e
    document <- askDocument
    eCloseMenu <- wrapDomEvent document (`on` Events.click) $ pure [CloseMenu]
    rec
      (_, rs, eActions, MonoidalMap decos, MonoidalMap changes) <-
        renderExpr
          (eid, enodes)
          (fanMap $ mergeMap decos)
          (fan $ fmap (nestingMaps ChangeIdK) (mergeMap changes) <> eMenuChanges)
          (pure mempty)
          rs
      eMenuChanges <- menu (eCloseMenu <> eActions)
    pure ()
