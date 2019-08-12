{-# language FlexibleContexts #-}
{-# language GADTs #-}
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
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Map.Monoidal (MonoidalMap(..))
import Data.Maybe (fromMaybe)
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

data Decoration
  = Highlight Color
  | Clear

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

renderExpr ::
  forall t m a.
  ( DomBuilder t m
  , PostBuild t m, TriggerEvent t m, MonadHold t m
  , MonadJSM m
  , DomBuilderSpace m ~ GhcjsDomSpace
  , MonadFix m
  ) =>
  (ID a, DMap ID (NodeInfo Identity)) ->
  EventSelector t (Const2 SomeID (NonEmpty Decoration)) ->
  EventSelector t ChangeIdK ->
  DMap ID (NodeInfo (Dynamic t)) ->
  Dynamic t (Map Binding (ID Binding)) -> -- localscope
  DMap ID (NodeEditInfo t) ->
  m
    ( NodeInfo (Dynamic t) a
    , DMap ID (NodeInfo (Dynamic t))
    , DMap ID (NodeEditInfo t)
    , Event t [Action]
    , MonoidalMap SomeID (Event t (NonEmpty Decoration))
    , MonoidalMap SomeID (Event t (DMap ChangeK Identity))
    )
renderExpr (root, nodes) eDecos eChanges liveMap dScope editInfo = do
  case DMap.lookup root nodes of
    Nothing -> do
      text $ fromString (show root) <> "Not found"
      pure (error "missing node info", mempty, mempty, never, mempty, mempty)
    Just ni -> do
      rec
        let eEnter :: Event t () = domEvent Mouseenter theSpan
        let eLeave :: Event t () = domEvent Mouseleave theSpan
        eOpenMenu :: Event t (Int, Int) <-
          wrapDomEvent (_element_raw theSpan) (elementOnEventName Contextmenu) $ do
            preventDefault
            mouseClientXY
        dStyling <-
          holdDyn
            mempty
            (fmapMaybe
               (foldr
                  (\case
                     Highlight col ->
                       const . Just $
                       "style" =: ("background-color: " <> renderColor col)
                     Clear ->
                       const $ Just mempty)
                  Nothing)
               (select eDecos (Const2 $ SomeID root)))
        (theSpan, (nni, mp, editInfo', eActions, decos', changes')) <-
          elDynAttr' "span" (("id" =: fromString (show root) <>) <$> dStyling) $
          case ni of
            BindingInfo ctx (Identity a) -> do
              let
                support :: Dynamic t (Set (ID Bound)) =
                  fromMaybe (pure mempty) $ do
                    SomeID par <- _ctxParent ctx
                    res <- DMap.lookup par liveMap
                    case res of
                      LamInfo _ _ bdy _ -> do
                        res' <- DMap.lookup bdy liveMap
                        pure $ freeVars res'
                      _ -> error "binding not attached to lambda"
              let
                eAnyCaptured :: Event t Bool =
                  switchDyn $
                  mergeWith (||) .
                  fmap (\(BoundEditInfo eCap) -> eCap) .
                  fromMaybe [] .
                  foldr
                    (\b rest -> (:) <$> DMap.lookup b editInfo <*> rest)
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
                    (mergeList
                     [ Highlight Grey <$ eEnter
                     , Clear <$ eLeave
                     ]) $
                  foldr
                    (\b ->
                       Map.insert
                         (SomeID b)
                         (mergeList [Highlight Grey <$ eEnter, Clear <$ eLeave]))
                    mempty
                    bounds

                eAction' =
                  (\(x, y) -> [OpenMenu (SomeID root) x y [Rename]]) <$>
                  eOpenMenu

              let ni' = BindingInfo (ctx { _ctxLocalScope = dScope }) dContent

              pure
                ( ni'
                , DMap.singleton root ni'
                , mempty
                , eAction'
                , decos1
                , changes1
                )
            BoundInfo ctx (Identity a) -> do
              let binding :: Maybe (ID Binding) = getBinding nodes root

              let
                dLocalScope :: Dynamic t (Map Binding (ID Binding)) =
                  fromMaybe (error "local scope missing") $ do
                    BoundInfo c _ <- DMap.lookup root liveMap
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
                         (mergeList [Highlight Grey <$ eEnter, Clear <$ eLeave]))
                    binding $
                  Map.singleton
                    (SomeID root)
                    (mergeList
                     [ (\b -> if b then Highlight Red else Highlight Grey) <$> eCaptured
                     , Highlight Grey <$ eEnter
                     , Clear <$ eLeave
                     ])

              let ni' = BoundInfo (ctx { _ctxLocalScope = dScope }) dContent
              pure
                ( ni'
                , DMap.singleton root ni'
                , DMap.singleton root $ BoundEditInfo eCaptured
                , never
                , decos1
                , mempty
                )
            HoleInfo ctx -> do
              text "_"
              let ni' = HoleInfo (ctx { _ctxLocalScope = dScope })
              pure (ni', DMap.singleton root ni', mempty, never, mempty, mempty)
            VarInfo ctx val (Identity vars) -> do
              (_, mp1, editInfo1, eActions1, decos1, changes1) <-
                renderExpr (val, nodes) eDecos eChanges liveMap dScope editInfo
              let ni' = VarInfo (ctx { _ctxLocalScope = dScope }) val (pure vars)
              pure (ni', DMap.insert root ni' mp1, editInfo1, eActions1, decos1, changes1)
            AppInfo ctx a b (Identity vars) -> do
              (_, mp1, editInfo1, eActions1, decos1, changes1) <-
                renderExpr (a, nodes) eDecos eChanges liveMap dScope editInfo
              text " "
              (_, mp2, editInfo2, eActions2, decos2, changes2) <-
                renderExpr (b, nodes) eDecos eChanges liveMap dScope editInfo

              let ni' = AppInfo (ctx { _ctxLocalScope = dScope }) a b (pure vars)

              pure
                ( ni'
                , DMap.insert root ni' $ mp1 <> mp2
                , editInfo1 <> editInfo2
                , eActions1 <> eActions2
                , decos1 <> decos2
                , changes1 <> changes2
                )
            LamInfo ctx a b (Identity vars) -> do
              text "\\"
              (BindingInfo _ dBindingVal, mp1, editInfo1, eActions1, decos1, changes1) <-
                renderExpr (a, nodes) eDecos eChanges liveMap dScope editInfo
              text " -> "
              (_, mp2, editInfo2, eActions2, decos2, changes2) <-
                renderExpr
                  (b, nodes)
                  eDecos
                  eChanges
                  liveMap
                  (flip Map.insert a . Binding <$> dBindingVal <*> dScope)
                  editInfo
              let ni' = LamInfo (ctx { _ctxLocalScope = dScope }) a b (pure vars)
              pure
                ( ni'
                , DMap.insert root ni' $ mp1 <> mp2
                , editInfo1 <> editInfo2
                , eActions1 <> eActions2
                , decos1 <> decos2
                , changes1 <> changes2
                )
      pure (nni, mp, editInfo', eActions, decos', changes')

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

nestingMaps :: GCompare g => (forall x. a -> f x -> g x) -> Map a (DMap f Identity) -> DMap g Identity
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
      (_, mp, editInfo, eActions, MonoidalMap decos, MonoidalMap changes) <-
        renderExpr
          (eid, enodes)
          (fanMap $ mergeMap decos)
          (fan $ fmap (nestingMaps ChangeIdK) (mergeMap changes) <> eMenuChanges)
          mp
          (pure mempty)
          editInfo
      eMenuChanges <- menu (eCloseMenu <> eActions)
    pure ()
