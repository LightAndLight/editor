{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
module Main where

import Editor

import Control.Monad (guard)
import Control.Monad.Fix (MonadFix)
import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Map.Monoidal (MonoidalMap(..))
import Data.Maybe (fromMaybe)
import Data.Dependent.Map (DMap)
import Data.String (fromString)
import Data.Text (Text)
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

data Change
  = Highlight Color
  | Clear

  | EditBinding
  | UpdateBinding String
  | CommitBinding
  deriving Show

data MenuItem = Rename
data Action
  = OpenMenu SomeID Int Int [MenuItem]
  | CloseMenu

renderExpr ::
  forall t m a.
  ( DomBuilder t m
  , PostBuild t m, TriggerEvent t m, MonadHold t m
  , MonadJSM m
  , DomBuilderSpace m ~ GhcjsDomSpace
  , MonadFix m
  ) =>
  (ID a, DMap ID (NodeInfo Identity)) ->
  MonoidalMap SomeID [Event t Change] ->
  Event t (MonoidalMap SomeID (NonEmpty Change)) ->
  DMap ID (NodeInfo (Dynamic t)) ->
  m
    ( DMap ID (NodeInfo (Dynamic t))
    , Event t [Action]
    , MonoidalMap SomeID [Event t Change]
    )
renderExpr (root, nodes) changes menuChanges liveMap = do
  case DMap.lookup root nodes of
    Nothing -> do
      text $ fromString (show root) <> "Not found"
      pure (mempty, never, mempty)
    Just ni -> do
      rec
        let eEnter :: Event t () = domEvent Mouseenter theSpan
        let eLeave :: Event t () = domEvent Mouseleave theSpan
        eOpenMenu :: Event t (Int, Int) <-
          wrapDomEvent (_element_raw theSpan) (elementOnEventName Contextmenu) $ do
            preventDefault
            mouseClientXY
        let
          eAllChanges =
            eChanges <>
            coerceEvent (mergeMap . fmap mergeList $ getMonoidalMap eChanges')
        dStyling <-
          holdDyn
            mempty
            (fmapMaybe
               (\(MonoidalMap mp1) -> do
                  res <- Map.lookup (SomeID root) mp1
                  foldr
                    (\case
                       Highlight col ->
                         const . Just $
                         "style" =: ("background-color: " <> renderColor col)
                       Clear ->
                         const $ Just mempty
                       _ -> id)
                    Nothing
                    res)
               eAllChanges)
        (theSpan, (mp, eActions, eChanges')) <-
          elDynAttr' "span" (("id" =: fromString (show root) <>) <$> dStyling) $
          case ni of
            BindingInfo ctx (Identity a) -> do
              rec
                dControls :: Dynamic t (Dynamic t String, Event t ()) <-
                  widgetHold
                    ((pure a, never) <$ text (fromString a))
                    (attachWithMaybe
                      (\val (MonoidalMap mp1) -> do
                          res <- Map.lookup (SomeID root) mp1
                          foldr
                            (\case
                               EditBinding ->
                                 const . Just $
                                 (\ti -> (Text.unpack <$> _textInput_value ti, keypress Enter ti)) <$>
                                 textInput (TextInputConfig "text" (fromString val) never (constDyn mempty))
                               CommitBinding ->
                                 const . Just $ (pure val, never) <$ text (fromString val)
                               _ -> id)
                            Nothing
                            res)
                      (current dContent)
                      eChanges)
                let dContent = dControls >>= fst
              let eCommit = switchDyn $ snd <$> dControls
              let eUpdate = updated dContent
              let bounds = getBounds nodes root
              let
                eChanges'' =
                  MonoidalMap $
                  Map.insert
                    (SomeID root)
                    [ UpdateBinding <$> eUpdate
                    , CommitBinding <$ eCommit
                    , Highlight Grey <$ eEnter
                    , Clear <$ eLeave
                    ] $
                  foldr
                    (\b ->
                       Map.insert
                         (SomeID b)
                         [Highlight Grey <$ eEnter, Clear <$ eLeave])
                    mempty
                    bounds
                eAction' =
                  (\(x, y) -> [OpenMenu (SomeID root) x y [Rename]]) <$>
                  eOpenMenu
              pure
                ( DMap.singleton root $ BindingInfo ctx dContent
                , eAction'
                , eChanges''
                )
            BoundInfo ctx (Identity a) -> do
              let binding :: Maybe (ID Binding) = getBinding nodes root
              let
                dBindingVal :: Dynamic t String =
                  fromMaybe (error "binding val missing") $ do
                    b <- binding
                    BindingInfo _ dVal <- DMap.lookup b liveMap
                    pure dVal
                dLocalScope :: Dynamic t (Map Binding (ID Binding)) =
                  fromMaybe (error "local scope missing") $ do
                    b <- binding
                    BindingInfo c _ <- DMap.lookup b liveMap
                    pure $ pure (_ctxLocalScope c)

              let
                eUpdateBinding :: Event t String =
                  maybe never _ $ getMonoidalMap changes
                  fmapMaybe
                    (\(MonoidalMap mp1) -> do
                        b <- binding
                        res <- Map.lookup (SomeID b) mp1
                        foldr
                          (\case; UpdateBinding str -> const (Just str); _ -> id)
                          Nothing
                          res)
                    eChanges

              dContent <- holdDyn a eUpdateBinding

              dynText $ fromString <$> dContent

              let
                eCaptured :: Event t () =
                  fmapMaybe id $
                  (\bval ls val -> guard $ val /= bval && Map.member (Binding val) ls) <$>
                  current dBindingVal <*>
                  current dLocalScope <@>
                  never -- eUpdateBinding

                eChanges'' =
                  MonoidalMap $
                  maybe
                    id
                    (\b ->
                       Map.insert
                         (SomeID b)
                         [Highlight Grey <$ eEnter, Clear <$ eLeave])
                    binding $
                  Map.singleton
                    (SomeID root)
                    [ Highlight Red <$ eCaptured
                    , Highlight Grey <$ eEnter
                    , Clear <$ eLeave
                    ]
              pure
                ( DMap.singleton root $ BoundInfo ctx dContent
                , never
                , eChanges''
                )
            HoleInfo ctx -> do
              text "_"
              pure (DMap.singleton root $ HoleInfo ctx, never, mempty)
            VarInfo ctx val -> do
              (mp1, eActions1, eChanges1) <- renderExpr (val, nodes) changes menuChanges liveMap
              pure (DMap.insert root (VarInfo ctx val) mp1, eActions1, eChanges1)
            AppInfo ctx a b -> do
              (mp1, eActions1, eChanges1) <- renderExpr (a, nodes) changes menuChanges liveMap
              text " "
              (mp2, eActions2, eChanges2) <- renderExpr (b, nodes) changes menuChanges liveMap
              pure
                ( DMap.insert root (AppInfo ctx a b) $ mp1 <> mp2
                , eActions1 <> eActions2
                , eChanges1 <> eChanges2
                )
            LamInfo ctx a b -> do
              text "\\"
              (mp1, eActions1, eChanges1) <- renderExpr (a, nodes) changes menuChanges liveMap
              text " -> "
              (mp2, eActions2, eChanges2) <- renderExpr (b, nodes) changes menuChanges liveMap
              pure
                ( DMap.insert root (LamInfo ctx a b) $ mp1 <> mp2
                , eActions1 <> eActions2
                , eChanges1 <> eChanges2
                )
      pure (mp, eActions, eChanges')

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
  m (Event t Change)
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
          SomeID ID_Binding{} -> EditBinding <$ eClick
          _ -> never

menu ::
  forall t m.
  (DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m) =>
  Event t [Action] ->
  m (Event t (MonoidalMap SomeID (NonEmpty Change)))
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

  eChange :: Event t (NonEmpty Change) <- switchHold never $ mergeList <$> es
  pure . coerceEvent $
    (\m a -> maybe mempty (\i -> Map.singleton i a) (_menu_object m)) <$>
    current dState <@>
    eChange

headWidget :: DomBuilder t m => m ()
headWidget = do
  el "title" $ text "Testing"
  el "style" $ text "html { font-family: monospace; }"

main :: IO ()
main =
  mainWidgetWithHead headWidget $ do
    let
      e =
        Lam (Binding "f") $
        Lam (Binding "x") $
        App (App (Var $ Bound "f") (Var $ Bound "x")) (Var $ Bound "x")
      e' = unbuild mempty (Context Nothing mempty) e
    document <- askDocument
    eCloseMenu <- wrapDomEvent document (`on` Events.click) $ pure [CloseMenu]
    rec
      (mp, eActions, changes) <- renderExpr e' changes eMenuChanges mp
      eMenuChanges <- menu (eCloseMenu <> eActions)
    pure ()
