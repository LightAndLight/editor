{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedLists, OverloadedStrings #-}
{-# language PackageImports #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables, TypeApplications #-}
{-# language TypeFamilies #-}
module App (app) where

import Control.Monad.Fix (MonadFix)
import Control.Monad.State (runStateT)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import GHCJS.DOM.EventM (on, eventTarget)
import qualified GHCJS.DOM.GlobalEventHandlers as Events
import GHCJS.DOM.HTMLElement (HTMLElement)
import GHCJS.DOM.HTMLInputElement (HTMLInputElement)
import qualified GHCJS.DOM.HTMLElement as HTMLElement
import qualified GHCJS.DOM.HTMLInputElement as HTMLInputElement
import JSDOM.Types (liftJSM, toJSVal, fromJSValUnchecked)
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex.Dom hiding (Delete, preventDefault)

import Path (Path, Target(..), target, empty)
import qualified Path.Map
import Syntax
import qualified Typecheck

import Editor (AtPath(..), ChangeCode, Choice(..), Option(..), EditorInit(..), EditorControls(..))
import qualified Editor
import Editor.Selection (Selection(..))
import Input (Inputs(..), getInputs)
import qualified Style
import qualified View

menuInput ::
  ( MonadHold t m, DomBuilder t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  , PostBuild t m, TriggerEvent t m
  , PerformEvent t m, MonadJSM (Performable m)
  , MonadJSM m
  ) =>
  Dynamic t Bool ->
  m (Dynamic t Text)
menuInput dInputValid = do
  (theInput, _) <-
    elDynAttr' "input"
      ((\valid ->
          "type" =: "text" <>
          "class" =: ("input" <> if valid then "" else " is-danger")
       ) <$>
       dInputValid
      )
      (pure ())
  ePostBuild <- delay 0.05 =<< getPostBuild
  performEvent_ $
    (do
       inputEl :: HTMLElement <-
         liftJSM $
         fromJSValUnchecked =<< toJSVal (_element_raw theInput)
       HTMLElement.focus inputEl
    ) <$
    ePostBuild
  eUpdated <-
    fmap switchDyn .
    widgetHold (pure never) $
      (do
         inputEl :: HTMLInputElement <-
           liftJSM $
           fromJSValUnchecked =<< toJSVal (_element_raw theInput)
         wrapDomEvent
           inputEl
           (`on` Events.input)
           (do
              m_target <- eventTarget
              case m_target of
                Nothing -> pure Nothing
                Just t -> do
                  tgt :: HTMLInputElement <-
                    liftJSM $ fromJSValUnchecked =<< toJSVal t
                  Just <$> HTMLInputElement.getValue tgt
           )
      ) <$
      ePostBuild
  holdDyn "" $ fmapMaybe id eUpdated

renderOption ::
  forall t m a.
  DomBuilder t m =>
  Bool ->
  AtPath (Option ChangeCode) a ->
  m (Event t ())
renderOption selected (AtPath _ (Option option)) =
  case option of
    Editor.InsertLam -> item "\\x -> _"
    Editor.InsertApp -> item "_ _"
    Editor.InsertVar -> item "variable"
    Editor.InsertTArr -> item "_ -> _"
    Editor.InsertTForall -> item "∀x. _"
    Editor.InsertTVar -> item "type variable"
    Editor.Rename -> item "rename"
  where
    item :: Text -> m (Event t ())
    item x = do
      (theElement, _) <-
        elAttr' "a"
          ("class" =:
           (Style.classes $
            [ Style.code, Style.Class "dropdown-item"] <>
            [ Style.Class "is-active" | selected ]
           )
          )
          (text x)
      pure $ domEvent Click theElement

renderOptions ::
  DomBuilder t m =>
  Int ->
  (Vector (AtPath (Option ChangeCode) a)) ->
  m (Event t Int)
renderOptions selected options =
  Vector.ifoldr
    (\ix a rest -> do
      e <- renderOption (ix == selected) a
      es <- rest
      pure $ leftmost [ix <$ e, es]
    )
    (pure never)
    options

bindDynamicM ::
  (MonadHold t m, DomBuilder t m) =>
  (a -> m b) ->
  Dynamic t a ->
  m (Dynamic t b)
bindDynamicM f d =
  widgetHold
    (f =<< sample (current d))
    (f <$> updated d)

menuForTarget ::
  forall t m a.
  ( MonadHold t m, DomBuilder t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  , PostBuild t m, TriggerEvent t m
  , PerformEvent t m, MonadJSM (Performable m)
  , MonadJSM m, MonadFix m
  ) =>
  Event t () ->
  Event t () ->
  Dynamic t (Vector (AtPath (Option ChangeCode) a)) ->
  m (Event t (AtPath (Choice ChangeCode) a))
menuForTarget eNextItem eEnter dOptions =
  elAttr "div" ("class" =: "dropdown is-active") $
  elAttr "div" ("class" =: "dropdown-content") $ do
    rec
      dInputValid <-
        holdDyn True $
        (\txt (AtPath _ (Option option)) ->
            case option of
              Editor.InsertVar -> not $ Text.null txt
              Editor.InsertTVar -> not $ Text.null txt
              _ -> True
        ) <$>
        current dInputText <@>
        eOption

      dInputText <- elAttr "div" ("class" =: "dropdown-item") $ menuInput dInputValid

      rec
        dSelection :: Dynamic t Int <-
          holdDyn 0 $
          (\n options -> (n + 1) `mod` Vector.length options) <$>
          current dSelection <*>
          current dOptions <@
          eNextItem

      eItemClicked :: Event t Int <-
        switchDyn <$>
        bindDynamicM
          (uncurry renderOptions)
          ((,) <$> dSelection <*> dOptions)

      let
        eOption :: Event t (AtPath (Option ChangeCode) a)
        eOption =
          leftmost
          [ (Vector.!) <$> current dOptions <*> current dSelection <@ eEnter
          , (Vector.!) <$> current dOptions <@> eItemClicked
          ]
    let
      eChoice :: Event t (AtPath (Choice ChangeCode) a)
      eChoice =
        (\inputText (AtPath path (Option o)) ->
           case o of
             Editor.InsertVar -> AtPath path (Choice (Syntax.N inputText) o)
             Editor.InsertApp -> AtPath path (Choice () o)
             Editor.InsertLam -> AtPath path (Choice () o)
             Editor.InsertTVar -> AtPath path (Choice (Syntax.N inputText) o)
             Editor.InsertTArr -> AtPath path (Choice () o)
             Editor.InsertTForall -> AtPath path (Choice () o)
             Editor.Rename -> AtPath path (Choice (Syntax.N inputText) o)
        ) <$>
        current dInputText <@>
        eOption

    pure $ gate (current dInputValid) eChoice

menu ::
  ( MonadHold t m, DomBuilder t m
  , PostBuild t m, TriggerEvent t m
  , PerformEvent t m, MonadJSM (Performable m)
  , DomBuilderSpace m ~ GhcjsDomSpace
  , MonadJSM m, MonadFix m
  ) =>
  Event t () ->
  Event t () ->
  Event t () ->
  Event t () ->
  Dynamic t (Vector (AtPath (Option ChangeCode) a)) ->
  m (Dynamic t Bool, Event t (AtPath (Choice ChangeCode) a))
menu eOpen eClose eNextItem eEnter dOptions = do
  eAction <-
    fmap switchDyn . widgetHold (pure never) $
    leftmost
    [ menuForTarget eNextItem eEnter dOptions <$ eOpen
    , pure never <$ eClose
    ]
  dOpen <- holdDyn False $ leftmost [True <$ eOpen, False <$ eClose]
  pure (dOpen, eAction)

infoItem :: DomBuilder t m => Text -> Text -> m ()
infoItem left right =
  elAttr "div"
    ("class" =: "level" <>
     "style" =:
     ("border-bottom: 1px solid;" <>
      "margin-bottom: 0.75em;" <>
      "padding-bottom: 0.25em"
     )
    ) $ do
    elAttr "div" ("class" =: "level-left") $ do
      elAttr "div"
        ("class" =: ("level-item " <> Style.classes [Style.text]))
        (text left)
    elAttr "div" ("class" =: "level-right") $ do
      elAttr "div"
        ("class" =: ("level-item " <> Style.classes [Style.code]))
        (text right)

app ::
  forall t m.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  , PerformEvent t m, MonadJSM (Performable m)
  , HasDocument m, MonadJSM m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  m ()
app =
  elAttr "div" ("class" =: "columns" <> "style" =: "height: 100%") $ do
    inputs <- getInputs
    editor <-
      elAttr "div" ("class" =: Style.classes [Style.mainPanel]) $ do
        rec
          let
            eOpenMenu = gate (not <$> current dMenuOpen) (Input._iSpace inputs)
            eCloseMenu =
              leftmost
              [ gate (current dMenuOpen) (Input._iEscape inputs)
              , () <$ eMenuChoice
              ]
            eNextItem = gate (current dMenuOpen) (Input._iTab inputs)
            eSelectItem = gate (current dMenuOpen) (Input._iEnter inputs)
            dOptions = Editor._eChangeCodeOptions editor

          let
            eAction =
              leftmost
              [ Editor.ChangeCode <$> eMenuChoice
              , Editor.ChangeSelection . Editor.SetSelection <$> eNodeSelected
              ]
          editor <-
            Editor.editor
              (EditorInit
               { _eiCode = Syntax.Decls [Syntax.Decl "val" $ Syntax.Done Syntax.THole Syntax.Hole]
               }
              )
              (EditorControls
               { _ecAction = eAction
               }
              )
          dNodeInfo <-
            bindDynamicM
              (View.viewDecls
                 (Just <$> Editor._eSelection editor)
                 Path.empty
              )
              (Editor._eCode editor)
          let eNodeSelected = switchDyn $ View._nodeFocus <$> dNodeInfo

          (dMenuOpen, eMenuChoice) <- menu eOpenMenu eCloseMenu eNextItem eSelectItem dOptions
        pure editor
    let
      dCode = Editor._eCode editor
      dSelection = Editor._eSelection editor

      dTcRes ::
        Dynamic t
          (Either
             Typecheck.TypeError
             ((), Typecheck.TCState Decls)
          )
      dTcRes =
        flip runStateT Typecheck.emptyTCState .
        Typecheck.checkDecls
          (const Nothing)
          (const Nothing)
          Path.empty <$>
        dCode

      dSelectionInfo :: Dynamic t (m ())
      dSelectionInfo =
        (\(Selection (path :: Path Decls y)) tcRes ->
           case target @y of
             TargetTerm -> do
               infoItem "Form" "expr"
               case tcRes of
                 Left err ->
                   text $ Typecheck.printTypeError err
                 Right (_, st) -> do
                   let
                     ty =
                       case Path.Map.lookup path (Typecheck._tcInfo st) of
                         Nothing -> Text.pack $ "not found at: " <> show path
                         Just (Typecheck.TermInfo name t) ->
                           Syntax.printType name $
                           Syntax.substTMetas (Typecheck._tcSubst st) t
                   infoItem "Type" ty
             TargetType -> do
               infoItem "Form" "type"
               case tcRes of
                 Left err ->
                   text $ Typecheck.printTypeError err
                 Right (_, st) -> do
                   let
                     ki =
                       case Path.Map.lookup path (Typecheck._tcInfo st) of
                         Nothing -> Text.pack $ "not found at: " <> show path
                         Just (Typecheck.TypeInfo k) ->
                           Syntax.printKind $
                           Syntax.substKMetas (Typecheck._tcKindSubst st) k
                   infoItem "Kind" ki
             TargetName -> do
               infoItem "Form" "name"
             TargetDecl -> do
               infoItem "Form" "declaration"
             TargetDeclBody -> do
               infoItem "Form" "declaration body"
             TargetDecls -> do
               infoItem "Form" "declarations"
        ) <$>
        dSelection <*>
        dTcRes
    elAttr "div" ("class" =: Style.classes [Style.rightPanel]) $ do
      el "header" $ text "Info"
      elAttr "section" ("class" =: Style.classes [Style.code]) $ dyn_ dSelectionInfo
    pure ()
