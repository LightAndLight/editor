{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedLists, OverloadedStrings #-}
{-# language PackageImports #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables, TypeApplications #-}
{-# language TypeFamilies #-}
module App (app) where

import qualified Debug.Trace as Debug

import Control.Monad (guard)
import Control.Monad.Fix (MonadFix)
import Control.Monad.State (runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Foldable (foldl')
import Data.Functor (void)
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

import qualified Edit
import qualified Focus
import Path (Path, TargetInfo(..), HasTargetInfo, ViewR(..), targetInfo, empty)
import qualified Path
import qualified Path.Map
import Syntax
import qualified Typecheck
import qualified Zipper

import Input (Inputs(..), getInputs)
import qualified Style
import View (viewTerm)
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
                  target :: HTMLInputElement <-
                    liftJSM $ fromJSValUnchecked =<< toJSVal t
                  Just <$> HTMLInputElement.getValue target
           )
      ) <$
      ePostBuild
  holdDyn "" $ fmapMaybe id eUpdated

data MenuAction a where
  InsertLam :: Path a (Term ty tm) -> MenuAction a
  InsertLamAnn :: Path a (Term ty tm) -> MenuAction a
  InsertApp :: Path a (Term ty tm) -> MenuAction a
  InsertVar :: Path a (Term ty tm) -> Name -> MenuAction a
  InsertName :: Path a Name -> Name -> MenuAction a
  InsertTArr :: Path a (Type ty) -> MenuAction a
  Annotate :: HasTargetInfo b => Path a b -> MenuAction a

  DeleteTerm :: Path a (Term ty tm) -> MenuAction a
  DeleteType :: Path a (Type ty) -> MenuAction a

  Other :: Text -> MenuAction a

renderMenuAction ::
  DomBuilder t m =>
  Bool ->
  MenuAction a ->
  m (Event t ())
renderMenuAction selected action =
  case action of
    InsertLam{} -> item "\\x -> _"
    InsertLamAnn{} -> item "\\(x : _) -> _"
    InsertApp{} -> item "_ _"
    InsertVar{} -> item "variable"
    InsertName _ n -> item $ unName n
    Annotate{} -> item "□ : _"
    InsertTArr{} -> item "_ -> _"
    DeleteTerm{} -> item "_"
    DeleteType{} -> item "_"
    Other str -> item str
  where
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

menuItems ::
  forall t m a b.
  (MonadHold t m, DomBuilder t m, MonadFix m) =>
  HasTargetInfo b =>
  Event t () ->
  Dynamic t Text ->
  Path a b ->
  m (Dynamic t Int, Dynamic t (Vector (MenuAction a)))
menuItems eNextItem dInputText path = do
  rec
    dSelection :: Dynamic t Int <-
      holdDyn 0 $
      leftmost
      [ (\n items -> (n + 1) `mod` Vector.length items) <$>
        current dSelection <*>
        current dItems <@ eNextItem
      ]
    dItems <-
      case targetInfo @b of
        TargetTerm ->
          pure $
            (\n ->
             [ Annotate path
             , InsertApp path
             , InsertLam path
             , InsertLamAnn path
             , InsertVar path $ N n
             ]
            ) <$>
            dInputText
        TargetType ->
          pure $
          constDyn
          [ InsertTArr path
          ]
        TargetName ->
          pure $
            (\n ->
               [ InsertName path $ N n
               , Annotate path
               ]
            ) <$>
            dInputText
  pure (dSelection, dItems)

renderMenuActions ::
  DomBuilder t m =>
  Int ->
  Vector (MenuAction a) ->
  m (Event t Int)
renderMenuActions selected =
  Vector.ifoldr
    (\ix a rest -> do
       e <- renderMenuAction (ix == selected) a
       es <- rest
       pure $ leftmost [ix <$ e, es]
    )
    (pure never)

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
  forall t m a b.
  ( MonadHold t m, DomBuilder t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  , PostBuild t m, TriggerEvent t m
  , PerformEvent t m, MonadJSM (Performable m)
  , MonadJSM m, MonadFix m
  ) =>
  HasTargetInfo b =>
  Event t () ->
  Event t () ->
  Path a b ->
  m (Event t [MenuAction a])
menuForTarget eNextItem eEnter path =
  elAttr "div" ("class" =: "dropdown is-active") $
  elAttr "div" ("class" =: "dropdown-content") $ do
    rec
      dInputText <- elAttr "div" ("class" =: "dropdown-item") $ menuInput dInputValid
      let
        dInputValid =
          (\sel txt ->
             case sel of
               InsertVar{} -> not $ Text.null txt
               _ -> True
          ) <$>
          dAction <*>
          dInputText
      (dSelection, dItems) <- menuItems eNextItem dInputText path
      let dAction = (Vector.!) <$> dItems <*> dSelection
    eItemClicked :: Event t Int <-
      fmap switchDyn $
      bindDynamicM
        (uncurry renderMenuActions)
        ((,) <$> dSelection <*> dItems)
    pure .
      fmap (\x -> [x]) .
      gate (current dInputValid) $
      leftmost
      [ (Vector.!) <$> current dItems <@> eItemClicked
      , current dAction <@ eEnter
      ]

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
  Dynamic t (Focus.Selection Decls) ->
  m (Dynamic t Bool, Event t [MenuAction Decls])
menu eOpen eClose eNextItem eEnter dSelection = do
  eAction <-
    fmap switchDyn . widgetHold (pure never) $
    leftmost
    [ (\(Focus.Selection path) -> menuForTarget eNextItem eEnter path) <$>
      current dSelection <@ eOpen
    , pure never <$ eClose
    ]
  dOpen <- holdDyn False $ leftmost [True <$ eOpen, False <$ eClose]
  pure (dOpen, eAction)

runAction ::
  HasTargetInfo a =>
  MenuAction a ->
  EditorState a ->
  EditorState a
runAction action es =
  case action of
    InsertLam path ->
      case Edit.edit path targetInfo (Edit.InsertTerm (Syntax.Lam "x" $ lift Syntax.Hole) (Path.singleton Path.LamArg)) (_esContent es) of
        Left err -> Debug.traceShow err es
        Right (newPath, _, new) ->
          es
          { _esSelection = Focus.Selection newPath
          , _esContent = new
          }
    InsertLamAnn path ->
      case Edit.edit path targetInfo (Edit.InsertTerm (Syntax.LamAnn "x" Syntax.THole $ lift Syntax.Hole) (Path.singleton Path.LamAnnType)) (_esContent es) of
        Left err -> Debug.traceShow err es
        Right (newPath, _, new) ->
          es
          { _esSelection = Focus.Selection newPath
          , _esContent = new
          }
    InsertApp path ->
      case Edit.edit path targetInfo (Edit.InsertTerm (Syntax.App Syntax.Hole Syntax.Hole) (Path.singleton Path.AppL)) (_esContent es) of
        Left err -> Debug.traceShow err es
        Right (newPath, _, new) ->
          es
          { _esSelection = Focus.Selection newPath
          , _esContent = new
          }
    InsertName path n ->
      case Edit.edit path targetInfo (Edit.ModifyName $ const n) (_esContent es) of
        Left err -> Debug.traceShow err es
        Right (newPath, _, new) ->
          es
          { _esSelection = Focus.Selection newPath
          , _esContent = new
          }
    InsertVar path n ->
      case Edit.edit path targetInfo (Edit.InsertVar n) (_esContent es) of
        Left err -> Debug.traceShow err es
        Right (newPath, _, new) ->
          case Focus.nextHole newPath new of
            Nothing ->
              es
              { _esSelection = Focus.Selection newPath
              , _esContent = new
              }
            Just newPath' ->
              es
              { _esSelection = newPath'
              , _esContent = new
              }
    Annotate (path :: Path a x) ->
      case targetInfo @x of
        TargetType -> error "todo: annotate type"
        TargetTerm ->
          case Edit.edit path targetInfo (Edit.ModifyTerm (`Syntax.Ann` Syntax.THole) $ Path.singleton Path.AnnR) (_esContent es) of
            Left err -> Debug.traceShow err es
            Right (newPath, _, new) ->
              es
              { _esSelection = Focus.Selection newPath
              , _esContent = new
              }
        TargetName ->
          case Path.viewr path of
            EmptyR -> es
            ps :> p ->
              case p of
                Path.DName -> error "todo: annotate DName"
                Path.TForallArg -> error "todo: annotate TForallArg"
                Path.LamAnnArg->
                  case Zipper.downTo ps $ Zipper.toZipper (_esContent es) of
                    Nothing -> es
                    Just z ->
                      case Zipper._focus z of
                        Syntax.LamAnn n _ body ->
                          let
                            new =
                              Zipper.fromZipper $
                              z { Zipper._focus = Syntax.LamAnn n THole body }
                            newPath = Path.snoc ps Path.LamAnnType
                          in
                            es
                            { _esSelection = Focus.Selection newPath
                            , _esContent = new
                            }
                        _ -> undefined
                Path.LamArg ->
                  case Zipper.downTo ps $ Zipper.toZipper (_esContent es) of
                    Nothing -> es
                    Just z ->
                      case Zipper._focus z of
                        Syntax.Lam n body ->
                          let
                            new =
                              Zipper.fromZipper $
                              z { Zipper._focus = Syntax.LamAnn n THole body }
                            newPath = Path.snoc ps Path.LamAnnType
                          in
                            es
                            { _esSelection = Focus.Selection newPath
                            , _esContent = new
                            }
                        _ -> undefined
    InsertTArr path ->
      case Edit.edit path targetInfo (Edit.InsertType (Syntax.TArr Syntax.THole Syntax.THole) (Path.singleton Path.TArrL)) (_esContent es) of
        Left err -> Debug.traceShow err es
        Right (newPath, _, new) ->
          es
          { _esSelection = Focus.Selection newPath
          , _esContent = new
          }
    DeleteTerm path ->
      case Edit.edit path TargetTerm Edit.DeleteTerm (_esContent es) of
        Left err -> Debug.traceShow err es
        Right (newPath, _, new) ->
          es
          { _esSelection = Focus.Selection newPath
          , _esContent = new
          }
    DeleteType path ->
      case Edit.edit path TargetType Edit.DeleteType (_esContent es) of
        Left err -> Debug.traceShow err es
        Right (newPath, _, new) ->
          es
          { _esSelection = Focus.Selection newPath
          , _esContent = new
          }
    Other{} -> es

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

data EditorState a
  = EditorState
  { _esSelection :: Focus.Selection a
  , _esContent :: a
  }

mkEditorState ::
  ( HasTargetInfo a
  , Reflex t, MonadHold t m, MonadFix m
  ) =>
  EditorState a ->
  Inputs t ->
  Event t (Focus.Selection a) ->
  Event t [MenuAction a] ->
  Dynamic t Bool ->
  m (Dynamic t (EditorState a))
mkEditorState initial inputs eSelection eMenuActions dMenuOpen = do
  let
    eNextHole =
      (\es ->
        case _esSelection es of
          Focus.Selection p ->
            case Focus.nextHole p (_esContent es) of
              Nothing -> es
              Just p' -> es { _esSelection = p' }
      ) <$
      gate (not <$> current dMenuOpen) (_iTab inputs)
    ePrevHole =
      (\es ->
        case _esSelection es of
          Focus.Selection p ->
            case Focus.prevHole p (_esContent es) of
              Nothing -> es
              Just p' -> es { _esSelection = p' }
      ) <$
      gate (not <$> current dMenuOpen) (_iShiftTab inputs)
  foldDyn
    ($)
    initial
    (mergeWith (.)
      [ (\acts es -> foldl' (flip runAction) es acts) <$> eMenuActions
      , eNextHole
      , ePrevHole
      , (\p es -> es { _esSelection = p }) <$> eSelection
      ]
    )

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
    (dTerm, dSelection) <-
      elAttr "div" ("class" =: Style.classes [Style.mainPanel]) $ do
        rec
          let eMenuActions = eMenuAction <> eDeleteNode
          dEditorState :: Dynamic t (EditorState Decls)<-
            mkEditorState
              (EditorState
               { _esSelection =
                 Focus.Selection $
                 Path.singleton (Path.Decl 0)
               , _esContent =
                 Syntax.Decls
                 [ Syntax.Decl (Syntax.N "val") Syntax.THole Syntax.Hole
                 ]
               }
              )
              inputs
              eSelection
              eMenuActions
              dMenuOpen
          let dSelection = _esSelection <$> dEditorState
          let dTerm = _esContent <$> dEditorState
          eSelection :: Event t (Focus.Selection Decls) <-
            fmap switchDyn $
            bindDynamicM
              (fmap View._nodeFocus .
               viewDecls (Just <$> dSelection)
              )
              dTerm
          let
            eDeleteNode =
              attachWithMaybe
                (\(open, sel) _ -> do
                  guard $ not open
                  case sel of
                    Focus.Selection (path :: Path Decls x) ->
                      case targetInfo @x of
                        TargetTerm -> Just [DeleteTerm path]
                        TargetType -> Just [DeleteType path]
                        TargetName -> Nothing
                )
                ((,) <$> current dMenuOpen <*> current dSelection)
                (_iDelete inputs)
          let
            eOpenMenu = _iSpace inputs
            eCloseMenu = _iEscape inputs <> void eSelection <> void eMenuAction
          (dMenuOpen, eMenuAction) <-
            menu eOpenMenu eCloseMenu (_iTab inputs) (_iEnter inputs) dSelection
        pure (dTerm, dSelection)
    let
      dTcRes ::
        Dynamic t
          (Either
             Typecheck.TypeError
             (Type Name, Typecheck.TCState Name Name)
          )
      dTcRes =
        flip runStateT Typecheck.emptyTCState .
        Typecheck.infer
          (Typecheck.TCEnv
           { Typecheck._teName = id
           , Typecheck._teNameTy = id
           , Typecheck._teGlobalCtx = const Nothing
           , Typecheck._teCtx = const Nothing
           , Typecheck._teGlobalTyCtx = const Nothing
           , Typecheck._teTyCtx = const Nothing
           , Typecheck._teBoundTyVars = mempty
           , Typecheck._tePath = Path.empty
           }
          ) <$>
        dTerm

      dSelectionInfo :: Dynamic t (m ())
      dSelectionInfo =
        (\(Focus.Selection (path :: Path Decls y)) tcRes ->
           case targetInfo @y of
             TargetTerm -> do
               infoItem "Form" "expr"
               case tcRes of
                 Left err ->
                   text . Text.pack $ show err
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
                   text . Text.pack $ show err
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
        ) <$>
        dSelection <*>
        dTcRes
    elAttr "div" ("class" =: Style.classes [Style.rightPanel]) $ do
      el "header" $ text "Info"
      elAttr "section" ("class" =: Style.classes [Style.code]) $
        dyn_ dSelectionInfo
    pure ()
