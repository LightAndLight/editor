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
  m (Dynamic t Text)
menuInput = do
  (theInput, _) <-
    elAttr' "input"
      ("type" =: "text" <> "class" =: "input" <> "id" =: "blaaah")
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
  InsertVar :: Path a Name -> Name -> MenuAction a
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
    InsertVar _ n -> item $ unName n
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
          constDyn
          [ Annotate path
          , InsertApp path
          , InsertLam path
          , InsertLamAnn path
          ]
        TargetType ->
          pure $
          constDyn
          [ InsertTArr path
          ]
        TargetName ->
          pure $
            (\n ->
               [ InsertVar path $ N n
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
  m (Event t (MenuAction a))
menuForTarget eNextItem eEnter path =
  elAttr "div" ("style" =: "position: absolute" <> "class" =: "dropdown is-active") $
  elAttr "div" ("class" =: "dropdown-content") $ do
    dInputText <- elAttr "div" ("class" =: "dropdown-item") menuInput
    (dSelection, dItems) <- menuItems eNextItem dInputText path
    eItemClicked :: Event t Int <-
      fmap switchDyn $
      bindDynamicM
        (uncurry renderMenuActions)
        ((,) <$> dSelection <*> dItems)
    pure $
      leftmost
      [ (Vector.!) <$> current dItems <@> eItemClicked
      , (Vector.!) <$> current dItems <*> current dSelection <@ eEnter
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
  Dynamic t (Focus.Selection (Syntax.Term ty tm)) ->
  m (Dynamic t Bool, Event t (MenuAction (Syntax.Term ty tm)))
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

runAction :: MenuAction a -> (Focus.Selection a, a) -> (Focus.Selection a, a)
runAction action (Focus.Selection oldPath, old) =
  case action of
    InsertLam path ->
      case Edit.edit path targetInfo (Edit.InsertTerm (Syntax.Lam "x" $ lift Syntax.Hole) (Path.singleton Path.LamArg)) old of
        Left err -> Debug.traceShow err (Focus.Selection oldPath, old)
        Right (newPath, _, new) -> (Focus.Selection newPath, new)
    InsertLamAnn path ->
      case Edit.edit path targetInfo (Edit.InsertTerm (Syntax.LamAnn "x" Syntax.THole $ lift Syntax.Hole) (Path.singleton Path.LamAnnType)) old of
        Left err -> Debug.traceShow err (Focus.Selection oldPath, old)
        Right (newPath, _, new) -> (Focus.Selection newPath, new)
    InsertApp path ->
      case Edit.edit path targetInfo (Edit.InsertTerm (Syntax.App Syntax.Hole Syntax.Hole) (Path.singleton Path.AppL)) old of
        Left err -> Debug.traceShow err (Focus.Selection oldPath, old)
        Right (newPath, _, new) -> (Focus.Selection newPath, new)
    InsertVar path n ->
      case Edit.edit path targetInfo (Edit.ModifyName $ const n) old of
        Left err -> Debug.traceShow err (Focus.Selection oldPath, old)
        Right (newPath, _, new) -> (Focus.Selection newPath, new)
    Annotate (path :: Path a x) ->
      case targetInfo @x of
        TargetType -> error "todo: annotate type"
        TargetTerm ->
          case Edit.edit path targetInfo (Edit.ModifyTerm (`Syntax.Ann` Syntax.THole) $ Path.singleton Path.AnnR) old of
            Left err -> Debug.traceShow err (Focus.Selection oldPath, old)
            Right (newPath, _, new) -> (Focus.Selection newPath, new)
        TargetName ->
          case Path.viewr path of
            EmptyR -> (Focus.Selection oldPath, old)
            ps :> p ->
              case p of
                Path.TForallArg -> error "todo: annotate tvar"
                Path.LamAnnArg->
                  case Zipper.downTo ps $ Zipper.toZipper old of
                    Nothing -> (Focus.Selection oldPath, old)
                    Just z ->
                      case Zipper._focus z of
                        Syntax.LamAnn n _ body ->
                          let
                            new =
                              Zipper.fromZipper $
                              z { Zipper._focus = Syntax.LamAnn n THole body }
                            newPath = Path.snoc ps Path.LamAnnType
                          in
                            (Focus.Selection newPath, new)
                        _ -> undefined
                Path.LamArg ->
                  case Zipper.downTo ps $ Zipper.toZipper old of
                    Nothing -> (Focus.Selection oldPath, old)
                    Just z ->
                      case Zipper._focus z of
                        Syntax.Lam n body ->
                          let
                            new =
                              Zipper.fromZipper $
                              z { Zipper._focus = Syntax.LamAnn n THole body }
                            newPath = Path.snoc ps Path.LamAnnType
                          in
                            (Focus.Selection newPath, new)
                        _ -> undefined
    InsertTArr path ->
      case Edit.edit path targetInfo (Edit.InsertType (Syntax.TArr Syntax.THole Syntax.THole) (Path.singleton Path.TArrL)) old of
        Left err -> Debug.traceShow err (Focus.Selection oldPath, old)
        Right (newPath, _, new) -> (Focus.Selection newPath, new)
    DeleteTerm path ->
      case Edit.edit path TargetTerm Edit.DeleteTerm old of
        Left err -> Debug.traceShow err (Focus.Selection oldPath, old)
        Right (newPath, _, new) -> (Focus.Selection newPath, new)
    DeleteType path ->
      case Edit.edit path TargetType Edit.DeleteType old of
        Left err -> Debug.traceShow err (Focus.Selection oldPath, old)
        Right (newPath, _, new) -> (Focus.Selection newPath, new)
    Other{} -> (Focus.Selection oldPath, old)

app ::
  forall t m.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  , PerformEvent t m, MonadJSM (Performable m)
  , HasDocument m, MonadJSM m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  m ()
app = do
  inputs <- getInputs
  rec
    let
      eNextHole =
        (\(Focus.Selection p, a) ->
           case Focus.nextHole p a of
             Nothing -> (Focus.Selection p, a)
             Just p' -> (p', a)
        ) <$
        gate (not <$> current dMenuOpen) (_iTab inputs)
      ePrevHole =
        (\(Focus.Selection p, a) ->
           case Focus.prevHole p a of
             Nothing -> (Focus.Selection p, a)
             Just p' -> (p', a)
        ) <$
        gate (not <$> current dMenuOpen) (_iShiftTab inputs)
    dPathTerm <-
      foldDyn
        ($)
        (Focus.Selection Path.empty, App (App (Var "f") (Var "x")) Hole)
        (mergeWith (.)
         [ runAction <$> eMenuAction
         , runAction <$> eDeleteNode
         , eNextHole
         , ePrevHole
         , (\p (_, a) -> (p, a)) <$> eSelection
         ]
        )
    let dSelection = fst <$> dPathTerm
    let dTerm = snd <$> dPathTerm
    eSelection :: Event t (Focus.Selection (Syntax.Term Name Name)) <-
      fmap switchDyn $
      bindDynamicM
        (fmap View._nodeFocus . viewTerm id id empty (Just <$> dSelection))
        dTerm
    let
      eDeleteNode =
        attachWithMaybe
          (\(open, sel) _ -> do
             guard $ not open
             case sel of
               Focus.Selection (path :: Path (Syntax.Term Name Name) x) ->
                 case targetInfo @x of
                   TargetTerm -> Just $ DeleteTerm path
                   TargetType -> Just $ DeleteType path
                   TargetName -> Nothing
          )
          ((,) <$> current dMenuOpen <*> current dSelection)
          (_iDelete inputs)
    let
      eOpenMenu = _iSpace inputs
      eCloseMenu = _iEscape inputs <> void eSelection <> void eMenuAction
    (dMenuOpen, eMenuAction) <-
      menu eOpenMenu eCloseMenu (_iTab inputs) (_iEnter inputs) dSelection
    let
      dTcRes =
        flip runStateT Typecheck.emptyTCState .
        Typecheck.infer
          id
          id
          (const Nothing)
          (const Nothing)
          (const Nothing)
          (const Nothing)
          mempty
          Path.empty <$>
        dTerm
    dyn_ $
      (\case
         Left err ->
           el "div" . text . Text.pack $ show err
         Right (ty, st) -> do
           el "div" . text $ Syntax.printType id ty
           el "div" . View.viewHoles id $ Typecheck._tcHoles st
      ) <$>
      dTcRes
  pure ()
