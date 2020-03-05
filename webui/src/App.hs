{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedLists, OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}
module App (app) where

import qualified Debug.Trace as Debug

import Control.Monad (when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Trans.Class (lift)
import Data.Foldable (traverse_)
import Data.Functor (void)
import Data.Some (Some(..))
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Type.Equality ((:~:)(..))
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (absurd)
import GHCJS.DOM.EventM (on, event, preventDefault)
import GHCJS.DOM.HTMLElement (HTMLElement)
import qualified GHCJS.DOM.HTMLElement as HTMLElement
import qualified GHCJS.DOM.GlobalEventHandlers as Events
import qualified JSDOM.Generated.KeyboardEvent as KeyboardEvent
import JSDOM.Types (liftJSM, toJSVal, fromJSValUnchecked)
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex.Dom hiding (preventDefault)

import qualified Edit
import Path (Path, TargetInfo(..), targetInfo, cons, empty)
import qualified Style
import Syntax
import View (viewTerm)
import qualified View

keyPressed ::
  forall t m.
  ( MonadHold t m, DomBuilder t m, MonadFix m
  , HasDocument m, MonadJSM m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  m (Event t Text)
keyPressed = do
  document <- askDocument
  let ctrl :: [Text] = ["Tab", "Enter"]
  eKeyDown :: Event t Text <-
    wrapDomEvent document (`on` Events.keyDown) $ do
      ev <- event
      code <- lift (KeyboardEvent.getCode ev)
      when (code `elem` ctrl) preventDefault
      pure code
  eKeyUp :: Event t Text <-
    wrapDomEvent document (`on` Events.keyUp) $ do
      ev <- event
      code <- lift (KeyboardEvent.getCode ev)
      when (code `elem` ctrl) preventDefault
      pure code
  rec
    bHeldKeys <-
      hold Set.empty $
      leftmost
      [ flip Set.insert <$> bHeldKeys <@> eKeyDown
      , flip Set.delete <$> bHeldKeys <@> eKeyUp
      ]
  let
    eKeyPressed =
      attachWithMaybe
        (\ks k ->
           if Set.member k ks
           then Nothing
           else Just k
        )
        bHeldKeys
        eKeyDown
  pure eKeyPressed

menuInput ::
  ( DomBuilder t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  , PostBuild t m, TriggerEvent t m
  , PerformEvent t m, MonadJSM (Performable m)
  , MonadJSM m
  ) =>
  m ()
menuInput = do
  (theInput, _) <-
    elAttr' "input"
      ("type" =: "text" <> "class" =: "input" <> "id" =: "blaaah")
      (pure ())
  ePostBuild <- delay 0.05 =<< getPostBuild
  performEvent_ $
    (do
       inputElement :: HTMLElement <-
         liftJSM $
         fromJSValUnchecked =<< toJSVal (_element_raw theInput)
       HTMLElement.focus inputElement
    ) <$
    ePostBuild

data MenuAction a where
  InsertLam :: Path a (Term v) -> TargetInfo (Term v) -> MenuAction a
  InsertApp :: Path a (Term v) -> TargetInfo (Term v) -> MenuAction a
  Other :: Text -> MenuAction a

renderMenuAction ::
  DomBuilder t m =>
  Bool ->
  MenuAction a ->
  m (Event t ())
renderMenuAction selected action =
  case action of
    InsertLam{} -> item "\\x -> _"
    InsertApp{} -> item "_ _"
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
  (MonadHold t m, DomBuilder t m, MonadFix m) =>
  Event t () ->
  Path a b ->
  TargetInfo b ->
  m (Dynamic t Int, Dynamic t (Vector (MenuAction a)))
menuItems eNextItem path info = do
  rec
    dSelection :: Dynamic t Int <-
      holdDyn 0 $
      leftmost
      [ (\n items -> (n + 1) `mod` Vector.length items) <$>
        current dSelection <*>
        current dItems <@ eNextItem
      ]
    dItems <-
      case info of
        TargetTerm ->
          pure $ constDyn [InsertApp path info, InsertLam path info]
        TargetType ->
          pure $ constDyn [Other "thing4", Other "thing5", Other "thing6"]
        TargetIdent ->
          pure $ constDyn [Other "thing7", Other "thing7", Other "thing9"]
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
  Event t () ->
  Event t () ->
  Path a b ->
  TargetInfo b ->
  m (Event t (MenuAction a))
menuForTarget eNextItem eEnter path target =
  elAttr "div" ("style" =: "position: absolute" <> "class" =: "dropdown is-active") $
  elAttr "div" ("class" =: "dropdown-content") $ do
    elAttr "div" ("class" =: "dropdown-item") menuInput
    (dSelection, dItems) <- menuItems eNextItem path target
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
  Dynamic t (Maybe (View.Selection (Syntax.Term a))) ->
  m (Event t (MenuAction (Syntax.Term a)))
menu eOpen eClose eNextItem eEnter dSelection =
  fmap switchDyn . widgetHold (pure never) $
  leftmost
  [ maybe
      (pure never)
      (\(Some path) ->
         case targetInfo path of
           Left Refl ->
             undefined
           Right target ->
             menuForTarget eNextItem eEnter path target
      ) <$>
    current dSelection <@ eOpen
  , pure never <$ eClose
  ]

app ::
  forall t m.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  , PerformEvent t m, MonadJSM (Performable m)
  , HasDocument m, MonadJSM m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  m ()
app = do
  eKeyPressed <- keyPressed
  let
    eSpace =
      fmapMaybe (\case; "Space" -> Just (); _ -> Nothing) eKeyPressed
    eEscape =
      fmapMaybe (\case; "Escape" -> Just (); _ -> Nothing) eKeyPressed
    eNextItem =
      fmapMaybe (\case; "Tab" -> Just (); _ -> Nothing) eKeyPressed
    eEnter =
      fmapMaybe (\case; "Enter" -> Just (); _ -> Nothing) eKeyPressed
  rec
    dTerm <-
      holdDyn
        (App (App (Var "f") (Var "x")) Hole)
        ((\old action ->
            case action of
              InsertLam path info ->
                case Edit.edit path info (Edit.InsertTerm (Syntax.Lam "x" $ lift Syntax.Hole) Path.empty) old of
                  Left err -> Debug.traceShow err old
                  Right (_, _, new) -> new
              InsertApp path info ->
                case Edit.edit path info (Edit.InsertTerm (Syntax.App Syntax.Hole Syntax.Hole) Path.empty) old of
                  Left err -> Debug.traceShow err old
                  Right (_, _, new) -> new
              Other{} -> old
         ) <$>
         current dTerm <@>
         eMenuAction
        )
    dSelection <- holdDyn Nothing $ Just <$> eSelection
    eSelection :: Event t (View.Selection (Syntax.Term Text)) <-
      fmap switchDyn $
      bindDynamicM
        (fmap snd . viewTerm id empty dSelection)
        dTerm
    let
      eOpenMenu = eSpace
      eCloseMenu = eEscape <> void eSelection <> void eMenuAction
    eMenuAction <- menu eOpenMenu eCloseMenu eNextItem eEnter dSelection
  pure ()
