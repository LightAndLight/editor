{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings, RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}
module App (app) where

import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Trans.Class (lift)
import Data.Functor (void)
import Data.Some (Some(..))
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Void (absurd)
import GHCJS.DOM.EventM (on, event, preventDefault)
import qualified GHCJS.DOM.GlobalEventHandlers as Events
import qualified JSDOM.Generated.KeyboardEvent as KeyboardEvent
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex.Dom hiding (preventDefault)

import Path (P(AppL), TargetInfo(..), targetInfo, cons, empty)
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
  eKeyDown :: Event t Text <-
    wrapDomEvent document (`on` Events.keyDown) $ do
      ev <- event
      lift (KeyboardEvent.getCode ev)
  eKeyUp :: Event t Text <-
    wrapDomEvent document (`on` Events.keyUp) $ do
      ev <- event
      lift (KeyboardEvent.getCode ev)
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

menuInput :: DomBuilder t m => m ()
menuInput =
  elAttr "input"
    ("type" =: "text" <> "class" =: "input")
    (pure ())

menu ::
  (MonadHold t m, DomBuilder t m) =>
  Event t () ->
  Event t () ->
  Dynamic t (Maybe (View.Selection (Syntax.Term a))) ->
  m ()
menu eOpen eClose dSelection =
  widgetHold_ (pure ()) $
  leftmost
  [ maybe
      (pure ())
      (\(Some path) ->
         case targetInfo path of
           Nothing -> undefined
           Just tInfo ->
             elAttr "div" ("style" =: "position: absolute" <> "class" =: "box") $ do
               el "div" menuInput
               text $ case tInfo of
                 TargetTerm -> "term menu"
                 TargetType -> "type menu"
                 TargetIdent -> "ident menu"
      ) <$>
    current dSelection <@ eOpen
  , pure () <$ eClose
  ]

app ::
  forall t m.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  , PerformEvent t m, MonadIO (Performable m)
  , HasDocument m, MonadJSM m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  m ()
app = do
  eKeyPressed <- keyPressed
  let
    eSpace = fmapMaybe (\case; "Space" -> Just (); _ -> Nothing) eKeyPressed
    eEscape = fmapMaybe (\case; "Escape" -> Just (); _ -> Nothing) eKeyPressed
  rec
    dSelection <- holdDyn Nothing $ Just <$> eSelection
    (_, eSelection) <-
      viewTerm
        id
        empty
        dSelection
        (App (App (Var "f") (Var "x")) Hole)
  let
    eOpenMenu = eSpace
    eCloseMenu = eEscape <> void eSelection
  menu eOpenMenu eCloseMenu dSelection
  pure ()
