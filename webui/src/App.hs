{-# language FlexibleContexts #-}
{-# language OverloadedStrings, RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}
module App (app) where

import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Trans.Class (lift)
import Data.Some (Some(..))
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Void (absurd)
import GHCJS.DOM.EventM (on, event, preventDefault)
import qualified GHCJS.DOM.GlobalEventHandlers as Events
import qualified JSDOM.Generated.KeyboardEvent as KeyboardEvent
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex.Dom hiding (preventDefault)

import Path (P(AppL), cons, empty)
import Syntax

import View (viewTerm)

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
      preventDefault
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
  rec
    dSelection <- holdDyn Nothing $ Just <$> eSelection
    (_, eSelection) <-
      viewTerm
        id
        empty
        dSelection
        (App (App (Var "f") (Var "x")) Hole)
  pure ()
