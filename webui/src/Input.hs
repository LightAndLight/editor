{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}
module Input where

import Control.Monad (when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans.Class (lift)
import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Set as Set
import GHCJS.DOM.EventM (on, event, preventDefault)
import qualified GHCJS.DOM.GlobalEventHandlers as Events
import qualified GHCJS.DOM.KeyboardEvent as KeyboardEvent
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex
import Reflex.Dom hiding (preventDefault)

keysDownUp ::
  forall t m.
  ( MonadHold t m, DomBuilder t m, MonadFix m
  , HasDocument m, MonadJSM m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  m (Event t Text, Event t Text)
keysDownUp = do
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
  pure (eKeyDown, eKeyUp)

keysHeld ::
  forall t m.
  ( MonadHold t m, DomBuilder t m, MonadFix m
  , HasDocument m, MonadJSM m, TriggerEvent t m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  Event t Text ->
  Event t Text ->
  m (Dynamic t (Set Text))
keysHeld eKeyDown eKeyUp = do
  rec
    dHeldKeys <-
      holdDyn Set.empty $
      leftmost
      [ flip Set.insert <$> current dHeldKeys <@> eKeyDown
      , flip Set.delete <$> current dHeldKeys <@> eKeyUp
      ]
  pure dHeldKeys

keyPressed ::
  Reflex t =>
  Event t Text ->
  Dynamic t (Set Text) ->
  Event t Text
keyPressed eKeyDown dKeysHeld =
  attachWithMaybe
    (\ks k ->
        if Set.member k ks
        then Nothing
        else Just k
    )
    (current dKeysHeld)
    eKeyDown

data Inputs t
  = Inputs
  { _iSpace :: Event t ()
  , _iEscape :: Event t ()
  , _iTab :: Event t ()
  , _iShiftTab :: Event t ()
  , _iEnter :: Event t ()
  , _iDelete :: Event t ()
  }

getInputs ::
  ( MonadHold t m
  , DomBuilder t m, DomBuilderSpace m ~ GhcjsDomSpace
  , TriggerEvent t m
  , HasDocument m
  , MonadFix m, MonadJSM m
  ) =>
  m (Inputs t)
getInputs = do
  (eKeyDown, eKeyUp) <- keysDownUp
  dKeysHeld <- keysHeld eKeyDown eKeyUp
  let
    dShiftMod =
      (\ks -> "ShiftLeft" `Set.member` ks || "ShiftRight" `Set.member` ks) <$>
      dKeysHeld
    eKeyPressed = keyPressed eKeyDown dKeysHeld
  pure $
    Inputs
    { _iSpace =
        fmapMaybe (\case; "Space" -> Just (); _ -> Nothing) eKeyPressed
    , _iEscape =
        fmapMaybe (\case; "Escape" -> Just (); _ -> Nothing) eKeyPressed
    , _iTab =
        gate (not <$> current dShiftMod) $
        fmapMaybe (\case; "Tab" -> Just (); _ -> Nothing) eKeyPressed
    , _iShiftTab =
        gate (current dShiftMod) $
        fmapMaybe (\case; "Tab" -> Just (); _ -> Nothing) eKeyPressed
    , _iEnter =
        fmapMaybe (\case; "Enter" -> Just (); _ -> Nothing) eKeyPressed
    , _iDelete =
        fmapMaybe (\case; "Delete" -> Just (); _ -> Nothing) eKeyPressed
    }
