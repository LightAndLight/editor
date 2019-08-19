{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}
module Main where

import Control.Monad (guard)
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (MonadReader, runReaderT, ask)
import Data.Functor.Identity (Identity(..))
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Map (Map)
import Data.String (fromString)
import Data.Text (Text)
import GHCJS.DOM.KeyboardEvent (getKey)
import JSDOM.EventM (event, on)
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex
import Reflex.Dom
import Reflex.Network

import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import qualified GHCJS.DOM.GlobalEventHandlers as Event

newtype ID = ID Int
  deriving (Eq, Ord, Show)

data Expr f
  = Var (f String)
  | Hole
  | App (f (Expr f)) (f (Expr f))
  | Lam (f String) (f (Expr f))

data D t a = D ID (Dynamic t a)

fresh :: (MonadReader (IORef ID) m, MonadIO m) => m ID
fresh = do
  ref <- ask
  liftIO $ do
    ID n <- readIORef ref
    ID n <$ writeIORef ref (ID $ n+1)

mkD :: (Reflex t, MonadReader (IORef ID) m, MonadIO m) => Expr Identity -> m (Expr (D t))
mkD ex =
  case ex of
    Var (Identity name) -> do
      n <- fresh
      pure . Var $ D n (pure name)
    Hole -> pure Hole
    App (Identity f) (Identity x) -> do
      n1 <- fresh
      n2 <- fresh
      f' <- mkD f
      x' <- mkD x
      pure $ App (D n1 $ pure f') (D n2 $ pure x')
    Lam (Identity name) (Identity e) -> do
      n1 <- fresh
      n2 <- fresh
      e' <- mkD e
      pure $ Lam (D n1 $ pure name) (D n2 $ pure e')

data Edit
  = MkApp

mkExpr ::
  (Reflex t, MonadHold t m, MonadFix m, Adjustable t m, MonadReader (IORef ID) m, MonadIO m) =>
  ID ->
  Expr Identity ->
  Event t (Map ID Edit) ->
  m (Dynamic t (Expr (D t)))
mkExpr i initial eEdits = do
  rec
    dExpr <-
      networkHold (mkD initial) $
      (\ex edit ->
        case edit of
          MkApp ->
            case ex of
              Hole -> do
                n1 <- fresh
                n2 <- fresh
                h1 <- mkExpr n1 Hole eEdits
                h2 <- mkExpr n2 Hole eEdits
                pure $ App (D n1 h1) (D n2 h2)
              _ -> pure ex) <$>
      current dExpr <@>
      fmapMaybe (Map.lookup i) eEdits
  pure dExpr

renderExpr :: (DomBuilder t m, PostBuild t m) => ID -> Dynamic t (Expr (D t)) -> m ()
renderExpr i dExpr =
  elAttr "span" ("id" =: fromString (show i)) .
  dyn_ $ do
    expr <- dExpr
    pure $
      case expr of
        Var (D _ dName) -> dynText $ fromString <$> dName
        Hole -> text "_"
        App (D fi dF) (D xi dX) -> do
          renderExpr fi dF
          text " "
          renderExpr xi dX
        Lam (D _ dName) (D ei dE) -> do
          text "\\"
          dynText $ fromString <$> dName
          text " -> "
          renderExpr ei dE

documentKey ::
  ( Reflex t, HasDocument m, TriggerEvent t m, MonadJSM m
  , DomBuilderSpace m ~ GhcjsDomSpace
  ) =>
  Text -> m (Event t ())
documentKey k' = do
  document <- askDocument
  fmapMaybe (\k -> guard $ k == k') <$>
    wrapDomEvent document (`on` Event.keyDown) (getKey =<< event)

headWidget :: DomBuilder t m => m ()
headWidget = do
  el "title" $ text "Testing"
  el "style" $ text "html { font-family: monospace; }"

main :: IO ()
main = do
  mainWidgetWithHead headWidget $ do
    ref <- liftIO $ newIORef (ID 0)
    flip runReaderT ref $ do
      n <- fresh
      eKeyA <- documentKey "a"
      dCursor <- pure $ constDyn n
      ex <-
        mkExpr n Hole $
        (\i -> Map.singleton i MkApp) <$> current dCursor <@ eKeyA
      renderExpr n ex
