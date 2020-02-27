{-# language OverloadedStrings #-}
module App (app) where

import Control.Monad.Fix (MonadFix)
import Data.Void (absurd)
import Reflex.Dom

import Syntax

import View (viewTerm)

app :: (MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m) => m ()
app = do
  _ <- viewTerm id $ App (App (Var "f") (Var "x")) Hole
  pure ()
