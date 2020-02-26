{-# language OverloadedStrings #-}
module App (app) where

import Data.Void (absurd)
import Reflex.Dom (DomBuilder)
import qualified Reflex.Dom as Dom

import Syntax

import View (viewTerm)

app :: DomBuilder t m => m ()
app = viewTerm id $ App (App (Var "f") (Var "x")) Hole
