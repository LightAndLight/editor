{-# language OverloadedStrings #-}
module View where

import qualified Bound
import Bound.Var (unvar)
import Data.Text (Text)
import Reflex (Dynamic)
import Reflex.Dom
  ( DomBuilder
  , elClass, text
  )

import Style (classes)
import qualified Style
import qualified Syntax

viewTerm ::
  DomBuilder t m =>
  (a -> Text) ->
  Syntax.Term a ->
  m ()
viewTerm name tm =
  case tm of
    Syntax.Hole ->
      elClass "span" "hole" $
      text "_"
    Syntax.Var a ->
      elClass "span" "var" $
      text (name a)
    Syntax.App a b ->
      elClass "span" "app" $ do
        viewTerm name a
        text " "
        viewTerm name b
    Syntax.Lam n e ->
      elClass "span" "lam" $ do
        text n
        viewTerm (unvar (\() -> n) name) $ Bound.fromScope e
