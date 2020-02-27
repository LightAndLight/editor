{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
module View where

import qualified Bound
import Bound.Var (unvar)
import Control.Monad.Fix (MonadFix)
import Data.Text (Text)
import Reflex
import Reflex.Dom

import Style (classes)
import qualified Style
import qualified Syntax

viewTerm ::
  (MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m) =>
  (a -> Text) ->
  Syntax.Term a ->
  m ()
viewTerm name tm = do
  rec
    (e, _) <-
      elDynClass'
        "span"
        (fmap
           (\hovered -> classes $ [Style.focusable, Style.node] <> [ Style.hovered | hovered ])
           dHovered
        ) $
      case tm of
        Syntax.Hole ->
          text "_"
        Syntax.Var a ->
          text (name a)
        Syntax.App a b -> do
          viewTerm name a
          text " "
          viewTerm name b
        Syntax.Lam n e -> do
          text n
          viewTerm (unvar (\() -> n) name) $ Bound.fromScope e
    let eMouseEnter = domEvent Mouseenter e
    let eMouseLeave = domEvent Mouseleave e
    dHovered <- holdDyn False $ leftmost [True <$ eMouseEnter, False <$ eMouseLeave]
  pure ()
