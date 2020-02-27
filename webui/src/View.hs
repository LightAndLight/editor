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
  m (Dynamic t Bool)
viewTerm name tm = do
  rec
    let eMouseEnter = domEvent Mouseenter e
    let eMouseLeave = domEvent Mouseleave e
    dThisHovered <- holdDyn False $ leftmost [True <$ eMouseEnter, False <$ eMouseLeave]
    dHoverStyle <- holdUniqDyn $ (\a b -> a && not b) <$> dThisHovered <*> dChildHovered
    (e, dChildHovered) <-
      elDynClass'
        "span"
        (fmap
           (\hovered ->
              classes $
              [ Style.focusable, Style.node ] <>
              [ Style.hovered | hovered ] <>
              case tm of
                Syntax.Hole{} -> [ Style.leaf ]
                Syntax.Var{} -> [ Style.leaf ]
                _ -> []
           )
           dHoverStyle
        ) $
      case tm of
        Syntax.Hole -> do
          text "_"
          pure $ constDyn False
        Syntax.Var a -> do
          text (name a)
          pure $ constDyn False
        Syntax.App a b -> do
          dH1 <- viewTerm name a
          dH2 <- viewTerm name b
          holdUniqDyn $ (||) <$> dH1 <*> dH2
        Syntax.Lam n e -> do
          text n
          dH1 <- viewTerm (unvar (\() -> n) name) $ Bound.fromScope e
          pure dH1
  holdUniqDyn $ (||) <$> dThisHovered <*> dChildHovered
