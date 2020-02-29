{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
module View where

import qualified Bound
import Bound.Var (unvar)
import Control.Monad.Fix (MonadFix)
import Data.Text (Text)
import Data.Some (Some(..))
import Reflex
import Reflex.Dom

import Path (Path, P(..), ViewL(..), viewl)
import Style (classes)
import qualified Style
import qualified Syntax

type Selection a = Some (Path (Syntax.Term a))

viewTerm ::
  (MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m) =>
  (a -> Text) ->
  Maybe (Selection a) ->
  Syntax.Term a ->
  m (Dynamic t Bool)
viewTerm name mSelection tm = do
  rec
    let eMouseEnter = domEvent Mouseenter e
    let eMouseLeave = domEvent Mouseleave e
    dThisHovered <- holdDyn False $ leftmost [True <$ eMouseEnter, False <$ eMouseLeave]
    dHoverStyle <- holdUniqDyn $ (\a b -> a && not b) <$> dThisHovered <*> dChildHovered
    let
      selected =
        case mSelection of
          Nothing -> False
          Just (Some path) ->
            case viewl path of
              EmptyL -> True
              _ :< _ -> False
    (e, dChildHovered) <-
      elDynClass'
        "span"
        (fmap
           (\hovered ->
              classes $
              [ Style.focusable, Style.node ] <>
              [ Style.selected | selected ] <>
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
          dH1 <-
            viewTerm
              name
              (mSelection >>=
               \(Some f) -> case viewl f of
                 AppL :< rest -> Just (Some rest)
                 _ -> Nothing
              )
              a
          dH2 <-
            viewTerm
              name
              (mSelection >>=
               \(Some f) -> case viewl f of
                 AppR :< rest -> Just (Some rest)
                 _ -> Nothing
              )
              b
          holdUniqDyn $ (||) <$> dH1 <*> dH2
        Syntax.Lam n e -> do
          text n
          dH1 <-
            viewTerm
              (unvar (\() -> n) name)
              (mSelection >>=
               \(Some f) -> case viewl f of
                LamBody :< rest -> Just (Some rest)
                _ -> Nothing)
              (Bound.fromScope e)
          pure dH1
  holdUniqDyn $ (||) <$> dThisHovered <*> dChildHovered
