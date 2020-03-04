{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
module View where

import qualified Bound
import Bound.Var (unvar)
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Text (Text)
import Data.Some (Some(..))
import Reflex
import Reflex.Dom

import Path (Path, P(..), ViewL(..), viewl, snoc, empty)
import Style (classes)
import qualified Style
import qualified Syntax

type Selection a = Some (Path a)

viewTerm ::
  forall t m a b.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  , PerformEvent t m, MonadIO (Performable m)
  ) =>
  (b -> Text) ->
  Path (Syntax.Term a) (Syntax.Term b) ->
  Dynamic t (Maybe (Selection (Syntax.Term b))) ->
  Syntax.Term b ->
  m (Dynamic t Bool, Event t (Selection (Syntax.Term a)))
viewTerm name path dmSelection tm = do
  rec
    let eMouseEnter = domEvent Mouseenter e
    let eMouseLeave = domEvent Mouseleave e
    let eMouseDown = domEvent Mousedown e
    let eMouseUp = domEvent Mouseup e
    let eSpace = keypress Space e
    dThisHovered <-
      holdDyn False $
      leftmost [True <$ eMouseEnter, False <$ eMouseLeave]
    dHovered <-
      holdUniqDyn $
      (\a b -> a && not b) <$>
      dThisHovered <*>
      dChildHovered
    dMouseHeld <-
      holdDyn False $
      gate
        (current dHovered)
        (leftmost [True <$ eMouseDown, False <$ eMouseUp])
    let
      dSelected =
        (\mSelection ->
           case mSelection of
             Nothing -> False
             Just (Some path) ->
               case viewl path of
                 EmptyL -> True
                 _ :< _ -> False
        ) <$>
        dmSelection
      eMenu = gate (current dSelected) eSpace
    performEvent_ $ liftIO (putStrLn "hi") <$ eMenu
    (e, (dChildHovered, eChildClicked)) <-
      elDynClass'
        "span"
        ((\hovered selected clicking ->
            classes $
            [ Style.focusable, Style.node ] <>
            [ Style.selected | selected ] <>
            [ Style.hovered | hovered ] <>
            [ Style.clicking | clicking ] <>
            (case tm of
               Syntax.Hole{} -> [ Style.leaf ]
               Syntax.Var{} -> [ Style.leaf ]
               _ -> []
            )
         ) <$>
         dHovered <*>
         dSelected <*>
         dMouseHeld
        ) $
      case tm of
        Syntax.Hole -> do
          text "_"
          pure (constDyn False, never)
        Syntax.Var a -> do
          text (name a)
          pure (constDyn False, never)
        Syntax.App a b -> do
          (dH1, eC1) <-
            viewTerm
              name
              (snoc path AppL)
              (
               (>>=
               \(Some f) -> case viewl f of
                 AppL :< rest -> Just (Some rest)
                 _ -> Nothing
               ) <$>
               dmSelection
              )
              a
          (dH2, eC2) <-
            viewTerm
              name
              (snoc path AppR)
              (
               (>>=
               \(Some f) -> case viewl f of
                 AppR :< rest -> Just (Some rest)
                 _ -> Nothing
               ) <$>
               dmSelection
              )
              b
          dH <- holdUniqDyn $ (||) <$> dH1 <*> dH2
          pure
            ( dH
            , leftmost [eC1, eC2]
            )
        Syntax.Lam n e -> do
          text n
          (dH1, eC1) <-
            viewTerm
              (unvar (\() -> n) name)
              (snoc path LamBody)
              (
               (>>=
               \(Some f) ->
                 case viewl f of
                   LamBody :< rest -> Just (Some rest)
                   _ -> Nothing
               ) <$>
               dmSelection
              )
              (Bound.fromScope e)
          pure (dH1, eC1)
  let eClicked = domEvent Click e
  dHoveredOrChild <- holdUniqDyn $ (||) <$> dThisHovered <*> dChildHovered
  pure
    ( dHoveredOrChild
    , leftmost
      [ Some path <$ gate (current dHovered) eClicked
      , eChildClicked
      ]
    )
