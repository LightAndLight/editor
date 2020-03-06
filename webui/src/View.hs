{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
module View where

import qualified Bound
import Bound.Var (unvar)
import Control.Monad.Fix (MonadFix)
import "core" Data.Some (Some(..))
import Reflex
import Reflex.Dom

import Path (Path, P(..), ViewL(..), viewl, snoc)
import Style (classes)
import qualified Style
import qualified Syntax

type Selection a = Some (Path a)

data NodeInfo t a
  = NodeInfo
  { _nodeHovered :: Dynamic t Bool
  , _nodeFocus :: Event t (Selection a)
  }

viewName ::
  (MonadHold t m, DomBuilder t m, PostBuild t m, MonadFix m) =>
  (b -> Syntax.Name) ->
  Path (Syntax.Term ty tm) b ->
  Dynamic t (Maybe (Selection b)) ->
  b ->
  m (NodeInfo t (Syntax.Term ty tm))
viewName name path dmSelection v = do
  rec
    let eMouseEnter = domEvent Mouseenter e
    let eMouseLeave = domEvent Mouseleave e
    let eMouseDown = domEvent Mousedown e
    let eMouseUp = domEvent Mouseup e
    dThisHovered <-
      holdDyn False $
      leftmost [True <$ eMouseEnter, False <$ eMouseLeave]
    dHovered <- holdUniqDyn dThisHovered
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
             Just (Some path') ->
               case viewl path' of
                 EmptyL -> True
                 _ :< _ -> False
        ) <$>
        dmSelection
    (e, _) <-
      elDynClass'
        "span"
        ((\hovered selected clicking ->
            classes $
            [ Style.code, Style.focusable, Style.node, Style.leaf ] <>
            [ Style.selected | selected ] <>
            [ Style.hovered | hovered ] <>
            [ Style.clicking | clicking ]
         ) <$>
         dHovered <*>
         dSelected <*>
         dMouseHeld
        )
        (text . Syntax.unName $ name v)
  let eClicked = domEvent Click e
  pure $
    NodeInfo
    { _nodeHovered = dHovered
    , _nodeFocus = Some path <$ gate (current dHovered) eClicked
    }

viewType ::
  forall t m ty ty' tm.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  ) =>
  (ty' -> Syntax.Name) ->
  Path (Syntax.Term ty tm) (Syntax.Type ty') ->
  Dynamic t (Maybe (Selection (Syntax.Type ty'))) ->
  Syntax.Type ty' ->
  m (NodeInfo t (Syntax.Term ty tm))
viewType nameTy path dmSelection ty = do
  rec
    let eMouseEnter = domEvent Mouseenter e
    let eMouseLeave = domEvent Mouseleave e
    let eMouseDown = domEvent Mousedown e
    let eMouseUp = domEvent Mouseup e
    dThisHovered <-
      holdDyn False $
      leftmost [True <$ eMouseEnter, False <$ eMouseLeave]
    dHovered <-
      holdUniqDyn $
      (\a b -> a && not b) <$>
      dThisHovered <*>
      _nodeHovered childInfo
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
             Just (Some path') ->
               case viewl path' of
                 EmptyL -> True
                 _ :< _ -> False
        ) <$>
        dmSelection
    (e, childInfo) <-
      elDynClass'
        "span"
        ((\hovered selected clicking ->
            classes $
            [ Style.code, Style.focusable, Style.node ] <>
            [ Style.selected | selected ] <>
            [ Style.hovered | hovered ] <>
            [ Style.clicking | clicking ] <>
            (case ty of
               Syntax.THole{} -> [ Style.leaf ]
               Syntax.TVar{} -> [ Style.leaf ]
               _ -> []
            )
         ) <$>
         dHovered <*>
         dSelected <*>
         dMouseHeld
        ) $
      case ty of
        Syntax.THole -> do
          text "_"
          pure $
            NodeInfo
            { _nodeHovered = constDyn False
            , _nodeFocus = never
            }
        Syntax.TVar a -> do
          text . Syntax.unName $ nameTy a
          pure $
            NodeInfo
            { _nodeHovered = constDyn False
            , _nodeFocus = never
            }
        Syntax.TArr a b -> do
          let
            parensa =
              case a of
                Syntax.TArr{} -> True
                Syntax.TForall{} -> True
                _ -> False
          aInfo <-
            (if parensa then text "(" else pure ()) *>
            viewType
              nameTy
              (snoc path TArrL)
              (
               (>>=
               \(Some f) -> case viewl f of
                 TArrL :< rest -> Just (Some rest)
                 _ -> Nothing
               ) <$>
               dmSelection
              )
              a <*
            (if parensa then text ")" else pure ())

          text "->"

          let parensb = False
          bInfo <-
            (if parensb then text "(" else pure ()) *>
            viewType
              nameTy
              (snoc path TArrR)
              (fmap
                 (>>=
                  \(Some f) -> case viewl f of
                    TArrR :< rest -> Just (Some rest)
                    _ -> Nothing
                 )
                 dmSelection
              )
              b <*
            (if parensb then text ")" else pure ())

          dH <- holdUniqDyn $ (||) <$> _nodeHovered aInfo <*> _nodeHovered bInfo
          pure $
            NodeInfo
            { _nodeHovered = dH
            , _nodeFocus = leftmost [_nodeFocus aInfo, _nodeFocus bInfo]
            }
        Syntax.TForall n body -> do
          text "forall"
          nInfo <-
            viewName
              id
              (Path.snoc path TForallArg)
              (fmap
                (>>=
                  \(Some f) -> case viewl f of
                    Path.TForallArg :< rest -> Just (Some rest)
                    _ -> Nothing
                )
                dmSelection
              )
              n
          text "."
          bodyInfo <-
            viewType
              (unvar (\() -> n) nameTy)
              (snoc path TForallBody)
              (fmap
                 (>>=
                  \(Some f) ->
                   case viewl f of
                     TForallBody :< rest -> Just (Some rest)
                     _ -> Nothing
                 )
                 dmSelection
              )
              (Bound.fromScope body)

          dH <-
            holdUniqDyn $
            (||) <$> _nodeHovered nInfo <*> _nodeHovered bodyInfo
          pure $
            NodeInfo
            { _nodeHovered = dH
            , _nodeFocus = leftmost [_nodeFocus nInfo, _nodeFocus bodyInfo]
            }
  let eClicked = domEvent Click e
  dHoveredOrChild <-
    holdUniqDyn $ (||) <$> dThisHovered <*> _nodeHovered childInfo
  pure $
    NodeInfo
    { _nodeHovered = dHoveredOrChild
    , _nodeFocus =
      leftmost
      [ Some path <$ gate (current dHovered) eClicked
      , _nodeFocus childInfo
      ]
    }

viewTerm ::
  forall t m ty tm tm'.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  ) =>
  (ty -> Syntax.Name) ->
  (tm' -> Syntax.Name) ->
  Path (Syntax.Term ty tm) (Syntax.Term ty tm') ->
  Dynamic t (Maybe (Selection (Syntax.Term ty tm'))) ->
  Syntax.Term ty tm' ->
  m (NodeInfo t (Syntax.Term ty tm))
viewTerm nameTy name path dmSelection tm = do
  rec
    let eMouseEnter = domEvent Mouseenter e
    let eMouseLeave = domEvent Mouseleave e
    let eMouseDown = domEvent Mousedown e
    let eMouseUp = domEvent Mouseup e
    dThisHovered <-
      holdDyn False $
      leftmost [True <$ eMouseEnter, False <$ eMouseLeave]
    dHovered <-
      holdUniqDyn $
      (\a b -> a && not b) <$>
      dThisHovered <*>
      _nodeHovered childInfo
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
             Just (Some path') ->
               case viewl path' of
                 EmptyL -> True
                 _ :< _ -> False
        ) <$>
        dmSelection
    (e, childInfo) <-
      elDynClass'
        "span"
        ((\hovered selected clicking ->
            classes $
            [ Style.code, Style.focusable, Style.node ] <>
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
          pure $
            NodeInfo
            { _nodeHovered = constDyn False
            , _nodeFocus = never
            }
        Syntax.Var a -> do
          text . Syntax.unName $ name a
          pure $
            NodeInfo
            { _nodeHovered = constDyn False
            , _nodeFocus = never
            }
        Syntax.App a b -> do
          let
            parensa =
              case a of
                Syntax.Lam{} -> True
                Syntax.LamAnn{} -> True
                _ -> False
          aInfo <-
            (if parensa then text "(" else pure ()) *>
            viewTerm
              nameTy
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
              a <*
            (if parensa then text ")" else pure ())

          let
            parensb =
              case b of
                Syntax.Lam{} -> True
                Syntax.LamAnn{} -> True
                Syntax.App{} -> True
                _ -> False
          bInfo <-
            (if parensb then text "(" else pure ()) *>
            viewTerm
              nameTy
              name
              (snoc path AppR)
              (fmap
                 (>>=
                  \(Some f) -> case viewl f of
                    AppR :< rest -> Just (Some rest)
                    _ -> Nothing
                 )
                 dmSelection
              )
              b <*
            (if parensb then text ")" else pure ())

          dH <- holdUniqDyn $ (||) <$> _nodeHovered aInfo <*> _nodeHovered bInfo
          pure $
            NodeInfo
            { _nodeHovered = dH
            , _nodeFocus = leftmost [_nodeFocus aInfo, _nodeFocus bInfo]
            }
        Syntax.Lam n body -> do
          text "\\"
          nInfo <-
            viewName
              id
              (Path.snoc path Path.LamArg)
              (fmap
                (>>=
                  \(Some f) -> case viewl f of
                    Path.LamArg :< rest -> Just (Some rest)
                    _ -> Nothing
                )
                dmSelection
              )
              n
          text "->"
          bodyInfo <-
            viewTerm
              nameTy
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
              (Bound.fromScope body)

          dH <-
            holdUniqDyn $
            (||) <$> _nodeHovered nInfo <*> _nodeHovered bodyInfo
          pure $
            NodeInfo
            { _nodeHovered = dH
            , _nodeFocus = leftmost [_nodeFocus nInfo, _nodeFocus bodyInfo]
            }
        Syntax.LamAnn n ty body -> do
          text "\\"
          text "("
          nInfo <-
            viewName
              id
              (Path.snoc path Path.LamAnnArg)
              (fmap
                (>>=
                  \(Some f) -> case viewl f of
                    Path.LamAnnArg :< rest -> Just (Some rest)
                    _ -> Nothing
                )
                dmSelection
              )
              n
          text ":"
          tyInfo <-
            viewType
              nameTy
              (Path.snoc path LamAnnType)
              (fmap
                (>>=
                  \(Some f) -> case viewl f of
                    Path.LamAnnType :< rest -> Just (Some rest)
                    _ -> Nothing
                )
                dmSelection
              )
              ty
          text ")"
          text " ->"
          bodyInfo <-
            viewTerm
              nameTy
              (unvar (\() -> n) name)
              (snoc path LamAnnBody)
              (
               (>>=
               \(Some f) ->
                 case viewl f of
                   LamAnnBody :< rest -> Just (Some rest)
                   _ -> Nothing
               ) <$>
               dmSelection
              )
              (Bound.fromScope body)

          dH <-
            holdUniqDyn $
            (\a b c -> a || b || c) <$>
            _nodeHovered nInfo <*>
            _nodeHovered tyInfo <*>
            _nodeHovered bodyInfo
          pure $
            NodeInfo
            { _nodeHovered = dH
            , _nodeFocus =
              leftmost
              [ _nodeFocus nInfo
              , _nodeFocus tyInfo
              , _nodeFocus bodyInfo
              ]
            }
  let eClicked = domEvent Click e
  dHoveredOrChild <-
    holdUniqDyn $ (||) <$> dThisHovered <*> _nodeHovered childInfo
  pure $
    NodeInfo
    { _nodeHovered = dHoveredOrChild
    , _nodeFocus =
      leftmost
      [ Some path <$ gate (current dHovered) eClicked
      , _nodeFocus childInfo
      ]
    }
