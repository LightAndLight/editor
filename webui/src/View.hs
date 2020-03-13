{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language RankNTypes #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
module View where

import qualified Bound
import Bound.Var (unvar)
import Control.Lens.TH (makeLenses)
import Control.Monad.Fix (MonadFix)
import qualified Data.Text as Text
import Reflex
import Reflex.Dom

import Focus (Selection(..))
import Path (Path, P(..), ViewL(..), HasTargetInfo, viewl, snoc)
import qualified Path
import Typecheck (Holes(..))
import Style (classes)
import qualified Style
import qualified Syntax

data NodeInfo t a
  = NodeInfo
  { _nodeHovered :: Dynamic t Bool
  , _nodeFocus :: Event t (Selection a)
  }
makeLenses ''NodeInfo

instance Reflex t => Semigroup (NodeInfo t a) where
  n1 <> n2 =
    NodeInfo
    { _nodeHovered = (||) <$> _nodeHovered n1 <*> _nodeHovered n2
    , _nodeFocus = leftmost [_nodeFocus n1, _nodeFocus n2]
    }

instance Reflex t => Monoid (NodeInfo t a) where
  mempty = NodeInfo { _nodeHovered = pure False, _nodeFocus = never }

viewName ::
  (MonadHold t m, DomBuilder t m, PostBuild t m, MonadFix m) =>
  HasTargetInfo b =>
  (b -> Syntax.Name) ->
  Dynamic t (Maybe (Selection b)) ->
  Path a b ->
  b ->
  m (NodeInfo t a)
viewName name dmSelection path v =
  viewNode (const True) dmSelection path (\a -> mempty <$ text (Syntax.unName $ name a)) v

viewTypeChildren ::
  forall t m a ty' tm.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  ) =>
  (ty' -> Syntax.Name) ->
  Dynamic t (Maybe (Selection (Syntax.Type ty'))) ->
  Path a (Syntax.Type ty') ->
  Syntax.Type ty' ->
  m (NodeInfo t a)
viewTypeChildren nameTy dmSelection path ty = do
  case ty of
    Syntax.TUnsolved{} -> error "todo"
    Syntax.TSubst{} -> error "todo"
    Syntax.TName n -> do
      text $ Syntax.unName n
      pure mempty
    Syntax.THole -> do
      text "_"
      pure mempty
    Syntax.TMeta n -> do
      text . Text.pack $ "?" <> show n
      pure mempty
    Syntax.TVar a -> do
      text . Syntax.unName $ nameTy a
      pure mempty
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
          (
            (>>=
            \(Selection f) -> case viewl f of
              TArrL :< rest -> Just (Selection rest)
              _ -> Nothing
            ) <$>
            dmSelection
          )
          (snoc path TArrL)
          a <*
        (if parensa then text ")" else pure ())

      text "->"

      let parensb = False
      bInfo <-
        (if parensb then text "(" else pure ()) *>
        viewType
          nameTy
          (fmap
              (>>=
              \(Selection f) -> case viewl f of
                TArrR :< rest -> Just (Selection rest)
                _ -> Nothing
              )
              dmSelection
          )
          (snoc path TArrR)
          b <*
        (if parensb then text ")" else pure ())

      nodeHovered holdUniqDyn (aInfo <> bInfo)
    Syntax.TForall n body -> do
      text "forall"
      nInfo <-
        viewName
          id
          (fmap
            (>>=
              \(Selection f) -> case viewl f of
                Path.TForallArg :< rest -> Just (Selection rest)
                _ -> Nothing
            )
            dmSelection
          )
          (Path.snoc path TForallArg)
          n
      text "."
      bodyInfo <-
        viewType
          (unvar (\() -> n) nameTy)
          (fmap
              (>>=
              \(Selection f) ->
                case viewl f of
                  TForallBody :< rest -> Just (Selection rest)
                  _ -> Nothing
              )
              dmSelection
          )
          (snoc path TForallBody)
          (Bound.fromScope body)

      nodeHovered holdUniqDyn (nInfo <> bodyInfo)

viewType ::
  forall t m a ty'.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  ) =>
  (ty' -> Syntax.Name) ->
  Dynamic t (Maybe (Selection (Syntax.Type ty'))) ->
  Path a (Syntax.Type ty') ->
  Syntax.Type ty' ->
  m (NodeInfo t a)
viewType nameTy dmSelection path ty =
  viewNode
    (\case; Syntax.TVar{} -> True; Syntax.THole -> True; _ -> False)
    dmSelection
    path
    (viewTypeChildren nameTy dmSelection path)
    ty

viewTermChildren ::
  forall t m a ty tm'.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  ) =>
  (ty -> Syntax.Name) ->
  (tm' -> Syntax.Name) ->
  Dynamic t (Maybe (Focus.Selection (Syntax.Term ty tm'))) ->
  Path a (Syntax.Term ty tm') ->
  Syntax.Term ty tm' ->
  m (NodeInfo t a)
viewTermChildren nameTy name dmSelection path tm =
  case tm of
    Syntax.Name n -> do
      text $ Syntax.unName n
      pure mempty
    Syntax.Hole -> do
      text "_"
      pure mempty
    Syntax.Var a -> do
      text . Syntax.unName $ name a
      pure mempty
    Syntax.App a b -> do
      let
        parensa =
          case a of
            Syntax.Lam{} -> True
            Syntax.LamAnn{} -> True
            Syntax.Ann{} -> True
            _ -> False
      aInfo <-
        (if parensa then text "(" else pure ()) *>
        viewTerm
          nameTy
          name
          (
            (>>=
            \(Selection f) -> case viewl f of
              AppL :< rest -> Just (Selection rest)
              _ -> Nothing
            ) <$>
            dmSelection
          )
          (snoc path AppL)
          a <*
        (if parensa then text ")" else pure ())

      let
        parensb =
          case b of
            Syntax.Lam{} -> True
            Syntax.LamAnn{} -> True
            Syntax.App{} -> True
            Syntax.Ann{} -> True
            _ -> False
      bInfo <-
        (if parensb then text "(" else pure ()) *>
        viewTerm
          nameTy
          name
          (fmap
              (>>=
              \(Selection f) -> case viewl f of
                AppR :< rest -> Just (Selection rest)
                _ -> Nothing
              )
              dmSelection
          )
          (snoc path AppR)
          b <*
        (if parensb then text ")" else pure ())

      nodeHovered holdUniqDyn (aInfo <> bInfo)
    Syntax.Ann a b -> do
      let
        parensa =
          case a of
            Syntax.Lam{} -> True
            Syntax.LamAnn{} -> True
            Syntax.Ann{} -> True
            _ -> False
      aInfo <-
        (if parensa then text "(" else pure ()) *>
        viewTerm
          nameTy
          name
          (
            (>>=
            \(Selection f) -> case viewl f of
              AnnL :< rest -> Just (Selection rest)
              _ -> Nothing
            ) <$>
            dmSelection
          )
          (snoc path AnnL)
          a <*
        (if parensa then text ")" else pure ())

      text ":"

      let
        parensb =
          case b of
            _ -> False
      bInfo <-
        (if parensb then text "(" else pure ()) *>
        viewType
          nameTy
          (fmap
              (>>=
              \(Selection f) -> case viewl f of
                AnnR :< rest -> Just (Selection rest)
                _ -> Nothing
              )
              dmSelection
          )
          (snoc path AnnR)
          b <*
        (if parensb then text ")" else pure ())

      nodeHovered holdUniqDyn (aInfo <> bInfo)
    Syntax.Lam n body -> do
      text "\\"
      nInfo <-
        viewName
          id
          (fmap
            (>>=
              \(Selection f) -> case viewl f of
                Path.LamArg :< rest -> Just (Selection rest)
                _ -> Nothing
            )
            dmSelection
          )
          (Path.snoc path Path.LamArg)
          n
      text "->"
      bodyInfo <-
        viewTerm
          nameTy
          (unvar (\() -> n) name)
          (
            (>>=
            \(Selection f) ->
              case viewl f of
                LamBody :< rest -> Just (Selection rest)
                _ -> Nothing
            ) <$>
            dmSelection
          )
          (snoc path LamBody)
          (Bound.fromScope body)

      nodeHovered holdUniqDyn (nInfo <> bodyInfo)
    Syntax.LamAnn n ty body -> do
      text "\\"
      text "("
      nInfo <-
        viewName
          id
          (fmap
            (>>=
              \(Selection f) -> case viewl f of
                Path.LamAnnArg :< rest -> Just (Selection rest)
                _ -> Nothing
            )
            dmSelection
          )
          (Path.snoc path Path.LamAnnArg)
          n
      text ":"
      tyInfo <-
        viewType
          nameTy
          (fmap
            (>>=
              \(Selection f) -> case viewl f of
                Path.LamAnnType :< rest -> Just (Selection rest)
                _ -> Nothing
            )
            dmSelection
          )
          (Path.snoc path LamAnnType)
          ty
      text ")"
      text " ->"
      bodyInfo <-
        viewTerm
          nameTy
          (unvar (\() -> n) name)
          (
            (>>=
            \(Selection f) ->
              case viewl f of
                LamAnnBody :< rest -> Just (Selection rest)
                _ -> Nothing
            ) <$>
            dmSelection
          )
          (snoc path LamAnnBody)
          (Bound.fromScope body)

      nodeHovered holdUniqDyn (nInfo <> tyInfo <> bodyInfo)

viewTerm ::
  forall t m a ty tm'.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  ) =>
  (ty -> Syntax.Name) ->
  (tm' -> Syntax.Name) ->
  Dynamic t (Maybe (Selection (Syntax.Term ty tm'))) ->
  Path a (Syntax.Term ty tm') ->
  Syntax.Term ty tm' ->
  m (NodeInfo t a)
viewTerm nameTy name dmSelection path tm =
  viewNode
    (\case; Syntax.Var{} -> True; Syntax.Hole -> True; _ -> False)
    dmSelection
    path
    (viewTermChildren nameTy name dmSelection path)
    tm

viewNode ::
  forall t m a val ty tm.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  , HasTargetInfo val
  ) =>
  (val -> Bool) ->
  Dynamic t (Maybe (Selection val)) ->
  Path a val ->
  (val -> m (NodeInfo t a)) ->
  val ->
  m (NodeInfo t a)
viewNode isLeaf dmSelection path f tm = do
  rec
    dThisHovered <-
      holdDyn False $
      leftmost
      [ True <$ domEvent Mouseenter e
      , False <$ domEvent Mouseleave e
      ]
    dHovered <-
      holdUniqDyn $
      (\a b -> a && not b) <$>
      dThisHovered <*>
      _nodeHovered childInfo
    let
      gateHovered :: forall a. Event t a -> Event t a
      gateHovered = gate $ current dHovered
    dMouseHeld <-
      holdDyn False . gateHovered $
      leftmost [True <$ domEvent Mousedown e, False <$ domEvent Mouseup e]
    let
      dSelected =
        maybe False (\(Selection path') -> Path.isEmpty path') <$>
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
            [ Style.leaf | isLeaf tm ]
         ) <$>
         dHovered <*>
         dSelected <*>
         dMouseHeld
        )
        (f tm)
  nodeHovered holdUniqDyn $
    NodeInfo
    { _nodeHovered = dThisHovered
    , _nodeFocus = Selection path <$ gateHovered (domEvent Click e)
    } <>
    childInfo

viewHoles ::
  DomBuilder t m =>
  (ty -> Syntax.Name) ->
  Holes ty tm ->
  m ()
viewHoles nameTy holes =
  case holes of
    Nil -> el "div" $ text "no holes"
    ConsHole p ns ty Nil ->
      line p ns ty
    ConsHole p ns ty rest -> do
      line p ns ty
      viewHoles nameTy rest
    ConsTHole p1 p2 k Nil ->
      tline p1 p2 k
    ConsTHole p1 p2 k rest -> do
      tline p1 p2 k
      viewHoles nameTy rest
  where
    line p ns ty =
      el "div" . text $
      Text.pack (show p) <> ": " <> Syntax.printType ns ty
    tline p1 p2 k =
      el "div" . text $
      Text.pack (show p1) <> ", " <> Text.pack (show p2) <> ": " <> Syntax.printKind k

viewDecl ::
  forall t m a.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  ) =>
  Path a Syntax.Decl ->
  Dynamic t (Maybe (Selection Syntax.Decl)) ->
  Syntax.Decl ->
  m (NodeInfo t a)
viewDecl path dmSelection decls = _

viewDecls ::
  forall t m a.
  ( MonadHold t m, PostBuild t m, DomBuilder t m, MonadFix m
  ) =>
  Path a Syntax.Decls ->
  Dynamic t (Maybe (Selection Syntax.Decls)) ->
  Syntax.Decls ->
  m (NodeInfo t a)
viewDecls path dmSelection decls = _
