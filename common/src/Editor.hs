{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
module Editor where

import Control.Monad
import Control.Monad.Fix
import Data.String
import Language.Javascript.JSaddle.Monad (MonadJSM)
import Reflex
import Reflex.Network
import Reflex.Dom
import qualified GHCJS.DOM.EventM as EventM
import qualified GHCJS.DOM.GlobalEventHandlers as Events

data Expr
  = Var Int
  | Lam String Expr
  | App Expr Expr
  deriving (Eq, Show)

data PathPiece a where
  LamName :: PathPiece String
  LamBody :: PathPiece Expr
  AppLeft :: PathPiece Expr
  AppRight :: PathPiece Expr
deriving instance Show (PathPiece a)

data Path a b where
  Nil :: Path a a
  Cons :: PathPiece a -> Path a b -> Path Expr b

showPath :: Path a b -> String
showPath Nil = "<empty path>"
showPath (Cons a Nil) = show a
showPath (Cons a b) = show a ++ " > " ++ showPath b

data Edit a where
  EditAt :: Path a b -> b -> Edit a
  DeleteAt :: Path a b -> Edit a

showEdit :: Edit a -> String
showEdit (EditAt p _) = "Edit at: " ++ showPath p
showEdit (DeleteAt p) = "Delete at: " ++ showPath p

data Focus a where
  FocusPath :: Path a b -> Focus a

data ExprD t
  = VarD Int
  | LamD (Dynamic t String) (Dynamic t (ExprD t))
  | AppD (Dynamic t (ExprD t)) (Dynamic t (ExprD t))
  | HoleD

followPathPieceD :: PathPiece a -> ExprD t -> Maybe (Dynamic t a)
followPathPieceD pp ex =
  case pp of
    LamName ->
      case ex of
        LamD a _ -> Just a
        _ -> Nothing
    LamBody ->
      case ex of
        LamD _ a -> Just a
        _ -> Nothing
    AppLeft ->
      case ex of
        AppD a _ -> Just a
        _ -> Nothing
    AppRight ->
      case ex of
        AppD _ a -> Just a
        _ -> Nothing

holdExprInner ::
  (Reflex t, MonadHold t m, Adjustable t m) =>
  Expr ->
  Event t (Edit Expr) ->
  m (ExprD t)
holdExprInner initial eEdit =
  case initial of
    Var n ->
        pure $ VarD n
    Lam n b ->
      LamD <$>
          (holdDyn
            n
            (fmapMaybe
               (\case
                   EditAt (Cons LamName Nil) n' -> Just n'
                   _ -> Nothing)
               eEdit)) <*>
        (holdExpr
            b
            (fmapMaybe
               (\case
                   EditAt (Cons LamBody rest) e -> Just $ EditAt rest e
                   DeleteAt (Cons LamBody rest) -> Just $ DeleteAt rest
                   _ -> Nothing)
               eEdit))
    App a b ->
      AppD <$>
        (holdExpr
          a
          (fmapMaybe
             (\case
                 EditAt (Cons AppLeft rest) e -> Just $ EditAt rest e
                 DeleteAt (Cons AppLeft rest) -> Just $ DeleteAt rest
                 _ -> Nothing)
             eEdit)) <*>
        (holdExpr
          b
          (fmapMaybe
             (\case
                 EditAt (Cons AppRight rest) e -> Just $ EditAt rest e
                 DeleteAt (Cons AppRight rest) -> Just $ DeleteAt rest
                 _ -> Nothing)
             eEdit))

holdExprM ::
  (Reflex t, MonadHold t m, Adjustable t m) =>
  m (ExprD t) ->
  Event t (Edit Expr) ->
  m (Dynamic t (ExprD t))
holdExprM initialM eEdit =
  networkHold
    initialM
    (fmapMaybe
        (\case
            EditAt Nil a -> Just $ holdExprInner a eEdit
            DeleteAt Nil -> Just $ pure HoleD
            _ -> Nothing)
        eEdit)

holdExpr ::
  (Reflex t, MonadHold t m, Adjustable t m) =>
  Expr ->
  Event t (Edit Expr) ->
  m (Dynamic t (ExprD t))
holdExpr initial eEdit = holdExprM (holdExprInner initial eEdit) eEdit

upFocus :: Focus a -> Maybe (Focus a)
upFocus (FocusPath Nil) = Nothing
upFocus (FocusPath (Cons _ Nil)) = Just $ FocusPath Nil
upFocus (FocusPath (Cons a rest)) = do
  FocusPath rest' <- upFocus $ FocusPath rest
  pure $ FocusPath (Cons a rest')

downFocus :: MonadSample t m => ExprD t -> Focus a -> m (Maybe (Focus a))
downFocus ex (FocusPath Nil) =
  case ex of
    VarD{} -> pure Nothing
    AppD{} -> pure . Just $ FocusPath (Cons AppLeft Nil)
    LamD{} -> pure . Just $ FocusPath (Cons LamBody Nil)
downFocus ex (FocusPath (Cons a rest)) = do
  case followPathPieceD a ex of
    Nothing -> pure Nothing
    Just dEx' -> do
      ex' <- sample $ current dEx'
      m_rest' <- downFocus ex' $ FocusPath rest
      case m_rest' of
        Nothing -> pure Nothing
        Just (FocusPath rest') -> pure . Just $ FocusPath (Cons a rest')

changeFocus ::
  ( Reflex t
  , DomBuilderSpace m ~ GhcjsDomSpace
  , TriggerEvent t m
  , HasDocument m
  , MonadJSM m
  ) =>
  Dynamic t (Focus a) ->
  m (Event t (Focus a))
changeFocus dFocus = do
  doc <- askDocument
  eK_key <-
    wrapDomEventMaybe
      doc
      (`EventM.on` Events.keyDown)
      (fmap (\c -> guard $ c == 75) getKeyEvent)
  pure $
    attachWithMaybe
      (\focus _ -> upFocus focus)
      (current dFocus)
      eK_key


holdFocus ::
  ( Reflex t
  , DomBuilderSpace m ~ GhcjsDomSpace
  , MonadHold t m
  , TriggerEvent t m
  , HasDocument m
  , MonadJSM m
  , MonadFix m
  ) =>
  Focus a ->
  m (Dynamic t (Focus a))
holdFocus initial = do
  rec
    eChange <- changeFocus dFocus
    dFocus <- holdDyn initial eChange
  pure dFocus

deleteEvent ::
  ( Reflex t
  , DomBuilderSpace m ~ GhcjsDomSpace
  , TriggerEvent t m
  , HasDocument m
  , MonadJSM m
  ) =>
  Dynamic t (Focus Expr) ->
  m (Event t (Edit Expr))
deleteEvent dFocus = do
  doc <- askDocument
  eDeleteKey <-
    wrapDomEventMaybe
      doc
      (`EventM.on` Events.keyDown)
      (fmap (\c -> guard $ c == 46) getKeyEvent)
  pure $ (\(FocusPath p) -> DeleteAt p) <$> current dFocus <@ eDeleteKey


viewExprD ::
  forall t m.
  (DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m) =>
  Dynamic t (Focus Expr) ->
  Dynamic t (ExprD t) ->
  m (Event t (Edit Expr))
viewExprD df dExpr = do
  switchHold never =<< dyn (go id (Just <$> df) <$> dExpr)
  where
    go ::
      (Path Expr Expr -> Path Expr Expr) ->
      Dynamic t (Maybe (Focus Expr)) ->
      ExprD t ->
      m (Event t (Edit Expr))
    go path dFocus expr = do
      dIsFocused <- holdUniqDyn $ (\case; Just (FocusPath Nil) -> True; _ -> False) <$> dFocus
      let dAttrs = (\b -> if b then "style" =: "background-color: gray;" else mempty) <$> dIsFocused
      (_, e1) <-
        elDynAttr' "span" dAttrs $
          case expr of
            VarD n -> do
              text . fromString . ('#' :) $ show n
              pure never
            LamD _ b -> do
              text "lam. "
              let
                dFocus' =
                  (\case
                      Just (FocusPath (Cons LamBody rest)) -> Just (FocusPath rest)
                      _ -> Nothing) <$>
                  dFocus
              switchHold never =<< dyn (go (path . Cons LamBody) dFocus' <$> b)
            AppD a b -> do
              let
                dFocus' =
                  (\case
                      Just (FocusPath (Cons AppLeft rest)) -> Just (FocusPath rest)
                      _ -> Nothing) <$>
                  dFocus
              e1 <- switchHold never =<< dyn (go (path . Cons AppLeft) dFocus' <$> a)
              text " "
              let
                dFocus'' =
                  (\case
                      Just (FocusPath (Cons AppRight rest)) -> Just (FocusPath rest)
                      _ -> Nothing) <$>
                  dFocus
              e2 <- switchHold never =<< dyn (go (path . Cons AppRight) dFocus'' <$> b)
              pure $ leftmost [e1, e2]
            HoleD -> do
              text "_"
              pure never
      let e2 = never
      pure $ leftmost [e1, e2]
