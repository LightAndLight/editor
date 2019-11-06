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

data PathPiece t a b where
  LamName :: PathPiece t (ExprD t) String
  LamBody :: PathPiece t (ExprD t) (ExprD t)
  AppLeft :: PathPiece t (ExprD t) (ExprD t)
  AppRight :: PathPiece t (ExprD t) (ExprD t)
deriving instance Show (PathPiece t a b)

data Path t a b where
  Nil :: Path t a a
  Cons :: PathPiece t a b -> Path t b c -> Path t a c

showPath :: Path t a b -> String
showPath Nil = "<empty path>"
showPath (Cons a Nil) = show a
showPath (Cons a b) = show a ++ " > " ++ showPath b

data Edit t a where
  EditAt :: Path t a b -> b -> Edit t a
  DeleteAt :: Path t a b -> Edit t a

showEdit :: Edit t a -> String
showEdit (EditAt p _) = "Edit at: " ++ showPath p
showEdit (DeleteAt p) = "Delete at: " ++ showPath p

data Focus t a where
  FocusPath :: Path t a b -> Focus t a

data ExprD t
  = VarD Int
  | LamD (Dynamic t String) (Dynamic t (ExprD t))
  | AppD (Dynamic t (ExprD t)) (Dynamic t (ExprD t))
  | HoleD

holdExprInner ::
  (Reflex t, MonadHold t m, Adjustable t m) =>
  Expr ->
  Event t (Edit t (ExprD t)) ->
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
  Event t (Edit t (ExprD t)) ->
  m (Dynamic t (ExprD t))
holdExprM initialM eEdit =
  networkHold
    initialM
    (fmapMaybe
        (\case
            EditAt Nil a -> Just $ pure a
            DeleteAt Nil -> Just $ pure HoleD
            _ -> Nothing)
        eEdit)

holdExpr ::
  (Reflex t, MonadHold t m, Adjustable t m) =>
  Expr ->
  Event t (Edit t (ExprD t)) ->
  m (Dynamic t (ExprD t))
holdExpr initial eEdit = holdExprM (holdExprInner initial eEdit) eEdit

upFocus :: Focus t a -> Maybe (Focus t a)
upFocus (FocusPath Nil) = Nothing
upFocus (FocusPath (Cons _ Nil)) = Just $ FocusPath Nil
upFocus (FocusPath (Cons a rest)) = do
  FocusPath rest' <- upFocus $ FocusPath rest
  pure $ FocusPath (Cons a rest')

downFocus
  :: (Reflex t, MonadSample t m)
  => ExprD t
  -> Focus t (ExprD t)
  -> m (Maybe (Focus t (ExprD t)))
downFocus ex (FocusPath Nil) =
  case ex of
    VarD{} -> pure Nothing
    HoleD{} -> pure Nothing
    AppD{} -> pure . Just $ FocusPath (Cons AppLeft Nil)
    LamD{} -> pure . Just $ FocusPath (Cons LamBody Nil)
downFocus ex (FocusPath (Cons a rest)) = do
  m_rest' <-
    case a of
      LamName -> pure Nothing
      LamBody ->
        case ex of
          LamD _ b -> do
            ex' <- sample (current b)
            downFocus ex' (FocusPath rest)
          _ -> pure Nothing
      AppLeft ->
        case ex of
          AppD b _ -> do
            ex' <- sample (current b)
            downFocus ex' (FocusPath rest)
          _ -> pure Nothing
      AppRight ->
        case ex of
          AppD _ b -> do
            ex' <- sample (current b)
            downFocus ex' (FocusPath rest)
          _ -> pure Nothing
  pure $
    case m_rest' of
      Nothing -> Nothing
      Just (FocusPath rest') -> Just $ FocusPath (Cons a rest')

changeFocus ::
  ( Reflex t
  , DomBuilderSpace m ~ GhcjsDomSpace
  , TriggerEvent t m
  , HasDocument m
  , MonadJSM m
  ) =>
  Dynamic t (Focus t (ExprD t)) ->
  Dynamic t (ExprD t) ->
  m (Event t (Focus t (ExprD t)))
changeFocus dFocus dExpr = do
  doc <- askDocument
  eK_key <-
    wrapDomEventMaybe
      doc
      (`EventM.on` Events.keyDown)
      (fmap (\c -> guard $ c == 75) getKeyEvent)
  eJ_key <-
    wrapDomEventMaybe
      doc
      (`EventM.on` Events.keyDown)
      (fmap (\c -> guard $ c == 74) getKeyEvent)
  pure $
    leftmost
    [ attachWithMaybe
        (\focus _ -> upFocus focus)
        (current dFocus)
        eK_key
    , push
      (\_ -> do
          expr <- sample $ current dExpr
          focus <- sample $ current dFocus
          downFocus expr focus)
      eJ_key
    ]


holdFocus ::
  ( Reflex t
  , DomBuilderSpace m ~ GhcjsDomSpace
  , MonadHold t m
  , TriggerEvent t m
  , HasDocument m
  , MonadJSM m
  , MonadFix m
  ) =>
  Focus t (ExprD t) ->
  Dynamic t (ExprD t) ->
  m (Dynamic t (Focus t (ExprD t)))
holdFocus initial dExpr = do
  rec
    eChange <- changeFocus dFocus dExpr
    dFocus <- holdDyn initial eChange
  pure dFocus

deleteEvent ::
  ( Reflex t
  , DomBuilderSpace m ~ GhcjsDomSpace
  , TriggerEvent t m
  , HasDocument m
  , MonadJSM m
  ) =>
  Dynamic t (Focus t (ExprD t)) ->
  m (Event t (Edit t (ExprD t)))
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
  Dynamic t (Focus t (ExprD t)) ->
  Dynamic t (ExprD t) ->
  m (Event t (Edit t (ExprD t)))
viewExprD df dExpr = do
  switchHold never =<< dyn (go id (Just <$> df) <$> dExpr)
  where
    go ::
      (Path t (ExprD t) (ExprD t) -> Path t (ExprD t) (ExprD t)) ->
      Dynamic t (Maybe (Focus t (ExprD t))) ->
      ExprD t ->
      m (Event t (Edit t (ExprD t)))
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
