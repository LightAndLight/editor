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
  | Hole
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

data EditAction
  = InsertLambda
  | InsertApp
  | DeleteExpr

data Edit t a where
  EditAt :: Path t a b -> EditAction -> Edit t a

showEdit :: Edit t a -> String
showEdit (EditAt p act) =
  (case act of
     InsertLambda -> "insert lambda"
     InsertApp -> "insert app"
     DeleteExpr -> "delete") ++
  " at: " ++
  showPath p

data Focus t a where
  FocusPath :: Path t a b -> Focus t a

data ExprD t
  = VarD Int
  | LamD (Dynamic t String) (Dynamic t (ExprD t))
  | AppD (Dynamic t (ExprD t)) (Dynamic t (ExprD t))
  | HoleD

holdExprInner ::
  (Reflex t, MonadHold t m, Adjustable t m, MonadFix m) =>
  Expr ->
  Event t (Edit t (ExprD t)) ->
  m (ExprD t)
holdExprInner initial eEdit =
  case initial of
    Hole -> pure HoleD
    Var n ->
        pure $ VarD n
    Lam n b ->
      LamD (pure n) <$>
      holdExpr
        b
        (fmapMaybe
            (\case
                EditAt (Cons LamBody rest) act -> Just $ EditAt rest act
                _ -> Nothing)
            eEdit)
    App a b ->
      AppD <$>
      holdExpr
        a
        (fmapMaybe
            (\case
                EditAt (Cons AppLeft rest) act -> Just $ EditAt rest act
                _ -> Nothing)
            eEdit) <*>
      holdExpr
        b
        (fmapMaybe
            (\case
                EditAt (Cons AppRight rest) act -> Just $ EditAt rest act
                _ -> Nothing)
            eEdit)

holdExprM ::
  (Reflex t, MonadHold t m, Adjustable t m, MonadFix m) =>
  m (ExprD t) ->
  Event t (Edit t (ExprD t)) ->
  m (Dynamic t (ExprD t))
holdExprM initialM eEdit = do
  rec
    dExpr <-
      networkHold
        initialM
        (attachWithMaybe
            (\expr (EditAt path act) ->
               case path of
                 Nil ->
                   case act of
                     DeleteExpr -> Just $ pure HoleD
                     InsertLambda ->
                       case expr of
                         HoleD -> Just $ holdExprInner (Lam "" Hole) eEdit
                         _ -> Nothing
                     InsertApp ->
                       case expr of
                         HoleD -> Just $ holdExprInner (App Hole Hole) eEdit
                         _ -> Nothing
                 _ -> Nothing)
            (current dExpr)
            eEdit)
  pure dExpr

holdExpr ::
  (Reflex t, MonadHold t m, Adjustable t m, MonadFix m) =>
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

findHole ::
  forall t m.
  (Reflex t, MonadSample t m) =>
  ExprD t ->
  m (Maybe (Path t (ExprD t) (ExprD t)))
findHole = go id
  where
    go ::
      (Path t (ExprD t) (ExprD t) -> Path t (ExprD t) (ExprD t)) ->
      ExprD t ->
      m (Maybe (Path t (ExprD t) (ExprD t)))
    go path expr =
      case expr of
        VarD{} -> pure Nothing
        HoleD -> pure . Just $ path Nil
        LamD _ a -> go (path . Cons LamBody) =<< sample (current a)
        AppD a b -> do
          m_p <- go (path . Cons AppLeft) =<< sample (current a)
          case m_p of
            Nothing -> go (path . Cons AppRight) =<< sample (current b)
            Just p -> pure $ Just p

{-
nextHoleFocus
  :: (Reflex t, MonadSample t m)
  => ExprD t
  -> Focus t (ExprD t)
  -> m (Maybe (Focus t (ExprD t)))
nextHoleFocus expr (FocusPath Nil) = _
nextHoleFocus expr (FocusPath (Cons a rest)) = _
-}

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

insertLambda ::
  ( Reflex t
  , DomBuilderSpace m ~ GhcjsDomSpace
  , TriggerEvent t m
  , HasDocument m
  , MonadJSM m
  ) =>
  Dynamic t (Focus t (ExprD t)) ->
  m (Event t (Edit t (ExprD t)))
insertLambda dFocus = do
  doc <- askDocument
  eBackslash_key <-
    wrapDomEventMaybe
      doc
      (`EventM.on` Events.keyDown)
      (fmap (\c -> guard $ c == 220) getKeyEvent)
  pure $ (\(FocusPath p) -> EditAt p InsertLambda) <$> current dFocus <@ eBackslash_key

insertApp ::
  ( Reflex t
  , DomBuilderSpace m ~ GhcjsDomSpace
  , TriggerEvent t m
  , HasDocument m
  , MonadJSM m
  ) =>
  Dynamic t (Focus t (ExprD t)) ->
  m (Event t (Edit t (ExprD t)))
insertApp dFocus = do
  doc <- askDocument
  eA_key <-
    wrapDomEventMaybe
      doc
      (`EventM.on` Events.keyDown)
      (fmap (\c -> guard $ c == 65) getKeyEvent)
  pure $ (\(FocusPath p) -> EditAt p InsertApp) <$> current dFocus <@ eA_key

deleteExpr ::
  ( Reflex t
  , DomBuilderSpace m ~ GhcjsDomSpace
  , TriggerEvent t m
  , HasDocument m
  , MonadJSM m
  ) =>
  Dynamic t (Focus t (ExprD t)) ->
  m (Event t (Edit t (ExprD t)))
deleteExpr dFocus = do
  doc <- askDocument
  eDeleteKey <-
    wrapDomEventMaybe
      doc
      (`EventM.on` Events.keyDown)
      (fmap (\c -> guard $ c == 46) getKeyEvent)
  pure $ (\(FocusPath p) -> EditAt p DeleteExpr) <$> current dFocus <@ eDeleteKey


editEvents ::
  ( Reflex t
  , DomBuilderSpace m ~ GhcjsDomSpace
  , TriggerEvent t m
  , HasDocument m
  , MonadJSM m
  ) =>
  Dynamic t (Focus t (ExprD t)) ->
  m (Event t (Edit t (ExprD t)))
editEvents dFocus = do
  eDelete <- deleteExpr dFocus
  eInsertLambda <- insertLambda dFocus
  eInsertApp <- insertApp dFocus
  pure $ leftmost [eDelete, eInsertLambda, eInsertApp]

shouldParens ::
  ExprD t ->
  ExprD t ->
  Bool
shouldParens parent child =
  case (parent, child) of
    (AppD{}, AppD{}) -> True
    (AppD{}, LamD{}) -> True
    _ -> False

parens ::
  (DomBuilder t m, PostBuild t m) =>
  Dynamic t Bool ->
  m a ->
  m a
parens dShould m = do
  dyn_ $ (\should -> when should $ text "(") <$> dShould
  a <- m
  dyn_ $ (\should -> when should $ text ")") <$> dShould
  pure a

viewExprD ::
  forall t m.
  (DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m) =>
  Dynamic t (Focus t (ExprD t)) ->
  Dynamic t (ExprD t) ->
  m (Event t (Edit t (ExprD t)))
viewExprD df dExpr = do
  switchHold never =<< dyn (go id (pure False) (Just <$> df) <$> dExpr)
  where
    go ::
      (Path t (ExprD t) (ExprD t) -> Path t (ExprD t) (ExprD t)) ->
      Dynamic t Bool ->
      Dynamic t (Maybe (Focus t (ExprD t))) ->
      ExprD t ->
      m (Event t (Edit t (ExprD t)))
    go path dShouldParens dFocus expr = do
      dIsFocused <- holdUniqDyn $ (\case; Just (FocusPath Nil) -> True; _ -> False) <$> dFocus
      let dAttrs = (\b -> if b then "style" =: "background-color: gray;" else mempty) <$> dIsFocused
      (_, e1) <-
        elDynAttr' "span" dAttrs .
        parens dShouldParens $
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
              switchHold never =<< dyn (go (path . Cons LamBody) (pure False) dFocus' <$> b)
            AppD a b -> do
              let
                dFocus' =
                  (\case
                      Just (FocusPath (Cons AppLeft rest)) -> Just (FocusPath rest)
                      _ -> Nothing) <$>
                  dFocus
              shouldParensLeft <- holdUniqDyn $ shouldParens expr <$> a
              e1 <-
                switchHold never =<<
                dyn (go (path . Cons AppLeft) shouldParensLeft dFocus' <$> a)
              text " "
              let
                dFocus'' =
                  (\case
                      Just (FocusPath (Cons AppRight rest)) -> Just (FocusPath rest)
                      _ -> Nothing) <$>
                  dFocus
              shouldParensRight <- holdUniqDyn $ shouldParens expr <$> b
              e2 <- switchHold never =<< dyn (go (path . Cons AppRight) shouldParensRight dFocus'' <$> b)
              pure $ leftmost [e1, e2]
            HoleD -> do
              text "_"
              pure never
      let e2 = never
      pure $ leftmost [e1, e2]
