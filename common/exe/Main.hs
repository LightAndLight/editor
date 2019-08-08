{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
module Main where

import Editor

import Control.Monad.Fix (MonadFix)
import Data.Map (Map)
import Data.Dependent.Map (DMap)
import Data.String (fromString)
import Reflex
import Reflex.Dom

import qualified Data.Map as Map
import qualified Data.Dependent.Map as DMap

data Change = Highlight | Clear

renderExpr ::
  forall t m a.
  (DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m) =>
  (ID a, DMap ID NodeInfo) ->
  Event t (Map SomeID Change) ->
  m (Event t (Map SomeID Change))
renderExpr (root, nodes) eChanges = do
  case DMap.lookup root nodes of
    Nothing -> do
      text $ fromString (show root) <> "Not found"
      pure never
    Just ni -> do
      rec
        let eEnter :: Event t () = domEvent Mouseenter theSpan
        let eLeave :: Event t () = domEvent Mouseleave theSpan
        let eAllChanges = eChanges <> eChanges'
        dStyling <-
          holdDyn
            mempty
            (fmapMaybe
               (fmap
                  (\case
                     Highlight -> "style" =: "background-color: gray"
                     Clear -> mempty) .
                Map.lookup (SomeID root))
               eAllChanges)
        (theSpan, eChanges') <-
          elDynAttr' "span" (("id" =: fromString (show root) <>) <$> dStyling) $
          case ni of
            BindingInfo _ a -> do
              text $ fromString a
              let bounds = getBounds nodes root
              pure $
                leftmost
                [ (Map.insert (SomeID root) Highlight $
                   foldr (\b -> Map.insert (SomeID b) Highlight) mempty bounds) <$ eEnter
                , (Map.insert (SomeID root) Clear $
                   foldr (\b -> Map.insert (SomeID b) Clear) mempty bounds) <$ eLeave
                ]
            BoundInfo _ a -> do
              text $ fromString a
              let binding = getBinding nodes root
              pure $
                leftmost
                [ (Map.insert (SomeID root) Highlight $
                   foldr (\b -> Map.insert (SomeID b) Highlight) mempty binding) <$ eEnter
                , (Map.insert (SomeID root) Clear $
                   foldr (\b -> Map.insert (SomeID b) Clear) mempty binding) <$ eLeave
                ]
            HoleInfo _ -> do
              text "_"
              pure never
            VarInfo _ val -> do
              renderExpr (val, nodes) eChanges
            AppInfo _ a b -> do
              eChanges1 <- renderExpr (a, nodes) eChanges
              text " "
              eChanges2 <- renderExpr (b, nodes) eChanges
              pure $ eChanges1 <> eChanges2
            LamInfo _ a b -> do
              text "\\"
              eChanges1 <- renderExpr (a, nodes) eChanges
              text " -> "
              eChanges2 <- renderExpr (b, nodes) eChanges
              pure $ eChanges1 <> eChanges2
      pure eChanges'

headWidget :: DomBuilder t m => m ()
headWidget = do
  el "title" $ text "Testing"
  el "style" $ text "html { font-family: monospace; }"

main :: IO ()
main =
  mainWidgetWithHead headWidget $ do
    let
      e =
        Lam (Binding "f") $
        Lam (Binding "x") $
        App (App (Var $ Bound "f") (Var $ Bound "x")) (Var $ Bound "x")
      e' = unbuild mempty (Context Nothing mempty) e
    rec eChanges <- renderExpr e' eChanges
    pure ()
