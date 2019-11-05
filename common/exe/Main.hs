{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language FlexibleInstances, MultiParamTypeClasses, TypeFamilies, UndecidableInstances #-}
module Main where

import Editor
import Reflex.Dom

headWidget :: DomBuilder t m => m ()
headWidget = do
  el "title" $ text "Testing"
  el "style" $ text "html { font-family: monospace; }"

main :: IO ()
main =
  mainWidgetWithHead headWidget $ do
    let ex = Lam "f" $ Lam "x" $ App (Var 1) (Var 0)
    let dFocus = pure $ FocusPath (Cons LamBody $ Cons LamBody Nil)
    eDelete <- deleteEvent dFocus
    rec
      dEx <- holdExpr ex $ leftmost [eDelete, eEdit]
      eEdit <- viewExprD dFocus dEx
    pure ()
