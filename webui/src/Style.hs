{-# language OverloadedStrings #-}
{-# language OverloadedLists #-}
module Style where

import qualified Data.Text.Lazy as Lazy (Text)
import Data.Text (Text)

import Clay

cssText :: Lazy.Text
cssText = render css

newtype Class = Class { unClass :: Text }

classes :: [Class] -> Text
classes [] = mempty
classes [x] = unClass x
classes (x:y:ys) = unClass x <> " " <> classes (y:ys)

focusable :: Class
focusable = Class "focusable"

hovered :: Class
hovered = Class "hovered"

selected :: Class
selected = Class "selected"

node :: Class
node = Class "node"

leaf :: Class
leaf = Class "leaf"

clicking :: Class
clicking = Class "clicking"

code :: Class
code = Class "code"

activeLight :: Color
activeLight = Rgba 150 150 150 0.3

activeDark :: Color
activeDark = Rgba 0 0 0 0.45

css :: Css
css = do
  byClass (unClass Style.code) & do
    fontFamily ["Source Code Pro"] [monospace]
  byClass (unClass focusable) & do
    let fade prop = transition prop 0.25 ease 0
    fade "border-color"
    fade "background-color"
    border solid (px 1) transparent
    byClass (unClass hovered) & do
      backgroundColor activeLight
      border solid (px 1) activeDark
      byClass (unClass clicking) & do
        boxShadow
          [ bsColor (Rgba 0 0 0 0.15) $
            bsInset $
            shadowWithSpread nil nil (em 0.1) (px 1)
          ]
  byClass (unClass Style.selected) & do
    backgroundColor activeLight
    border solid (px 1) activeDark
  byClass (unClass node) & do
    display inlineBlock
    let m = em 0.025
    let m2 = em 0.125
    marginTop m
    marginBottom m
    marginLeft m2
    marginRight m2
    let r = em 0.2
    borderRadius r r r r
    byClass (unClass leaf) & do
      let p = em 0.15
      padding p p p p
