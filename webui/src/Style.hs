{-# language OverloadedStrings #-}
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

css :: Css
css =
  Clay.span ? do
    fontFamily [] [monospace]
