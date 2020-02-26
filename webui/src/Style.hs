{-# language OverloadedStrings #-}
module Style where

import qualified Data.Text.Lazy as Lazy (Text)
import Data.Text (Text)

import Clay

cssText :: Lazy.Text
cssText = render css

css :: Css
css =
  Clay.span ? do
    fontFamily [] [monospace]
