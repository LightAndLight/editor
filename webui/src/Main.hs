module Main where

import Data.Text.Encoding (encodeUtf8)
import Data.Text.Lazy (toStrict)
import Reflex.Dom (run, mainWidgetWithCss)

import App (app)
import Style (cssText)

main :: IO ()
main = mainWidgetWithCss (encodeUtf8 $ toStrict cssText) app
