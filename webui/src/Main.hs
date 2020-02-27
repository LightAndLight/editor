{-# language OverloadedStrings #-}
module Main where

import Data.Text.Encoding (encodeUtf8)
import Data.Text.Lazy (toStrict)
import Reflex.Dom ((=:), run, mainWidgetWithHead, el, elAttr, text)

import App (app)
import Style (cssText)

main :: IO ()
main =
  mainWidgetWithHead
    (do
        elAttr "link"
          ("href"=:"https://fonts.googleapis.com/css?family=Source+Code+Pro&display=swap" <>
           "rel"=:"stylesheet"
          )
          (pure ())
        el "style" . text $ toStrict cssText
    )
    app
