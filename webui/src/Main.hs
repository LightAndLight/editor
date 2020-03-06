{-# language OverloadedStrings #-}
module Main where

import Data.Text.Lazy (toStrict)
import Reflex.Dom ((=:), mainWidgetWithHead, el, elAttr, text)

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
        elAttr "link"
          ("href"=:"https://cdn.jsdelivr.net/npm/bulma@0.8.0/css/bulma.min.css" <>
           "rel"=:"stylesheet"
          )
          (pure ())
        elAttr "script"
          ("defer" =: mempty <>
           "src" =: "https://use.fontawesome.com/releases/v5.3.1/js/all.js"
          )
          (pure ())
        el "style" . text $ toStrict cssText

    )
    app
