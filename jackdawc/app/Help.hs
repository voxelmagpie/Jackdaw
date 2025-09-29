{-# LANGUAGE TemplateHaskell #-}

module Help where

import Data.FileEmbed
import Data.Text (Text)

helpFile :: Text
helpFile = $(embedStringFile "res/help.txt")
