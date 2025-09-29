-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Token where

import Prelude2

data Token
  = Define Text
  | DefineMacro Text
  | Concat
  | Stringify Text
  | LParen
  | RParen
  | Ident Text
  | OtherToken Text
  | NewLine
  deriving (Show, Eq)

type Token' = (Token, Int)

tokenToText :: Token -> Text
tokenToText = \case
  Define x -> "#define " <> x
  DefineMacro x -> "#define " <> x <> "("
  Concat -> "##"
  Stringify x -> "#" <> x
  NewLine -> "\n"
  LParen -> "("
  RParen -> ")"
  Ident x -> x
  OtherToken x -> x
