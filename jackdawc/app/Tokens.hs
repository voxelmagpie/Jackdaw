-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tokens (Token (..), TokenL, prettyPrintToken) where

import Data.Text qualified as T
import Names
import Prelude2
import SrcLoc

data Token
  = Op OpName -- !, +, etc.
  | IdentOrKw VName -- abc, fn, _a3, etc.
  | TypeName TName -- Abc, etc.
  | FloatLiteral Text
  | IntLiteral Integer
  | StringLiteral Text
  | CharLiteral Char
  | Symbol Char -- @, ?, \, etc.
  | VarArgsToken
  deriving (Eq, Show, Generic)

type TokenL = (Token, SrcRange)

prettyPrintToken :: Token -> Text
prettyPrintToken = \case
  Symbol c -> T.singleton c
  Op (OpName x) -> x
  IdentOrKw (VName x) -> x
  TypeName (TName x) -> x
  FloatLiteral x -> tShow x
  IntLiteral x -> tShow x
  StringLiteral x -> tShow x
  CharLiteral x -> tShow x
  VarArgsToken -> "..."
