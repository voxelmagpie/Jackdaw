-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Names where

import Data.Char (isAsciiLower, isAsciiUpper)
import Data.HashTable.IO qualified as HT
import Data.Text qualified as T
import Language.C
import Language.C.Data.Ident (Ident (Ident))
import Prelude2
import State

jdKeywords :: [Text]
jdKeywords = ["if", "else", "type", "enum", "struct", "var", "fn", "accessor", "iterator", "const", "alias", "loop", "break", "continue", "ref", "in", "return", "true", "false", "void", "nullptr", "as", "for", "foreach", "and", "or", "yield", "require", "uninitialised", "match", "import", "unsafe", "throw", "try", "catch", "borrow"]

jdReservedTypes :: [Text]
jdReservedTypes = ["Self", "I8", "U8", "I16", "U16", "I32", "U32", "I64", "U64", "F32", "F64", "Bool", "Array", "Slice"]

identToText :: Ident -> Text
identToText (Ident s _ _) = T.pack s

forceTsDefNamingConv :: State -> Ident -> IO Text
forceTsDefNamingConv s x' =
  let x = identToText x'
   in if isTsDefNamingConv x
        then do
          HT.insert s.nameMap x x
          pure x
        else do
          let y = "T" <> x
          HT.insert s.nameMap x y
          pure y

toTsDefNamingConv :: Ident -> Text
toTsDefNamingConv x' =
  let x = identToText x'
   in if isTsDefNamingConv x
        then x
        else "T" <> x

-- Type system definition naming convention, i.e. Abc123_
isTsDefNamingConv :: Text -> Bool
isTsDefNamingConv x = isAsciiUpper (T.head x) && x `notElem` jdReservedTypes

forceVDefNamingConv :: State -> Ident -> IO Text
forceVDefNamingConv s x' =
  let x = identToText x'
   in if isVDefNamingConv x
        then do
          HT.insert s.nameMap x x
          pure x
        else do
          let y = T.cons '_' x
          HT.insert s.nameMap x y
          pure y

toVDefNamingConv :: Ident -> Text
toVDefNamingConv x' =
  let x = identToText x'
   in if isVDefNamingConv x
        then x
        else T.cons '_' x

-- Value definition naming convention, i.e. abc123_
isVDefNamingConv :: Text -> Bool
isVDefNamingConv x = (isAsciiLower (T.head x) || T.head x == '_') && x `notElem` jdKeywords
