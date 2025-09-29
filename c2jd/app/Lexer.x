-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

-- Lexes output from cpp -dM

{
{-# LANGUAGE NoDuplicateRecordFields #-}
{-# LANGUAGE FieldSelectors #-}
{-# LANGUAGE ImplicitPrelude #-}
{-# LANGUAGE NoStrictData #-}
{-# OPTIONS_GHC -O2 #-}

module Lexer(lexPpOutput) where
import Token
import Data.Text.Read qualified as TextRead
import Data.Text (Text)
import Data.Text qualified as T
import Data.Int (Int32)
import Data.Functor ((<&>))
import Data.Foldable (Foldable (foldl'))
import Control.Arrow ((<<<), (>>>))
import Data.Char(ord, isSpace)
}

%wrapper "monad-strict-text"
%encoding "latin1"

$digit = 0-9
$hexdigit = [0-9a-fA-F]
$alpha = [a-zA-Z]
$lowercase = [a-z]
$CAPS = [A-Z]
$whitespace = [\ \t\f\v]
$newline = [\r\n]
$symbol = [\!\%\&\*\+\/\<\=\>\^\|\-\~\`\@\$\{\}\[\]\:\;\,\.\?\']

tokens :-

  $whitespace+ ;
  \\ $whitespace* $newline ;
  $newline { tok $ const NewLine }

  "#define" $whitespace+ [$alpha \_] [$alpha $digit \_]* { tok mkDef }
  "#define" $whitespace+ [$alpha \_] [$alpha $digit \_]* "(" { tok mkMacro }

  "##" { tok $ const Concat }
  "#" [$alpha \_] [$alpha $digit \_]* { tok $ Stringify . T.tail }

  "(" { tok $ const LParen }
  ")" { tok $ const RParen }

  $digit* \. [$digit]+ ((e|E) (\-|\+)? $digit+)? (f|F|l|L)? { tok OtherToken }
  $digit+ (((e|E) (\-|\+)? $digit+) | (f|F|l|L)) { tok OtherToken }
  $digit+ (u|U|l|L|ll|LL|lu|LU|llu|LLU|ul|UL|ull|ULL)? { tok OtherToken }
  "0" [xX] $hexdigit+ \. [$hexdigit]+ ((p|P) (\-|\+)? $hexdigit+)? (f|F|l|L)? { tok OtherToken }
  "0" [xX] [$hexdigit]+ (((p|P) (\-|\+)? $hexdigit+)? | (f|F|l|L)?) { tok OtherToken }
  "0" [xX] $hexdigit+ (u|U|l|L|ll|LL|lu|LU|llu|LLU|ul|UL|ull|ULL)? { tok OtherToken }

  $symbol+ { tok OtherToken }
  
  [$alpha \_] [$alpha $digit \_]* { tok Ident }  
  
  \" ([^\"] | (\\\"))* \" { tok OtherToken }
  
  \' \\ [^\'] \' { tok OtherToken }
  \' ([^\'] | (\\\'))* \' { tok OtherToken }

{

lexPpOutput :: Text -> Either String [Token']
lexPpOutput src = run
  where
    -- Repeatedly scan tokens until alexMonadScan returns Nothing
    go :: Alex [Token']
    go = do
      tokenMaybe <- alexMonadScan
      case tokenMaybe of
        Nothing -> pure []
        Just t -> fmap (t :) go
    run = 
      case runAlex src go of
        Right x -> Right x
        Left e -> Left $ 'L' : tail e

-- Nothing represents EOF, tells go in lexPpOutput to stop
alexEOF :: Alex (Maybe Token')
alexEOF = pure Nothing

-- 
tok :: (Text -> Token) -> AlexInput -> Int -> Alex (Maybe Token')
tok mkTok (AlexPn _ row _, _, _, remainingText) len =
  let tokenText = T.take len remainingText in
    pure $ Just (mkTok tokenText, row)

mkDef :: Text -> Token
mkDef = T.drop 7 >>> T.dropWhile (isSpace) >>> Define

mkMacro :: Text -> Token
mkMacro = T.drop 7 >>> T.dropWhile (isSpace) >>> (\x -> T.take (T.length x - 1) x) >>> DefineMacro

}
