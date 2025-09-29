-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

{
{-# LANGUAGE NoDuplicateRecordFields #-}
{-# LANGUAGE FieldSelectors #-}
{-# LANGUAGE ImplicitPrelude #-}
{-# LANGUAGE NoStrictData #-}
{-# OPTIONS_GHC -O2 #-}

module Lexer(lexJackdaw) where
import Tokens
import Data.Text.Read qualified as TextRead
import Data.Text (Text)
import Data.Text qualified as T
import Names (VName(..), TName(..), OpName(..))
import SrcLoc (SrcLoc(..), SrcRange(..))
import Data.Functor ((<&>))
import Data.Foldable (Foldable (foldl'))
import Control.Arrow ((<<<), (>>>))
import Data.Char(ord)
}

%wrapper "monad-strict-text"
%encoding "latin1"

$digit = 0-9
$hexdigit = [0-9a-fA-F]
$alpha = [a-zA-Z]
$lowercase = [a-z]
$CAPS = [A-Z]
$whitespace = [\ \t\n\r\f\v]
$newline = [\r\n]
$symbol = [\`\@\$\(\)\{\}\[\]\:\;\,\.\?]

tokens :-

  "//" [^$newline]* ;
  $whitespace+ ;

  "..." { tok $ const VarArgsToken }

  $symbol  { tok $ Symbol . T.head }

  $digit+ \. [$digit]+ { tok FloatLiteral }
  $digit+ { tok $ parseInt }

  "0" [xX] $hexdigit+ { tok parseHexInt }
  "0" [bB] [01]+ { tok parseBinInt }

  "!" { tok $ Op . OpName }
  "%" { tok $ Op . OpName }
  "&" { tok $ Op . OpName }
  "*" { tok $ Op . OpName }
  "+" { tok $ Op . OpName }
  "-" { tok $ Op . OpName }
  "/" { tok $ Op . OpName }
  "^" { tok $ Op . OpName }
  "|" { tok $ Op . OpName }
  "~" { tok $ Op . OpName }
  "++" { tok $ Op . OpName }
  "+%" { tok $ Op . OpName }
  "-%" { tok $ Op . OpName }
  "*%" { tok $ Op . OpName }
  "<" { tok $ Op . OpName }
  ">" { tok $ Op . OpName }

  "%=" { tok $ Op . OpName }
  "&=" { tok $ Op . OpName }
  "*=" { tok $ Op . OpName }
  "+=" { tok $ Op . OpName }
  "-=" { tok $ Op . OpName }
  "/=" { tok $ Op . OpName }
  "^=" { tok $ Op . OpName }
  "|=" { tok $ Op . OpName }
  "~=" { tok $ Op . OpName }
  "++=" { tok $ Op . OpName }
  "+%=" { tok $ Op . OpName }
  "-%=" { tok $ Op . OpName }
  "*%=" { tok $ Op . OpName }
  "<<=" { tok $ Op . OpName }
  ">>=" { tok $ Op . OpName }

  "=" { tok $ Symbol . T.head }
  "==" { tok $ Op . OpName }
  "!=" { tok $ Op . OpName }
  "<=" { tok $ Op . OpName }
  ">=" { tok $ Op . OpName }
  "<<" { tok $ Op . OpName }
  ">>" { tok $ Op . OpName }
  
  [$lowercase \_] [$alpha $digit \_]* { tok $ IdentOrKw . VName }  
  $CAPS [$alpha $digit \_]* { tok $ TypeName . TName }
  
  \" ([^\"] | (\\\"))* \" { tok' mkStringTok }
  
  \' \\ [^\'] \' { tok' mkEscapeCharLit }
  \' [^\'\\] \' { tok $ CharLiteral . T.head . stripQuotes }

{

type TokenL' = (Token, (SrcLoc, SrcLoc))

-- Only allow non-control-code ASCII for now. Will either support unicode later or switch to ByteString input.
hasInvalidChars :: Text -> Bool
hasInvalidChars = T.unpack >>> (any isInvalid)
  where
    isInvalid c = (ord c < 32 && not (c `elem` ['\t', '\n', '\r'])) || ord c > 127 

lexJackdaw :: FilePath -> Text -> Either String [TokenL]
lexJackdaw fileName src = 
  if hasInvalidChars src then 
    Left "File contains non-ASCII or null/control character(s)" 
  else 
    run
  where
    -- Repeatedly scan tokens until alexMonadScan returns Nothing
    go :: Alex [TokenL']
    go = do
      tokenMaybe <- alexMonadScan
      case tokenMaybe of
        Nothing -> pure []
        Just t -> fmap (t :) go
    run = 
      case runAlex src go of
        Right x -> Right $ x <&> \(t, (a, b)) -> (t, SrcRange fileName a b)
        Left e -> Left $ 'L' : tail e

-- Nothing represents EOF, tells go in lexJackdaw to stop
alexEOF :: Alex (Maybe TokenL')
alexEOF = pure Nothing

-- 
tok :: (Text -> Token) -> AlexInput -> Int -> Alex (Maybe TokenL')
tok mkTok (pos, _, _, remainingText) len =
  let tokenText = T.take len remainingText in
    pure $ Just (mkTok tokenText, makeSrcRange pos len)

tok' :: (Text -> Alex Token) -> AlexInput -> Int -> Alex (Maybe TokenL')
tok' mkTok (pos, _, _, remainingText) len = do
  let tokenText = T.take len remainingText
  t <- mkTok tokenText
  pure $ Just (t, makeSrcRange pos len)


makeSrcRange :: AlexPosn -> Int -> (SrcLoc, SrcLoc)
makeSrcRange (AlexPn i row _) len = (l, r)
  where
    l = SrcLoc row i
    r = SrcLoc row (i+len-1)


-- Parsing cannot fail as the lexer rule guarantees that it is a valid number
parseInt :: Text -> Token
parseInt s = case TextRead.decimal s of
  Left e -> error e
  Right (x, _) -> IntLiteral x

parseHexInt :: Text -> Token
parseHexInt s = case TextRead.hexadecimal s of
  Left e -> error e
  Right (x, _) -> IntLiteral x

parseBinInt :: Text -> Token
parseBinInt textWithPrefix = IntLiteral result'
  where
    chars = T.unpack $ T.drop 2 textWithPrefix
    
    f (result, add) '0' = (result, add*2)
    f (result, add) _ = (result + add, add*2)

    (result', _) = foldl' f (0 :: Integer, 1) $ reverse chars 

stripQuotes :: Text -> Text
stripQuotes t =  T.tail $ T.take (T.length t - 1) t 

-- TODO \uXXXX and \UXXXXXX
mkEscapeCharLit :: Text -> Alex Token
mkEscapeCharLit s = do
  let c = T.head $ T.drop 2 s 
  getEscChar c <&> CharLiteral

getEscChar :: Char -> Alex Char
getEscChar = \case
  'a' -> pure '\a'
  'b' -> pure '\b'
  'f' -> pure '\f'
  'n' -> pure '\n'
  'r' -> pure '\r'
  't' -> pure '\t'
  '"' -> pure '\"'
  '\'' -> pure '\''
  '\\' -> pure '\\'
  _ -> alexError "Invalid escape character"

-- Strips quotation marks and processes escape characters
mkStringTok :: Text -> Alex Token
mkStringTok s = (StringLiteral . T.pack) <$> go (T.unpack $ stripQuotes s)
  where
    go :: String -> Alex String
    go ('\\' : x : xs) = do
      c <- getEscChar x
      (c :) <$> go xs
    go (x : xs) = (x :) <$> go xs
    go [] = pure []


}
