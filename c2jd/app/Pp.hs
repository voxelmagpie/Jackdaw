-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Pp (transpilePpDefs) where

import C (CException (CException), evalCExpr, jdTypeToText)
import Control.Exception (Exception, handle, throwIO, try)
import Control.Monad (unless)
import Data.Foldable (Foldable (length), find)
import Data.HashTable.IO qualified as HT
import Data.List (filter)
import Data.Text qualified as T
import Language.C (ParseError (ParseError), builtinIdent, execParser, expressionP, initPos, inputStreamFromString, newNameSupply)
import Names (isTsDefNamingConv, isVDefNamingConv)
import Prelude2
import State
import Token

newtype PpException = PpException Text
  deriving (Show)
  deriving anyclass (Exception)

ppThrow :: Text -> Int -> IO a
ppThrow msg line = throwIO $ PpException $ "Preprocessor parse error on line " <> T.pack (show line) <> " in out/cpp.h: " <> msg

-- Converts the output from cpp -dM into Jackdaw code
transpilePpDefs :: State -> [Token'] -> IO ()
transpilePpDefs s input = do
  gather s input
  flip HT.mapM_ s.ppDefs $ \(name, tokens) -> do
    unless ("__" `T.isPrefixOf` name || null tokens) $ do
      handle (\(PpException e) -> addLine s $ "// Skipped " <> name <> " (" <> e <> ")") $ do
        -- Insert a value in the cache to prevent recursion
        HT.insert s.ppDefsCache name [(Ident name, snd $ head tokens)]
        ts <- processDef s [] tokens [] <&> (fst >>> reverse)
        HT.insert s.ppDefsCache name ts

        unless (null ts) $ do
          -- Get all type names (needed by C compiler for parsing?)
          names'' <- HT.toList s.nameMap <&> (filter (\(_, v) -> isTsDefNamingConv v) >>> (<&> (fst >>> T.unpack)))
          let names' = "__builtin_va_list" : names''
          let names = names' <&> builtinIdent

          let cSrc = tokensToString ts
          case execParser expressionP (inputStreamFromString $ T.unpack cSrc) (initPos "") names newNameSupply of
            Left (ParseError (e, _)) -> do
              traceShowM e
              addLine s $ "// Skipped (C parse error) " <> name <> ": " <> cSrc
            Right (ast, _) ->
              try (evalCExpr s [] ast) >>= \case
                Right x -> do
                  let (t, x') = jdTypeToText x
                  let name' = if isVDefNamingConv name then name else T.cons '_' name
                  addLine s $ "@Unsafe const " <> name' <> ": " <> t <> " = " <> x'
                Left (CException e) -> do
                  addLine s $ "// Skipped (" <> e <> ") " <> name <> ": " <> cSrc

-- Initial parsing pass to get all definitions and macros
gather :: State -> [Token'] -> IO ()
gather s = \case
  -- #define name()...
  ((DefineMacro name, _) : (RParen, _) : xs) -> do
    let (tokens, xs') = getMacroTokens xs []
    HT.insert s.ppMacros name ([], tokens)
    gather s xs'
  -- #define name(args)...
  ((DefineMacro name, _) : xs) -> do
    try (parseParamsList xs []) >>= \case
      Left (PpException e) ->
        addLine s $ "// Skipping " <> name <> ": " <> e
      Right (args, xs') -> do
        let (tokens, xs'') = getMacroTokens xs' []
        HT.insert s.ppMacros name (args, tokens)
        gather s xs''
  -- Self referential macros (#define xyz xyz) can be ignored
  ((Define name, _) : (Ident name', _) : (NewLine, _) : xs)
    | name == name' ->
        gather s xs
  -- #define name ...
  ((Define name, _) : xs) -> do
    let (tokens, xs') = getMacroTokens xs []
    HT.insert s.ppDefs name tokens
    gather s xs'
  [] -> pure ()
  ((_, line) : _) -> ppThrow "Expected '#define NAME'" line

-- Returns (macro-tokens, rest-of-file)
getMacroTokens :: [Token'] -> [Token'] -> ([Token'], [Token'])
getMacroTokens input acc = case input of
  [] -> (reverse acc, input)
  ((NewLine, _) : xs) -> (reverse acc, xs)
  (x : xs) -> getMacroTokens xs (x : acc)

-- Returns (parameters, rest-of-file)
parseParamsList :: [Token'] -> [Text] -> IO ([Text], [Token'])
parseParamsList input acc = case input of
  [] -> ppThrow "EOF in args list" 0
  ((Ident name, _) : (OtherToken ",", _) : xs) -> parseParamsList xs (name : acc)
  ((Ident name, _) : (RParen, _) : xs) -> pure (reverse $ name : acc, xs)
  ((_, l) : _) -> ppThrow "Parse error in args list" l

-- Returns (processed-tokens-rev, rest-of-file)
-- Will never produce Define/Concat/Stringify/Newline/VarArgs
processDef :: State -> [(Text, [Token'])] -> [Token'] -> [Token'] -> IO ([Token'], [Token'])
processDef s args input acc = case input of
  [] -> pure (acc, [])
  ((NewLine, _) : _) -> undefined
  ((Define _, _) : _) -> undefined
  ((DefineMacro _, _) : _) -> undefined
  -- Parenthesis are not parsed, just a regular token
  (x@(LParen, _) : xs) -> processDef s args xs (x : acc)
  (x@(RParen, _) : xs) -> processDef s args xs (x : acc)
  (x@(OtherToken _, _) : xs) -> processDef s args xs (x : acc)
  ((Stringify _, _) : _) -> undefined -- TODO
  ((Ident t, line) : xs) -> do
    (ts, xs') <- processIdent s args xs t line
    case xs' of
      ((Concat, _) : _) -> do
        (t', xs'') <- processConcats s args xs' $ tokensToString ts
        processDef s args xs'' ((Ident t', line) : acc)
      _ ->
        processDef s args xs' (reverse ts ++ acc)
  ((Concat, line) : _) -> ppThrow "Unexpected ##" line

-- Returns (resulting-text, rest-of-input)
processConcats :: State -> [(Text, [Token'])] -> [Token'] -> Text -> IO (Text, [Token'])
processConcats s args xs x = case xs of
  ((Concat, _) : ((Ident i, ln) : xs')) -> do
    (ts, xs'') <- processIdent s args xs' i ln
    processConcats s args xs'' (T.append x $ tokensToString ts)
  _ ->
    pure (x, xs)

-- Returns (new-tokens, rest-of-input)
processIdent :: State -> [(Text, [Token'])] -> [Token'] -> Text -> Int -> IO ([Token'], [Token'])
processIdent s args xs t line = do
  case find ((== t) . fst) args of
    Just (_, ts) ->
      pure (ts, xs)
    _ -> do
      tokensMaybe <- HT.lookup s.ppDefs t
      case tokensMaybe of
        Just ts -> do
          HT.lookup s.ppDefsCache t >>= \case
            Just ts' ->
              pure (ts', xs)
            _ -> do
              HT.insert s.ppDefsCache t [(Ident t, line)]
              (ts', _) <- processDef s [] ts []
              HT.insert s.ppDefsCache t (reverse ts')
              pure (reverse ts', xs)
        _ -> do
          tokensMaybe' <- HT.lookup s.ppMacros t
          case tokensMaybe' of
            Just (params, ts) -> do
              (args', xs') <- parseArgs xs
              unless (length args' == length params) $ ppThrow "Wrong number of args to macro" line
              -- Macro name is added to args mapping to itself to prevent recursion
              (ts', _) <- processDef s ((t, [(Ident t, line)]) : zip params args') ts []
              pure (reverse ts', xs')
            _ ->
              -- Just a name
              pure ([(Ident t, line)], xs)

tokensToString :: [Token'] -> Text
tokensToString = (<&> tokenToText . fst) >>> T.intercalate " "

-- Returns (args-list, rest-of-input)
parseArgs :: [Token'] -> IO ([[Token']], [Token'])
parseArgs = \case
  [] -> ppThrow "EOF in macro args" 0
  ((LParen, _) : xs) -> parseArgs' xs []
  ((_, l) : _) -> ppThrow "Expected '('" l

-- TODO Does this handle nested macro calls? E.g. f(g(x, y))
-- TODO ## and # within arguments
parseArgs' :: [Token'] -> [[Token']] -> IO ([[Token']], [Token'])
parseArgs' xs acc = do
  (ts, xs') <- readTokensUntilCommaOrRParen xs []
  case xs' of
    ((RParen, _) : xs'') -> pure (reverse $ ts : acc, xs'')
    ((OtherToken ",", _) : xs'') -> parseArgs' xs'' (ts : acc)
    _ -> undefined

-- Returns (tokens, rest-of-input)
readTokensUntilCommaOrRParen :: [Token'] -> [Token'] -> IO ([Token'], [Token'])
readTokensUntilCommaOrRParen input acc = case input of
  [] -> ppThrow "EOF in macro arg" 0
  ((RParen, _) : _) -> pure (reverse acc, input)
  ((OtherToken ",", _) : _) -> pure (reverse acc, input)
  (x : xs) -> readTokensUntilCommaOrRParen xs (x : acc)
