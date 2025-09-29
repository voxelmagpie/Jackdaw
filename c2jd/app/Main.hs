-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at http://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use maybe" #-}

module Main where

import C
import Control.Monad (unless, when)
import Data.HashTable.IO qualified as HT
import Data.IORef (readIORef, writeIORef)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import GHC.IORef (newIORef)
import Language.C
import Lexer
import Pp (transpilePpDefs)
import Prelude2
import State
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.Exit (ExitCode (ExitSuccess), die)
import System.IO (IOMode (WriteMode), openBinaryFile)
import System.Process.Text (readProcessWithExitCode)

main :: IO ()
main = do
  -- File path
  args <- getArgs
  (cFilePath, dumpCFiles) <- case args of
    [x] ->
      pure (x, False)
    [x, y] -> do
      unless (y == "--dump-c") $ die $ "Unknown argument: " <> y
      pure (x, True)
    _ ->
      die "Expected 1 argument (file path) with optional --dump-c argument"

  go cFilePath dumpCFiles

go :: FilePath -> Bool -> IO ()
go cFilePath dumpCFiles = do
  when dumpCFiles $ createDirectoryIfMissing False "./out/"

  -- Translate C code

  cSrc <- do
    (exitCode, src, err) <- readProcessWithExitCode "cpp" ["-P", cFilePath] ""
    unless (exitCode == ExitSuccess) $ die $ T.unpack err
    pure src

  when dumpCFiles $ do
    h <- openBinaryFile "out/c.h" WriteMode
    TIO.hPutStr h cSrc

  let astMaybe = parseC (inputStreamFromString $ T.unpack cSrc) (initPos cFilePath)
  CTranslUnit decls _ <- case astMaybe of
    Left e -> die $ show e
    Right x -> pure x

  s <- State <$> HT.new <*> newIORef [] <*> newIORef 0 <*> HT.new <*> HT.new <*> HT.new <*> HT.new

  translateFile s decls

  -- Translate preprocessor definitions

  cppDefinesSrc <- do
    (exitCode, src, err) <- readProcessWithExitCode "cpp" ["-dM", cFilePath] ""
    unless (exitCode == ExitSuccess) $ die $ T.unpack err
    pure src

  when dumpCFiles $ do
    h <- openBinaryFile "out/cpp.h" WriteMode
    TIO.hPutStr h cppDefinesSrc

  tokens <- case lexPpOutput cppDefinesSrc of
    Left e -> die e
    Right x -> pure x

  transpilePpDefs s tokens

  o <- readIORef s.outputRev <&> reverse
  writeIORef s.outputRev []
  TIO.putStrLn $ T.intercalate "\n" o

  pure ()
