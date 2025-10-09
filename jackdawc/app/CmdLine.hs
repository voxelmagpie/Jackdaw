-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module CmdLine where

import Control.Exception (Exception)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.State (State, gets, modify', runState)
import Data.List (elemIndex, isPrefixOf)
import Data.Maybe (fromMaybe)
import Data.Text qualified as T
import Prelude2

newtype ArgsException = ArgsException Text
  deriving (Show)
  deriving anyclass (Exception)

-- If an arg begins with "-" then it is a setting, otherwise it is a file path/name
data Arg = ArgFilePath String | ArgSetting String (Maybe String)

type ArgProcessor = ExceptT ArgsException (State ([Arg], Config))

getNextArg :: ArgProcessor (Maybe Arg)
getNextArg =
  gets fst >>= \case
    [] -> pure Nothing
    (y : ys) -> do
      modify' $ first $ const ys
      pure $ Just y

peekNextArg :: ArgProcessor (Maybe Arg)
peekNextArg = gets (head . fst)

-- For getting args after "--" to pass to the compiled program
getAllRemainingArgStrings :: ArgProcessor [String]
getAllRemainingArgStrings = do
  xs <- gets fst
  modify' $ first (const [])
  pure $ xs <&> \case
    ArgFilePath x -> x
    ArgSetting x Nothing -> x
    ArgSetting x (Just y) -> x <> "=" <> y

-- e.g. jackdawc build foo.jackdaw --build-mode=debug lol.jackdaw -a --stlib res/stlib/
extractArgs :: [String] -> Either ArgsException Config
extractArgs xs = case runState (runExceptT go1) (xs', def) of
  (Left err, _) -> Left err
  (Right _, (_, y)) -> Right y
  where
    go1 :: ArgProcessor ()
    go1 = do
      -- Get source file or directory
      peekNextArg >>= \case
        Just (ArgFilePath path) -> do
          _ <- getNextArg
          modify' $ second $ \s -> s {inputFileOrDir = Just path}
          peekNextArg >>= \case
            Just (ArgFilePath _) -> throwError $ ArgsException "Multiple input files/directories"
            _ -> go2
        _ -> go2

    go2 :: ArgProcessor ()
    go2 = do
      -- Get configuration argument
      getNextArg >>= \case
        Just (ArgSetting option valueMaybe) -> do
          case option of
            "--build-mode" -> do
              mode <- case fromMaybe "" valueMaybe of
                "debug" -> pure BuildDebug
                "unopt" -> pure BuildUnopt
                "opt" -> pure BuildOpt
                "small" -> pure BuildSmall
                _ -> throwError $ ArgsException "Expected one of: debug, unopt, opt, small"
              modify' $ second $ \s -> s {buildMode = mode}
            "--strip" -> do modify' $ second $ \s -> s {strip = True}
            "-s" -> do modify' $ second $ \s -> s {strip = True}
            "--exe" -> do
              getNextArg >>= \case
                Just (ArgFilePath path) -> do
                  modify' $ second $ \s -> s {exePath = Just path}
                _ -> throwError $ ArgsException "Expected output executable file path"
            x | "-l" `isPrefixOf` x ->
              modify' $ second $ \s -> s {cSharedLibs = s.cSharedLibs ++ [x]}
            "--dump-c" ->
              modify' $ second $ \s -> s {dumpC = True}
            "--no-cpp-line" ->
              modify' $ second $ \s -> s {noCppLine = True}
            "--cc" -> do
              getNextArg >>= \case
                Just (ArgFilePath path) -> do
                  modify' $ second $ \s -> s {cc = Just path}
                _ -> throwError $ ArgsException "Expected C compiler command or file path"
            "--c-warnings" ->
              modify' $ second $ \s -> s {cWarnings = True}
            "--unchecked-arithmetic" ->
              modify' $ second $ \s -> s {uncheckedArithmetic = True}
            "--timings" ->
              modify' $ second $ \s -> s {outputTimings = True}
            "--single-threaded" ->
              modify' $ second $ \s -> s {singleThreaded = True}
            "--" -> do
              as <- getAllRemainingArgStrings
              modify' $ second $ \s -> s {args = as}
            "--add-package" -> do
              name <-
                getNextArg >>= \case
                  Just (ArgFilePath name) -> pure name
                  _ -> throwError $ ArgsException "Expected name"
              path <-
                getNextArg >>= \case
                  Just (ArgFilePath path) -> pure path
                  _ -> throwError $ ArgsException "Expected path"

              modify' $ second $ \s -> s {packages = (name, path) : s.packages}
            _ -> throwError $ ArgsException $ "Unknown configuration option: " <> T.pack option
          go2
        _ -> pure ()
    xs' =
      xs <&> \s ->
        if "-" `isPrefixOf` s
          then case elemIndex '=' s of
            Just i -> ArgSetting (take i s) (Just $ drop (i + 1) s)
            _ -> ArgSetting s Nothing
          else
            ArgFilePath s

data BuildMode = BuildDebug | BuildUnopt | BuildOpt | BuildSmall
  deriving (Show, Eq, Generic)

instance Default BuildMode where
  def = BuildDebug

data Config = Config
  { inputFileOrDir :: Maybe String,
    buildMode :: BuildMode,
    strip :: Bool,
    exePath :: Maybe String,
    cSharedLibs :: [String], -- of form -labc
    args :: [String],
    dumpC :: Bool,
    noCppLine :: Bool,
    cc :: Maybe String,
    cWarnings :: Bool,
    uncheckedArithmetic :: Bool,
    outputTimings :: Bool,
    singleThreaded :: Bool,
    packages :: [(String, FilePath)]
  }
  deriving (Show, Eq, Generic, Default)
