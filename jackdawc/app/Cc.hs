-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Cc where

import CmdLine (BuildMode (..))
import Control.Exception (throwIO)
import Control.Monad (unless)
import Data.Maybe (fromMaybe)
import Ex
import GHC.IO.Exception (ExitCode (ExitSuccess))
import Prelude2
import System.Process.Text (readProcessWithExitCode)

data CcArgs = CcArgs
  { cc :: String,
    buildMode :: BuildMode,
    strip :: Bool,
    destMaybe :: Maybe FilePath,
    cPreludePath :: FilePath,
    srcPathOrSrc :: Either FilePath Text,
    cSharedLibs :: [String],
    warnings :: Bool,
    singleThreaded :: Bool
  }

runCc :: CcArgs -> IO Text
runCc args = do
  -- TODO Process does not currently support OsString so using FilePath everywhere
  let destMaybe' = fromMaybe "/dev/null" args.destMaybe
  let w = if args.warnings then ["-Wno-discarded-qualifiers"] else ["-w"]
  let flags1 = case args.buildMode of
        BuildDebug -> ["-g3", "-O0"]
        BuildUnopt -> ["-g0", "-O1"]
        BuildOpt -> ["-g0", "-O2"]
        BuildSmall -> ["-g0", "-Os"]
  let strip' = ["-s" | args.strip]
  let verAndMt = if args.singleThreaded then ["-std=c99"] else ["-std=c11", "-DMULTITHREADED"]
  let a = [args.cPreludePath, "-x", "c"] ++ verAndMt ++ w ++ flags1 ++ strip' ++ ["-o", destMaybe']
  (exitCode, _, err) <- case args.srcPathOrSrc of
    Left path -> do
      readProcessWithExitCode args.cc (a ++ [path] ++ args.cSharedLibs) ""
    Right src ->
      readProcessWithExitCode args.cc (a ++ ["-"] ++ args.cSharedLibs) src

  unless (exitCode == ExitSuccess) $ throwIO $ CompileException err
  pure err
