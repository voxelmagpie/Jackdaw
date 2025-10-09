-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import Ast qualified as A
import Cc
import CmdLine
import Control.Concurrent (getNumCapabilities)
import Control.Concurrent.Async (async, wait)
import Control.Exception (catch, handle, throwIO, try)
import Control.Monad (forM, forM_, unless, when)
import Control.Monad.Reader (ReaderT (runReaderT))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Char (isSpace)
import Data.HashMap.Strict qualified as HM
import Data.List (find, isSuffixOf, sort, uncons)
import Data.Maybe (fromMaybe)
import Data.String (IsString (..))
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8')
import Data.Text.IO qualified as TIO
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Ex
import GHC.IO.Exception (ExitCode (ExitSuccess))
import Help
import Hir qualified as H
import Lexer (lexJackdaw)
import Lower (runLowerer)
import Names
import Parser (parseJackdawAst)
import Prelude2
import System.Directory (createDirectoryIfMissing, getSymbolicLinkTarget, getTemporaryDirectory, listDirectory, removeDirectoryRecursive, removeFile)
import System.Environment (getArgs)
import System.Exit (die)
import System.FilePath (dropExtension, takeBaseName, takeDirectory, takeExtension, takeFileName, (<.>), (</>))
import System.IO (IOMode (WriteMode), hClose, hPutStrLn, openBinaryTempFile, withFile)
import System.Process (callProcess)
import System.Process.Text (readProcessWithExitCode)
import Tc.Borrow qualified as Bw
import Tc.Error (Err (Err), ErrorOrigin (BorrowCheckerError, TypeCheckerError))
import Tc.State (convertBwCheckFnTypeIO)
import Tc.Tc (runTc)
import Timings
import Tokens (prettyPrintToken)

writeIr :: Bool
writeIr = False

writeAsts :: Bool
writeAsts = False

printStagesDone :: Bool
printStagesDone = False

printFailureTestErrors :: Bool
printFailureTestErrors = False

-- For profiling
dontActuallyRunTests :: Bool
dontActuallyRunTests = False

compileAndRunTestProgram :: Config -> FilePath -> Text -> [(Namespace, A.Ast)] -> String -> IO (Timings, Text)
compileAndRunTestProgram cfg cPreludePath cPreludeHSrc stLib name = do
  let name' = fromString name
  let outputDir = "tests_output" </> name'
  putStrLn $ "> " <> name
  createDirectoryIfMissing False outputDir

  let srcPath = ("res" </> "tests" </> name') <.> ".jackdaw"
  src <- BS.readFile srcPath >>= byteStringToTextOrThrow

  startTime <- getCurrentTime

  (c, testTimings1) <- compileToC stLib srcPath (Just src) outputDir (name == "stlib_test") False cfg.uncheckedArithmetic

  let cFilePath = (outputDir </> name') <.> ".c"
  withFile cFilePath WriteMode $ \h -> do
    TIO.hPutStrLn h cPreludeHSrc
    TIO.hPutStrLn h c

  let exePath = outputDir </> name'

  ccStartTime <- getCurrentTime

  cWarnings <-
    if dontActuallyRunTests
      then pure ""
      else do
        runCc
          $ CcArgs
            { cc = fromMaybe "cc" cfg.cc,
              buildMode = BuildDebug,
              strip = False,
              destMaybe = Just exePath,
              cPreludePath = cPreludePath,
              srcPathOrSrc = Left cFilePath,
              cSharedLibs = [],
              warnings = cfg.cWarnings,
              singleThreaded = cfg.singleThreaded
            }

  ccEndTime <- getCurrentTime
  let ccTime = diffUTCTime ccEndTime ccStartTime

  when printStagesDone $ putStrLn "C compiler done"

  executeStartTime <- getCurrentTime
  unless dontActuallyRunTests $ do
    let !tests = findTests src
    forM_ tests $ runTest exePath
  executeEndTime <- getCurrentTime
  let executeTime = diffUTCTime executeEndTime executeStartTime

  pure
    ( testTimings1
        { cc = ccTime,
          execute = executeTime,
          total = diffUTCTime executeEndTime startTime
        },
      cWarnings
    )

data Test = Test Text Text -- input, expected output

-- Lines at start of file beginning with "//!" are tests
findTests :: Text -> [Test]
findTests src = parseTestLine <$> testLines
  where
    lines' = T.lines src
    testLines = filter (T.isPrefixOf "//!") lines'

-- //! INPUT # EXPECTED-OUTPUT
parseTestLine :: Text -> Test
parseTestLine line = Test (T.strip $ must $ head x) output
  where
    x = T.drop 3 line & T.split (== '#')
    _ = assert (length x == 2) ()
    output = T.strip (x !! 1) & T.replace "\\n" "\n"

runTest :: FilePath -> Test -> IO ()
runTest path (Test input expected) = do
  (exitCode, resultStr, err) <- readProcessWithExitCode path ["abc"] (input <> "\n")
  unless (exitCode == ExitSuccess) $ throwIO $ CompileException $ "(test crashed)\n" <> err

  let result = T.strip resultStr
  when (result /= expected) $ throwIO $ CompileException $ "Expected '" <> expected <> "', got '" <> result <> "'"

-- Number of buckets is either bucketCount or bucketCount-1
splitListIntoBuckets :: Int -> [a] -> [[a]]
splitListIntoBuckets bucketCount xs | bucketCount <= 1 = [xs]
splitListIntoBuckets bucketCount xs = zs
  where
    fits = length xs `mod` bucketCount == 0
    bucketSize = max 1 $ if fits then length xs `div` bucketCount else length xs `div` (bucketCount - 1)
    ys = [0 :: Int .. (bucketCount - 2)] <&> \i -> take bucketSize (drop (i * bucketSize) xs)
    ys' = ys ++ [drop ((bucketCount - 1) * bucketSize) xs] -- Last bucket may be > bucketSize
    zs = filter notNull ys' -- Last bucket may be empty

runTests :: Config -> FilePath -> IO ()
runTests cfg stLibDir = do
  createDirectoryIfMissing False "tests_output"
  removeDirectoryRecursive "tests_output"
  createDirectoryIfMissing False "tests_output"

  stLibStartTime <- getCurrentTime
  (stLib, stLibTimings) <- catch (getPackageAsts "stlib" stLibDir) $ \(CompileException e) -> die $ T.unpack e
  stLibEndTme <- getCurrentTime
  TIO.putStrLn $ "Stlib parsed in " <> tShow (diffUTCTime stLibEndTme stLibStartTime) <> " seconds"

  startTime <- getCurrentTime
  TIO.putStrLn "Running tests..."

  tests <- listDirectory "res/tests" <&> filter (".jackdaw" `isSuffixOf`)
  let testNames = tests <&> dropLast (T.length ".jackdaw") & sort

  threadCount <- getNumCapabilities

  let allTestGroups = splitListIntoBuckets threadCount testNames
  TIO.putStrLn $ T.concat ["Using ", tShow $ length allTestGroups, " threads"]

  let cPreludePath = stLibDir </> "prelude.c"
  let cPreludeHPath = stLibDir </> "prelude.h"
  cPreludeHSrc <- BS.readFile cPreludeHPath >>= byteStringToTextOrThrow

  -- Returns either an error message or the names and timings of the tests
  let runTestBatch :: [String] -> IO (Either Text [(Text, Timings, Text)])
      runTestBatch names = do
        x <- try @CompileException $ forM names $ \name ->
          handle (\(CompileException e) -> throwIO $ CompileException $ "Test " <> T.pack name <> " failed:\n\n" <> e)
            $ compileAndRunTestProgram cfg cPreludePath cPreludeHSrc stLib name
            <&> \(t, w) -> (T.pack name, t, w)

        case x of
          Left (CompileException e) -> pure $ Left e
          Right y -> pure $ Right y

  as <- forM allTestGroups $ \name -> async (runTestBatch name)

  timings' <- forM as $ \a -> do
    r <- wait a
    case r of
      Left msg -> die $ T.unpack msg
      Right xs -> do
        forM_ (thd3 <$> xs) $ \w ->
          unless (T.null w) $ TIO.putStrLn w
        pure $ fst2Of3 <$> xs

  let timings = ("stlib", stLibTimings) : concat timings'
  writeTimingsFile "tests_output/timings.txt" timings

  handle (\(CompileException e) -> die $ T.unpack e) $ do
    testTypeCheckFailure stLib
    testBorrowCheckFailure stLib

  endTime <- getCurrentTime

  TIO.putStrLn $ "All tests passed in " <> tShow (diffUTCTime endTime startTime) <> " seconds"

testBorrowCheckFailure :: [(Namespace, A.Ast)] -> IO ()
testBorrowCheckFailure stLib = do
  when printFailureTestErrors $ putStrLn ""
  putStrLn "> Borrow checker tests"
  when printFailureTestErrors $ putStrLn ""

  fullSrc <- BS.readFile "res/bw_chk_tests.jackdaw" >>= byteStringToTextOrThrow
  let tests = T.splitOn "// --- //\n" fullSrc <&> T.dropWhile isSpace

  forM_ tests $ \src -> do
    tokens <- case lexJackdaw "bw_chk_tests.jackdaw" src of
      (Left e) -> throwIO $ CompileException $ "bw_chk_tests.jackdaw lexer error:\n" <> T.pack e <> "\n" <> src
      (Right a) -> pure a
    let astMaybe = runReaderT (parseJackdawAst tokens) "bw_chk_tests.jackdaw"
    ast <- case astMaybe of
      (Left (e, _)) -> throwIO $ CompileException $ "bw_chk_tests.jackdaw parser error:\n" <> e <> "\n" <> src
      (Right a) -> pure a
    tcRes <- runTc (convertBwCheckFnTypeIO Bw.runBorrowChecker) (HM.fromList $ (Namespace "@/main", ast) : stLib) False False
    case tcRes of
      Right _ -> throwIO $ CompileException $ "Borrow checker failure test did not fail:\n" <> src
      Left es -> do
        let errs = T.intercalate ",\n" (es <&> \(Err _ _ s) -> s)
        unless (all (\(Err o _ _) -> o == BorrowCheckerError) es)
          $ throwIO
          $ CompileException
          $ "bw_chk_tests.jackdaw unexpected error:\n"
          <> errs
          <> "\n"
          <> src
        when printFailureTestErrors
          $ TIO.putStrLn errs
          >> TIO.putStrLn "--"

testTypeCheckFailure :: [(Namespace, A.Ast)] -> IO ()
testTypeCheckFailure stLib = do
  when printFailureTestErrors $ putStrLn ""
  putStrLn "> Type checker tests"
  when printFailureTestErrors $ putStrLn ""
  fullSrc <- BS.readFile "res/tc_tests.jackdaw" >>= byteStringToTextOrThrow
  let tests = T.splitOn "// --- //\n" fullSrc <&> T.dropWhile isSpace

  forM_ tests $ \src -> do
    tokens <- case lexJackdaw "tc_tests.jackdaw" src of
      (Left e) -> throwIO $ CompileException $ "tc_tests.jackdaw lexer error:\n" <> T.pack e <> "\n" <> src
      (Right a) -> pure a
    let astMaybe = runReaderT (parseJackdawAst tokens) "tc_tests.jackdaw"
    ast <- case astMaybe of
      (Left (e, _)) -> throwIO $ CompileException $ "tc_tests.jackdaw parser error:\n" <> e <> "\n" <> src
      (Right a) -> pure a
    tcRes <- runTc (convertBwCheckFnTypeIO Bw.runBorrowChecker) (HM.fromList $ (Namespace "@/main", ast) : stLib) False False
    case tcRes of
      Right _ -> throwIO $ CompileException $ "Type checker failure test did not fail:\n" <> src
      Left es -> do
        let errs = T.intercalate ",\n" (es <&> \(Err _ _ s) -> s)
        unless (all (\(Err o _ _) -> o == TypeCheckerError) es)
          $ throwIO
          $ CompileException
          $ "tc_tests.jackdaw unexpected error:\n"
          <> errs
          <> "\n"
          <> src
        when printFailureTestErrors
          $ TIO.putStrLn errs
          >> TIO.putStrLn "--"

byteStringToTextOrThrow :: ByteString -> IO Text
byteStringToTextOrThrow bs = case decodeUtf8' bs of
  Left e -> throwIO $ CompileException $ tShow e
  Right x -> pure x

-- Parses a Jackdaw source file from a FilePath or Text
parseFile :: FilePath -> Maybe Text -> FilePath -> IO (A.Ast, Timings)
parseFile srcPath srcMaybe dumpDir = do
  !src <- case srcMaybe of
    Nothing -> BS.readFile srcPath >>= byteStringToTextOrThrow
    Just x -> pure x

  let name = dropExtension $ takeFileName srcPath

  lexingStartTime <- getCurrentTime

  let srcPath' = T.pack srcPath
  let tokensMaybe = lexJackdaw srcPath src
  !tokens <- case tokensMaybe of
    (Left e) -> throwIO $ CompileException $ T.pack e <> " in " <> srcPath'
    (Right a) -> pure a

  lexingEndTime <- getCurrentTime

  when printStagesDone $ putStrLn "Lexing done"

  when writeAsts
    $ do
      when (dumpDir /= "") $ createDirectoryIfMissing False dumpDir
      withFile (dumpDir </> name <.> ".tokens.txt") WriteMode
        $ flip TIO.hPutStr
        $ T.unlines
        $ fmap (fst >>> prettyPrintToken) tokens

  when writeAsts $ do
    when (dumpDir /= "") $ createDirectoryIfMissing False dumpDir
    withFile (dumpDir </> name <.> ".tokens.hs.txt") WriteMode
      $ flip hPutStrLn
      $ show tokens

  parsingStartTime <- getCurrentTime

  let astMaybe = runReaderT (parseJackdawAst tokens) srcPath
  !ast <- case astMaybe of
    (Left (e, _)) ->
      throwIO $ CompileException e
    (Right a) ->
      pure a

  parsingEndTime <- getCurrentTime

  when printStagesDone $ putStrLn "Parsing done"

  when writeAsts $ do
    when (dumpDir /= "") $ createDirectoryIfMissing False dumpDir
    withFile (dumpDir </> name <.> ".ast.hs.txt") WriteMode
      $ flip hPutStrLn
      $ show ast

  pure
    ( ast,
      Timings
        { lexing = diffUTCTime lexingEndTime lexingStartTime,
          parsing = diffUTCTime parsingEndTime parsingStartTime,
          typeChecking = def,
          transpiling = def,
          cc = def,
          execute = def,
          total = diffUTCTime parsingEndTime lexingStartTime
        }
    )

findSrcFiles :: FilePath -> Text -> FilePath -> IO ([(Namespace, A.Ast)], Timings)
findSrcFiles dir pkg dumpDir = do
  filesRelPath <- listDirectory dir <&> filter (takeExtension >>> (== ".jackdaw"))
  let filesAbsPath = (dir </>) <$> filesRelPath
  let namespaces =
        filesRelPath <&> \path ->
          Namespace $ "@" <> pkg <> "/" <> T.pack (takeBaseName path)

  as <- forM (zip namespaces filesAbsPath) $ \(ns, path) -> do
    async (parseFile path Nothing dumpDir) <&> (ns,)

  xs <- forM as $ \(ns, a) -> do
    (ast, timings) <- wait a
    pure (ns, ast, timings)

  pure (fst2Of3 <$> xs, mconcat $ thd3 <$> xs)

getPackageAsts :: String -> FilePath -> IO ([(Namespace, A.Ast)], Timings)
getPackageAsts name path = findSrcFiles path (T.pack name) (name <> "_asts")

compileToC :: [(Namespace, A.Ast)] -> FilePath -> Maybe Text -> FilePath -> Bool -> Bool -> Bool -> IO (Text, Timings)
compileToC depsAsts srcPath srcMaybe dumpDir forceCheckStLib addDbgLineNumbers uncheckedArithmetic = do
  startTime <- getCurrentTime

  (files, tt) <-
    if takeExtension srcPath == ".jackdaw"
      then do
        (ast, tt) <- parseFile srcPath srcMaybe dumpDir
        pure ([(Namespace "@/main", ast)], tt)
      else do
        findSrcFiles srcPath "" dumpDir

  let name = dropExtension $ takeFileName srcPath

  let printErrs :: [Err] -> IO a
      printErrs es =
        throwIO
          $ CompileException
          $ T.intercalate "\n\n"
          $ es
          <&> \(Err _ _ e) -> e

  typeCheckingStartTime <- getCurrentTime
  tcRes <- runTc (convertBwCheckFnTypeIO Bw.runBorrowChecker) (HM.fromList $ files ++ depsAsts) forceCheckStLib uncheckedArithmetic
  (hir, typeCheckingTime) <- case tcRes of
    Left errs ->
      printErrs errs
    Right hir -> do
      typeCheckingEndTime <- getCurrentTime
      when printStagesDone $ putStrLn "Type checking done"
      text <- H.showIr hir
      when writeIr $ do
        when (dumpDir /= "") $ createDirectoryIfMissing False dumpDir
        withFile (dumpDir </> name <.> ".hir.hs.txt") WriteMode $ flip TIO.hPutStr text
      pure (hir, diffUTCTime typeCheckingEndTime typeCheckingStartTime)

  transpilingStartTime <- getCurrentTime
  c <- runLowerer hir addDbgLineNumbers
  transpilingEndTime <- getCurrentTime
  when printStagesDone $ putStrLn "Transpiling done"
  let transpilingTime = diffUTCTime transpilingEndTime transpilingStartTime

  when printStagesDone $ putStrLn "Transpiling done"

  endTime <- getCurrentTime
  pure
    ( c,
      Timings
        { lexing = tt.lexing,
          parsing = tt.parsing,
          typeChecking = typeCheckingTime,
          transpiling = transpilingTime,
          cc = def,
          execute = def,
          total = diffUTCTime endTime startTime
        }
    )

compile :: Config -> FilePath -> Maybe FilePath -> Bool -> [(String, FilePath)] -> IO ()
compile cfg srcPath exePathMaybe outputTimings packages = do
  let stLibDir = find (fst >>> (== "stlib")) packages & must & snd
  let addDbgLineNumbers = cfg.buildMode == BuildDebug && not cfg.noCppLine

  let srcPathIsFile = takeExtension srcPath == ".jackdaw"
  exePath <- case exePathMaybe of
    Just x -> pure x
    _ ->
      if srcPathIsFile
        then
          pure $ dropExtension srcPath
        else
          pure $ takeDirectory srcPath <> "exe"

  packages' <- forM packages $ \(pkg, path) -> do
    (a, t) <- getPackageAsts pkg path
    pure (T.pack pkg, a, t)

  let outputDir = takeDirectory exePath
  startTime <- getCurrentTime
  (c, timings1) <- compileToC (concatMap snd3 packages') srcPath Nothing outputDir False addDbgLineNumbers cfg.uncheckedArithmetic
  let cPreludePath = stLibDir </> "prelude.c"
  let cPreludeHPath = stLibDir </> "prelude.h"
  cPreludeHSrc <- BS.readFile cPreludeHPath >>= byteStringToTextOrThrow
  let c' = cPreludeHSrc `T.append` c

  cPathOrSrc <-
    if cfg.dumpC
      then do
        let path = exePath ++ ".c"
        TIO.writeFile path c'
        pure $ Left path
      else
        pure $ Right c'

  when cfg.dumpC
    $ TIO.writeFile (exePath ++ ".c") c'

  ccStartTime <- getCurrentTime

  cWarnings <-
    runCc
      $ CcArgs
        { cc = fromMaybe "cc" cfg.cc,
          buildMode = cfg.buildMode,
          strip = cfg.strip,
          destMaybe = Just exePath,
          cPreludePath = cPreludePath,
          srcPathOrSrc = cPathOrSrc,
          cSharedLibs = cfg.cSharedLibs,
          warnings = cfg.cWarnings,
          singleThreaded = cfg.singleThreaded
        }

  when (cfg.cWarnings && not (T.null cWarnings)) $ TIO.putStrLn cWarnings

  ccEndTime <- getCurrentTime
  let ccTime = diffUTCTime ccEndTime ccStartTime

  let timings' = timings1 {cc = ccTime, total = diffUTCTime ccEndTime startTime}
  let timings = ("", timings') : (outerOf3 <$> packages')
  when outputTimings
    $ writeTimingsFile "timings.txt" timings

main :: IO ()
main = do
  args <- getArgs
  case uncons args of
    Nothing -> putStrLn "Jackdaw compiler v0.1.0"
    Just (cmd, args'') -> do
      cfg <- case extractArgs args'' of Left e -> throwIO e; Right x -> pure x

      packages <- case find (fst >>> (== "stlib")) cfg.packages of
        Just _ -> pure cfg.packages
        _ -> do
          -- assume the jackdawc executable and stlib package have been installed to the same directory
          d <- getSymbolicLinkTarget "/proc/self/exe" <&> (takeDirectory >>> (</> "stlib"))
          pure $ ("stlib", d) : cfg.packages

      case cmd of
        "help" ->
          TIO.putStrLn helpFile
        "run-tests" ->
          runTests cfg "res/stlib"
        "build" -> do
          srcPath <- case cfg.inputFileOrDir of
            Nothing -> die "Expected path to source file"
            Just x -> pure x

          handle @CompileException (un >>> T.unpack >>> die)
            $ compile cfg srcPath cfg.exePath cfg.outputTimings packages
          pure ()
        "run" -> do
          srcPath <- case cfg.inputFileOrDir of
            Nothing -> die "Expected path to source file"
            Just x -> pure x

          case cfg.exePath of
            Just p -> do
              handle @CompileException (un >>> T.unpack >>> die)
                $ compile cfg srcPath cfg.exePath cfg.outputTimings packages
              callProcess p cfg.args
            _ -> do
              tmpDir <- getTemporaryDirectory
              (exePath, exeFile) <- openBinaryTempFile tmpDir "jackdaw"
              hClose exeFile

              handle @CompileException (un >>> T.unpack >>> die)
                $ compile cfg srcPath (Just exePath) cfg.outputTimings packages

              callProcess exePath cfg.args
              removeFile exePath
        _ -> die $ "Unknown command: '" <> cmd <> "'\nRun 'jackdawc help' to get a list of commands"
