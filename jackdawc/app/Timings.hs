-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-orphans #-}

module Timings where

import Control.Monad (forM_)
import Data.List (sortBy)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Time.Clock (NominalDiffTime)
import Prelude2
import System.IO (IOMode (WriteMode), withFile)

-- Times in seconds
data Timings = Timings
  { lexing :: NominalDiffTime,
    parsing :: NominalDiffTime,
    typeChecking :: NominalDiffTime,
    transpiling :: NominalDiffTime,
    cc :: NominalDiffTime,
    execute :: NominalDiffTime,
    total :: NominalDiffTime
  }
  deriving (Show, Generic, Default)

instance Semigroup Timings where
  x <> y =
    Timings
      { lexing = x.lexing + y.lexing,
        parsing = x.parsing + y.parsing,
        typeChecking = x.typeChecking + y.typeChecking,
        transpiling = x.transpiling + y.transpiling,
        cc = x.cc + y.cc,
        execute = x.execute + y.execute,
        total = x.total + y.total
      }

instance Monoid Timings where
  mempty = Timings def def def def def def def

data TimingsPct = TimingsPct
  { lexing :: Float,
    parsing :: Float,
    typeChecking :: Float,
    transpiling :: Float,
    cc :: Float,
    execute :: Float
  }
  deriving (Show, Generic, Default)

timingsPctToText :: TimingsPct -> Text
timingsPctToText x =
  T.unlines
    [ "Lexing: " <> tShow x.lexing <> "%",
      "Parsing: " <> tShow x.parsing <> "%",
      "Type Checking: " <> tShow x.typeChecking <> "%",
      "Transpiling: " <> tShow x.transpiling <> "%",
      "Code Generation: " <> tShow x.cc <> "%",
      "Execution: " <> tShow x.execute <> "%"
    ]

-- Rounds to 1dp
toPct :: Float -> Float
toPct x = let y :: Int = round (x * 1000); z :: Float = fromIntegral y in z / 10

timingsToPct :: Timings -> TimingsPct
timingsToPct tt =
  let total = realToFrac tt.total
   in TimingsPct
        { lexing = toPct $ realToFrac tt.lexing / total,
          parsing = toPct $ realToFrac tt.parsing / total,
          typeChecking = toPct $ realToFrac tt.typeChecking / total,
          transpiling = toPct $ realToFrac tt.transpiling / total,
          cc = toPct $ realToFrac tt.cc / total,
          execute = toPct $ realToFrac tt.execute / total
        }

instance Default NominalDiffTime where
  def = 0

writeTimingsFile :: FilePath -> [(Text, Timings)] -> IO ()
writeTimingsFile path timings = withFile path WriteMode
  $ \h -> do
    let overallTimings = timingsToPct $ foldl' (<>) def $ snd <$> timings
    let totalTime = sum $ timings <&> (snd >>> (.total) >>> realToFrac)

    TIO.hPutStrLn h "Total"
    TIO.hPutStrLn h "--------"
    TIO.hPutStrLn h $ timingsPctToText overallTimings
    TIO.hPutStrLn h ""

    let timingsWithPct = timings <&> (\(n, t) -> (n, t, toPct $ realToFrac t.total / totalTime))
    let timingsWithPctSorted = sortBy (\(_, _, p1) (_, _, p2) -> compare p2 p1) timingsWithPct

    forM_ timingsWithPctSorted $ \(name, t, pct) -> do
      TIO.hPutStrLn h $ (if T.null name then "(app)" else name) <> ": " <> tShow pct <> "%"
      TIO.hPutStrLn h "--------"
      TIO.hPutStrLn h $ timingsPctToText $ timingsToPct t