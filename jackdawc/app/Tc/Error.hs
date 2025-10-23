-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.Error where

import Control.Exception (Exception)
import Control.Monad (when)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.Text qualified as T
import Prelude2
import SrcLoc
import Tc.Ctx (ErrorTrace (..))

data Error = Error ErrorSeverity ErrorOrigin SrcRange Text
  deriving (Show, Generic)

data ErrorOrigin = TypeCheckerError | BorrowCheckerError
  deriving (Show, Generic, Eq)

data ErrorSeverity = SevError | SevWarning | SevHint
  deriving (Show, Generic, Eq)

newtype TcException = TcException ()
  deriving (Show, Generic)
  deriving anyclass (Newtype, Exception)

class (Monad m) => MonadTcError m where
  getErrsListRev :: m [Error]
  consErr :: Error -> m ()
  throwTcException :: TcException -> m a

  throw :: (HasSrcRange r) => ErrorOrigin -> ErrorTrace -> r -> Text -> m a
  throw o et sr msg = do
    addError SevError o et sr msg
    throwTcException $ TcException ()

  addError :: (HasSrcRange r) => ErrorSeverity -> ErrorOrigin -> ErrorTrace -> r -> Text -> m ()
  addError sev o (ErrorTrace loc et) sr msg' = do
    let et' = take (length et - 1) et
    let trace' = et' <&> \(loc', SrcRange fp l _) -> "In " <> fmtLoc loc' <> " at " <> srcLocColour <> T.pack fp <> ":" <> tShow l.line <> reset
    let sev' = case sev of SevError -> errorColour <> "Error"; SevWarning -> warningColour <> "Warning"; SevHint -> noteColour <> "Note"
    let msg =
          T.intercalate "\n"
            $ [sev' <> ": " <> msg' <> reset]
            ++ ["In " <> fmtLoc loc <> " at " <> srcLocColour <> T.pack (filePath sr) <> ":" <> tShow (startLoc sr).line <> reset | not (T.null loc)]
            ++ ["At " <> srcLocColour <> T.pack (filePath sr) <> ":" <> tShow (startLoc sr).line <> reset | T.null loc]
            ++ trace'
    consErr $ Error sev o (srcRangeOf sr sr) msg

    e <- getErrsListRev <&> filter (\(Error s _ _ _) -> s == SevError)
    when (length e > 100) $ throwTcException $ TcException ()

typeColour :: Text
typeColour = "\x1b[36;1m" -- Cyan, bold

locColour :: Text
locColour = "\x1b[0;1m" -- Bold

srcLocColour :: Text
srcLocColour = "\x1b[34;1m" -- Blue, bold

errorColour :: Text
errorColour = "\x1b[31;1m" -- Red, bold

warningColour :: Text
warningColour = "\x1b[33;1m" -- Yellow, bold

noteColour :: Text
noteColour = "\x1b[32;1m" -- Green, bold

reset :: Text
reset = "\x1b[0m"

fmtLocTyp :: [Char] -> String -> String
fmtLocTyp [] s = T.unpack (T.reverse reset) <> s
fmtLocTyp (c : cs) s
  | not (isAsciiLower c) && not (isAsciiUpper c) && (c /= '_') && not (isDigit c) =
      fmtLocPunc cs (c : (T.unpack (T.reverse locColour) <> s))
fmtLocTyp (c : cs) s = fmtLocTyp cs (c : s)

fmtLocPunc :: [Char] -> String -> String
fmtLocPunc [] s = T.unpack (T.reverse reset) <> s
fmtLocPunc (c : cs) s | isAsciiUpper c = fmtLocTyp cs (c : (T.unpack (T.reverse typeColour) <> s))
fmtLocPunc (c : cs) s | isAsciiLower c || c == '_' = fmtLocVal cs (c : s)
fmtLocPunc (c : cs) s = fmtLocPunc cs (c : s)

fmtLocVal :: [Char] -> String -> String
fmtLocVal [] s = T.unpack (T.reverse reset) <> s
fmtLocVal (c : cs) s
  | not (isAsciiLower c) && not (isAsciiUpper c) && (c /= '_') && not (isDigit c) =
      fmtLocPunc cs (c : s)
fmtLocVal (c : cs) s = fmtLocVal cs (c : s)

-- Highlights Type names
fmtLoc :: Text -> Text
fmtLoc l = T.reverse $ T.pack $ fmtLocPunc (T.unpack l) (T.unpack $ T.reverse locColour)
