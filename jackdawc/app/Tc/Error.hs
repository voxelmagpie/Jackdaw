-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.Error where

import Control.Exception (Exception)
import Control.Monad (when)
import Data.Text qualified as T
import Prelude2
import SrcLoc

data Err = Err ErrorOrigin SrcRange Text
  deriving (Show, Generic)

data ErrorOrigin = TypeCheckerError | BorrowCheckerError
  deriving (Show, Generic, Eq)

newtype TcException = TcException [Err]
  deriving (Show, Generic)
  deriving anyclass (Newtype, Exception)

class (Monad m) => MonadTcError m where
  getErrsListRev :: m [Err]
  consErr :: Err -> m ()
  throwTcException :: TcException -> m a

  throw :: (HasSrcRange r) => ErrorOrigin -> [(Text, SrcLoc')] -> r -> Text -> m a
  throw o et sr msg = do
    addError o et sr msg
    e <- getErrsListRev
    throwTcException $ TcException $ reverse e

  addError :: (HasSrcRange r) => ErrorOrigin -> [(Text, SrcLoc')] -> r -> Text -> m ()
  addError o et sr msg' = do
    let msg =
          T.intercalate "\n"
            $ msg'
            : ("At " <> T.pack (filePath sr) <> ":" <> tShow (startLoc sr).line)
            : (et <&> \(wh, SrcLoc' fp l) -> "In " <> wh <> " at " <> T.pack fp <> ":" <> tShow l.line)
    consErr $ Err o (srcRangeOf sr sr) msg

    e <- getErrsListRev
    when (length e > 100) $ throwTcException $ TcException $ reverse e

  checkErrs :: m ()
  checkErrs = do
    es <- getErrsListRev
    when (notNull es) $ throwTcException $ TcException $ reverse es
