-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.Error where

import Control.Exception (Exception)
import Control.Monad (when)
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

  throw :: (HasSrcRange r) => ErrorOrigin -> r -> Text -> m a
  throw o sr msg = do
    addError o sr msg
    e <- getErrsListRev
    throwTcException $ TcException $ reverse e

  throw' :: ErrorOrigin -> Text -> m a
  throw' o = throw o (def :: SrcRange)

  addError :: (HasSrcRange r) => ErrorOrigin -> r -> Text -> m ()
  addError o sr msg = do
    consErr $ Err o (srcRangeOf sr sr) msg

    e <- getErrsListRev
    when (length e > 100) $ throwTcException $ TcException $ reverse e

  checkErrs :: m ()
  checkErrs = do
    es <- getErrsListRev
    when (notNull es) $ throwTcException $ TcException $ reverse es
