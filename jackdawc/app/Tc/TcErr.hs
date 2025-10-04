-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

-- Alternative versions of the error functions that take the error trace list
module Tc.TcErr (throw, addError) where

import Prelude2
import SrcLoc (HasSrcRange, SrcLoc')
import Tc.Error (MonadTcError)
import Tc.Error qualified as E

throw :: (MonadTcError m, HasSrcRange r) => [(Text, SrcLoc')] -> r -> Text -> m a
throw =
  E.throw E.TypeCheckerError

addError :: (MonadTcError m, HasSrcRange r) => [(Text, SrcLoc')] -> r -> Text -> m ()
addError =
  E.addError E.TypeCheckerError
