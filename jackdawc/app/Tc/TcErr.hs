-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

-- Alternative versions of the error functions that take the error trace list
module Tc.TcErr (throw, addError) where

import Data.Text qualified as T
import Prelude2
import SrcLoc (HasSrcRange, SrcLoc (..), SrcLoc' (SrcLoc'))
import Tc.Error (MonadTcError)
import Tc.Error qualified as E

throw :: (MonadTcError m, HasSrcRange r) => [(Text, SrcLoc')] -> r -> Text -> m a
throw et sr msg =
  E.throw E.TypeCheckerError sr
    $ T.intercalate "\n"
    $ msg
    -- If length et == 1 then the error is not in generic code and an error trace is not needed
    : if length et == 1 then [] else et <&> fmt

addError :: (MonadTcError m, HasSrcRange r) => [(Text, SrcLoc')] -> r -> Text -> m ()
addError et sr msg =
  E.addError E.TypeCheckerError sr
    $ T.intercalate "\n"
    $ msg
    : if length et == 1 then [] else et <&> fmt

fmt :: (Text, SrcLoc') -> Text
fmt (wh, SrcLoc' fp l) = "> In " <> wh <> " at " <> T.pack fp <> ":" <> tShow l.line