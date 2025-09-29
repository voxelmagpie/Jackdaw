-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Ex where

import Control.Exception (Exception)
import Prelude2

newtype CompileException = CompileException Text
  deriving (Show, Eq, Generic)
  deriving anyclass (Exception, Newtype)