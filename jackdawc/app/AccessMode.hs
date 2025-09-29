-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module AccessMode where

import Prelude2

data AccessMode = Shared | Exclusive | Move
  deriving (Show, Eq, Generic, Hashable)
