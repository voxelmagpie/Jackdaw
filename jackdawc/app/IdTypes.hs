-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module IdTypes (IdType (..), IntIdType (..), TextIdType (..), IntId (..), TextId (..)) where

import Prelude2

class (Hashable a, Eq a, Default a) => IdType a where
  idToText :: a -> Text

class (IdType a) => IntIdType a where
  idFromInt :: Int -> a
  idToInt :: a -> Int

class (IdType a) => TextIdType a where
  idFromText :: Text -> a

newtype IntId = IntId Int
  deriving (Generic)
  deriving newtype (Show, Eq, Hashable, Default)
  deriving anyclass (Newtype)

instance IntIdType IntId where
  idFromInt = IntId
  idToInt (IntId i) = i

instance IdType IntId where
  idToText (IntId t) = tShow t

newtype TextId = TextId Text
  deriving (Generic)
  deriving newtype (Show, Eq, Hashable, Default)
  deriving anyclass (Newtype)

instance TextIdType TextId where
  idFromText = TextId

instance IdType TextId where
  idToText (TextId t) = t
