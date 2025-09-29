-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module HashMultiMap where

import Data.HashMap.Strict qualified as HM
import Prelude2

newtype HashMultiMap k v = HashMultiMap (HM.HashMap k (List1 v))
  deriving (Show, Generic, Eq)
  deriving newtype (Default)

instance Functor (HashMultiMap k) where
  fmap f (HashMultiMap m) = HashMultiMap $ m <&> (<&> f)

empty :: HashMultiMap k v
empty = def

lookup :: (Eq k, Hashable k) => k -> HashMultiMap k v -> [v]
lookup key (HashMultiMap m) = maybe [] toList $ HM.lookup key m

insert :: (Eq k, Hashable k) => k -> v -> HashMultiMap k v -> HashMultiMap k v
insert key !value (HashMultiMap m) = HashMultiMap $ HM.insert key newList m
  where
    oldListMaybe = HM.lookup key m
    newList = case oldListMaybe of
      Nothing -> List1 value []
      (Just (List1 x ys)) -> List1 value (x : ys)

mapList1 :: (List1 v1 -> List1 v2) -> HashMultiMap k v1 -> HashMultiMap k v2
mapList1 f (HashMultiMap m) = HashMultiMap $ m <&> f

instance ToList (HashMultiMap k v) where
  type ToListItemType (HashMultiMap k v) = (k, v)
  toList (HashMultiMap m) = concatMap f $ toList m
    where
      f :: (k, List1 v) -> [(k, v)]
      f (key, list) = toList $ list <&> (key,)

toList1 :: HashMultiMap k v -> [(k, List1 v)]
toList1 (HashMultiMap m) = toList m

-- Index is per-key
toListIndexed :: HashMultiMap k v -> [(k, v, Int)]
toListIndexed (HashMultiMap m) = concatMap f $ toList m
  where
    f :: (k, List1 v) -> [(k, v, Int)]
    f (key, list) = zipWith (curry (\(i, (key', val)) -> (key', val, i))) [0 ..] (toList $ list <&> (key,))

fromList :: (Eq k, Hashable k) => [(k, v)] -> HashMultiMap k v
fromList = foldl' (\acc (key, val) -> insert key val acc) def
