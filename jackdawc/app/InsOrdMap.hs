-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module InsOrdMap where

import Data.HashSet qualified as HS
import Data.List (find)
import Data.Maybe (fromMaybe)
import Prelude2

-- List is stored in reverse order
newtype InsOrdMap k v = InsOrdMap [(k, v)]
  deriving (Show, Eq, Generic)
  deriving newtype (Default)
  deriving anyclass (Newtype)

instance Indexable (InsOrdMap k v) where
  type IndexableItemType (InsOrdMap k v) = v
  x !! y = must $ x !? y
  InsOrdMap m !? i = snd <$> (m !? (length m - i - 1))

instance Functor (InsOrdMap k) where
  fmap f (InsOrdMap xs) = InsOrdMap $ xs <&> second f

instance Foldable (InsOrdMap k) where
  foldr f x (InsOrdMap xs) = foldr f x $ reverse $ snd <$> xs

instance Traversable (InsOrdMap k) where
  traverse :: (Applicative f) => (a -> f b) -> InsOrdMap k a -> f (InsOrdMap k b)
  traverse f (InsOrdMap xs) = traverse (snd >>> f) (reverse xs) <&> \u -> InsOrdMap $ zip (fst <$> xs) (reverse u)

instance HasLength (InsOrdMap k v) where
  length = un >>> length

-- Returns Nothing if the key was already present
tryInsert :: (Eq k) => k -> v -> InsOrdMap k v -> Maybe (InsOrdMap k v)
tryInsert key !val (InsOrdMap xs) =
  if key `elem` (fst <$> xs) then Nothing else Just $ InsOrdMap $ (key, val) : xs

insert :: (Eq k) => k -> v -> InsOrdMap k v -> InsOrdMap k v
insert key !val m = tryInsert key val m & fromMaybe m

instance ToList (InsOrdMap k v) where
  type ToListItemType (InsOrdMap k v) = (k, v)
  toList (InsOrdMap xs) = reverse xs

keys :: InsOrdMap k v -> [k]
keys (InsOrdMap xs) = reverse $ fst <$> xs

keysSet :: (Hashable k) => InsOrdMap k v -> HS.HashSet k
keysSet (InsOrdMap xs) = HS.fromList $ fst <$> xs

elems :: InsOrdMap k v -> [v]
elems (InsOrdMap xs) = reverse $ snd <$> xs

empty :: InsOrdMap k v
empty = InsOrdMap []

singleton :: k -> v -> InsOrdMap k v
singleton key !val = InsOrdMap [(key, val)]

lookup :: (Eq k) => k -> InsOrdMap k v -> Maybe v
lookup key (InsOrdMap xs) = find (\(key', _) -> key' == key) xs <&> snd

lookupWithIndex :: (Eq k) => k -> InsOrdMap k v -> Maybe (v, Int)
lookupWithIndex key (InsOrdMap m) = findWithIndex (\(key', _) -> key' == key) m <&> first snd . second (\i -> length m - i - 1)

-- Returns nothing if there are duplicate keys
fromList :: (Eq k, Hashable k) => [(k, v)] -> Maybe (InsOrdMap k v)
fromList xs =
  let ks = fst <$> xs
   in if HS.size (HS.fromList ks) == length ks
        then
          Just $ InsOrdMap $ reverse xs
        else Nothing

uncheckedFromList :: (Eq k) => [(k, v)] -> InsOrdMap k v
uncheckedFromList x = InsOrdMap $ reverse x
