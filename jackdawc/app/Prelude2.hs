-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-orphans #-}

module Prelude2
  ( module Prelude2,
    module Prelude,
    (>>>),
    (<<<),
    (&),
    (<&>),
    Text,
    assert,
    Hashable,
    HashMap,
    HashSet,
    Generic,
    Generic1,
    Newtype,
    Default (..),
    throwError,
    first,
    second,
    foldl',
  )
where

import Control.Arrow ((<<<), (>>>))
import Control.Exception (assert)
import Control.Monad.Except (MonadError (throwError))
import Control.Newtype.Generics (Newtype (..))
import Data.Bifunctor (Bifunctor (first, second))
import Data.ByteString qualified as BS
import Data.Default (Default (..))
import Data.Foldable (foldl')
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.HashTable.IO qualified as HT
import Data.Hashable (Hashable (..))
import Data.Kind (Type)
import Data.List (findIndex)
import Data.Maybe (fromJust)
import Data.Text (Text)
import Data.Text qualified as T
import Debug.Trace qualified as TR
import GHC.Generics (Generic, Generic1)
import GHC.Stack (HasCallStack)
import Prelude hiding (cycle, filter, foldl, foldl1, foldr1, head, id, init, last, length, map, maximum, minimum, tail, (!!))
import Prelude qualified as P

type HashTable k v = HT.BasicHashTable k v

-- type HashSet k = HT.BasicHashTable k ()

-- TODO implement these type classes for any type that is ListLike
class HasLength a where
  length :: a -> Int

instance HasLength [a] where
  length = P.length

instance HasLength Text where
  length = T.length

instance HasLength BS.ByteString where
  length = BS.length

instance HasLength (List1 a) where
  length (List1 _ xs) = length xs + 1

instance HasLength (List2 a) where
  length (List2 _ _ xs) = length xs + 2

class Filterable a where
  type FilterValue a :: Type
  filter :: (FilterValue a -> Bool) -> a -> a

instance Filterable [a] where
  type FilterValue [a] = a
  filter = P.filter

instance Filterable (HashMap k v) where
  type FilterValue (HashMap k v) = v
  filter = HM.filter

instance Filterable (HashSet a) where
  type FilterValue (HashSet a) = a
  filter = HS.filter

un :: (Newtype n) => n -> O n
un = unpack

class Must a where
  type MustValue a :: Type
  must :: (HasCallStack) => a -> MustValue a
  must' :: (HasCallStack, Show b) => b -> a -> MustValue a

instance Must (Maybe a) where
  type MustValue (Maybe a) = a
  must = fromJust
  must' msg x = case x of
    Just y -> y
    _ -> error $ show msg

instance Must (Either e a) where
  type MustValue (Either e a) = a
  must (Right x) = x
  must _ = error "Left"
  must' msg = \case
    Right x -> x
    _ -> error $ show msg

class ToList l where
  type ToListItemType l :: Type
  toList :: l -> [ToListItemType l]

instance ToList [a] where
  type ToListItemType [a] = a
  toList x = x

instance ToList (HashMap k v) where
  type ToListItemType (HashMap k v) = (k, v)
  toList = HM.toList

instance ToList (HashSet a) where
  type ToListItemType (HashSet a) = a
  toList = HS.toList

class Indexable l where
  type IndexableItemType l :: Type
  (!!) :: (HasCallStack) => l -> Int -> IndexableItemType l
  (!?) :: l -> Int -> Maybe (IndexableItemType l)

instance Indexable [a] where
  type IndexableItemType [a] = a
  (!!) = (P.!!)
  xs !? i = if i < 0 || i >= length xs then Nothing else Just $ xs !! i

instance Indexable (List1 a) where
  type IndexableItemType (List1 a) = a
  List1 x _ !! 0 = x
  List1 _ ys !! i = ys !! (i - 1)
  List1 x _ !? 0 = Just x
  List1 _ ys !? i = ys !? (i - 1)

instance Indexable (List2 a) where
  type IndexableItemType (List2 a) = a
  List2 x _ _ !! 0 = x
  List2 _ y _ !! 1 = y
  List2 _ _ zs !! i = zs !! (i - 2)
  List2 x _ _ !? 0 = Just x
  List2 _ y _ !? 1 = Just y
  List2 _ _ zs !? i = zs !? (i - 2)

{-# WARNING todo "'todo' left in code" #-}
todo :: (HasCallStack) => a
todo = undefined

instance Default Text where def = ""

instance Default (HashMap k v) where def = HM.empty

instance Default (HashSet a) where def = HS.empty

head :: [a] -> Maybe a
head (x : _) = Just x
head _ = Nothing

last :: [a] -> Maybe a
last [] = Nothing
last x = Just $ P.last x

tail :: [a] -> [a]
tail [] = []
tail (_ : xs) = xs

{-# WARNING traceIO "traceIO used here" #-}
traceIO :: String -> IO ()
traceIO = TR.traceIO

{-# WARNING traceM "traceM used here" #-}
traceM :: (Monad m) => String -> m ()
traceM = TR.traceM

{-# WARNING trace "trace used here" #-}
trace :: String -> a -> a
trace = TR.trace

{-# WARNING traceShow "traceShow used here" #-}
traceShow :: (Show t) => t -> a -> a
traceShow = show >>> TR.trace

{-# WARNING traceShowM "traceShowM used here" #-}
traceShowM :: (Show t, Monad m) => t -> m ()
traceShowM = show >>> TR.traceM

identity :: a -> a
identity x = x

notNull :: [a] -> Bool
notNull = not . null

with :: (MonadError e m) => Maybe a -> e -> m a
with (Just x) _ = pure x
with _ err = throwError err

dropLast :: Int -> [a] -> [a]
dropLast i xs = take (length xs - i) xs

data OneOrBoth a b = Fst a | Snd b | Both a b
  deriving (Show, Eq, Generic)

getFst :: OneOrBoth a b -> Maybe a
getFst (Fst x) = Just x
getFst (Both x _) = Just x
getFst _ = Nothing

getSnd :: OneOrBoth a b -> Maybe b
getSnd (Snd x) = Just x
getSnd (Both _ x) = Just x
getSnd _ = Nothing

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x

thd3 :: (a, b, c) -> c
thd3 (_, _, x) = x

fst2Of3 :: (a, b, c) -> (a, b)
fst2Of3 (x, y, _) = (x, y)

lst2Of3 :: (a, b, c) -> (b, c)
lst2Of3 (_, y, z) = (y, z)

outerOf3 :: (a, b, c) -> (a, c)
outerOf3 (x, _, z) = (x, z)

-- Prepends the Just value to the list
consMaybe :: Maybe a -> [a] -> [a]
consMaybe (Just x) xs = x : xs
consMaybe _ xs = xs

assertM :: (HasCallStack) => (Monad m) => Bool -> m ()
assertM b = assert b $ pure ()

tShow :: (Show a) => a -> Text
tShow = show >>> T.pack

findWithIndex :: (a -> Bool) -> [a] -> Maybe (a, Int)
findWithIndex f xs = findIndex f xs <&> \i -> (xs !! i, i)

--

data List1 a = List1 a [a]
  deriving (Show, Eq, Functor, Generic, Hashable, Foldable, Traversable)

instance ToList (List1 a) where
  type ToListItemType (List1 a) = a
  toList (List1 x ys) = x : ys

instance Semigroup (List1 a) where
  (List1 x xs) <> (List1 y ys') = List1 x $ xs <> (y : ys')

data List2 a = List2 a a [a]
  deriving (Show, Eq, Functor, Generic, Hashable, Foldable, Traversable)

instance ToList (List2 a) where
  type ToListItemType (List2 a) = a
  toList (List2 x y zs) = x : y : zs

instance Semigroup (List2 a) where
  (List2 x x' xs) <> (List2 y y' ys') = List2 x x' $ xs <> (y : y' : ys')

list2ToList1 :: List2 a -> List1 a
list2ToList1 (List2 x y zs) = List1 x $ y : zs

zipList2 :: List2 a -> List2 b -> List2 (a, b)
zipList2 (List2 x y zs) (List2 x' y' zs') = List2 (x, x') (y, y') $ zip zs zs'

listToList1 :: [a] -> Maybe (List1 a)
listToList1 [] = Nothing
listToList1 (x : xs) = Just $ List1 x xs

listToList2 :: [a] -> Maybe (List2 a)
listToList2 [] = Nothing
listToList2 [_] = Nothing
listToList2 (x : y : zs) = Just $ List2 x y zs

list1Head :: List1 a -> a
list1Head (List1 x _) = x

list2Head :: List2 a -> a
list2Head (List2 x _ _) = x

newtype Indentation = Indentation Int
  deriving (Show, Eq, Generic)
  deriving anyclass (Newtype)
  deriving newtype (Default)

incInd :: Indentation -> Indentation
incInd (Indentation i) = Indentation $ i + 1

indTabs :: Indentation -> Text
indTabs i = T.replicate (un i) "\t"

getLeft :: Either a b -> Maybe a
getLeft (Left x) = Just x
getLeft (Right _) = Nothing

getRight :: Either a b -> Maybe b
getRight (Left _) = Nothing
getRight (Right x) = Just x

fromEithers :: [Either a b] -> Maybe [b]
fromEithers xs = reverse <$> foldl' f (Just []) xs
  where
    f acc z = case (z, acc) of
      (_, Nothing) -> Nothing
      (Left _, _) -> Nothing
      (Right x, Just y) -> Just $ x : y

foldEithers :: [Either a b] -> Either a [b]
foldEithers xs = reverse <$> foldl' f (Right []) xs
  where
    f acc z = case (z, acc) of
      (_, e@(Left _)) -> e
      (Left e, _) -> Left e
      (Right x, Right ys) -> Right $ x : ys

toMaybe :: Bool -> a -> Maybe a
toMaybe c x = if c then Just x else Nothing

--
--

-- allM and andM copyright GHC
-- See: licences/ghc.txt
-- https://hackage.haskell.org/package/ghc-9.12.1/docs/src/GHC.Utils.Monad.html#allM
-- https://hackage.haskell.org/package/ghc-9.12.1/docs/src/GHC.Utils.Monad.html#andM
allM :: (Monad m, Foldable f) => (a -> m Bool) -> f a -> m Bool
allM f = foldr (andM . f) (pure True)

andM :: (Monad m) => m Bool -> m Bool -> m Bool
andM m1 m2 = m1 >>= \x -> if x then m2 else pure False

--
--

-- https://hackage.haskell.org/package/Agda-2.7.0.1/docs/src/Agda.Utils.List.html#updateAt
-- Copyright Agda 2 authors&contributors, MIT Licence
-- See: licences/agda2.txt

-- | Update nth element of a list, if it exists.
--   @O(min index n)@.
--
--   Precondition: the index is >= 0.
updateAt :: Int -> (a -> a) -> [a] -> [a]
updateAt _ _ [] = []
updateAt 0 f (a : as) = f a : as
updateAt n f (a : as) = a : updateAt (n - 1) f as
