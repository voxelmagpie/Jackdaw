-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tables
  ( Table (..),
    tblEmpty,
    tblInsert,
    tblGet,
    tblGetMaybe,
    tblForEach,
    tblToList,
    tblFromList,
    tblReserveId,
    UniqueTable (..),
    uTblForEach,
    uTblEmpty,
    uTblGet,
    uTblGetByValue,
    uTblInsert,
    uTblInsert',
    uTblInsert'',
    uTblToList,
    uTblMember,
    tblReplace,
    tblMap,
    tblMapIO,
    IsValueNew (..),
    module IdTypes,
  )
where

import Control.Monad (forM_)
import Data.HashTable.IO qualified as HT
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.Maybe (isJust)
import GHC.Stack (HasCallStack)
import IdTypes (IntIdType (..))
import Prelude2

--
-- Map from ID to value with auto-incrementing ID
--

data Table id a = Table {m :: HashTable id a, nextId :: IORef id}

tblEmpty :: (Default id) => IO (Table id a)
tblEmpty = Table <$> HT.new <*> newIORef def

tblInsert :: (IntIdType id) => a -> Table id a -> IO id
tblInsert value tbl = do
  i <- readIORef tbl.nextId
  modifyIORef' tbl.nextId (idToInt >>> (+ 1) >>> idFromInt)
  HT.insert tbl.m i value
  pure i

-- For when using tblReserveId
tblGetMaybe :: (HasCallStack, IntIdType id) => id -> Table id a -> IO (Maybe a)
tblGetMaybe i tbl = HT.lookup tbl.m i

tblGet :: (HasCallStack, IntIdType id) => id -> Table id a -> IO a
tblGet i tbl = must <$> HT.lookup tbl.m i

tblForEach :: ((id, a) -> IO x) -> Table id a -> IO ()
tblForEach f tbl = HT.mapM_ f tbl.m

tblToList :: (Hashable id) => Table id a -> IO [(id, a)]
tblToList tbl = HT.toList tbl.m

tblFromList :: (IntIdType id) => [a] -> IO (Table id a, [id])
tblFromList xs = do
  m <- tblEmpty
  forM_ xs $ flip tblInsert m
  pure (m, [0 .. length xs - 1] <&> idFromInt)

tblReplace :: (IntIdType id) => id -> a -> Table id a -> IO ()
tblReplace id value tbl = HT.insert tbl.m id value

tblMap :: (IntIdType id) => id -> (a -> a) -> Table id a -> IO ()
tblMap id f tbl = do
  x <- HT.lookup tbl.m id <&> must
  HT.insert tbl.m id $ f x

tblMapIO :: (IntIdType id) => id -> (a -> IO a) -> Table id a -> IO ()
tblMapIO id f tbl = do
  x <- HT.lookup tbl.m id <&> must
  x' <- f x
  HT.insert tbl.m id x'

-- It is the caller's responsibility to ensure that a value is added for this ID
tblReserveId :: (IntIdType id) => Table id a -> IO id
tblReserveId tbl = do
  i <- readIORef tbl.nextId
  modifyIORef' tbl.nextId (idToInt >>> (+ 1) >>> idFromInt)
  pure i

--
-- Unique table (identical values have same ID)
--

data UniqueTable id a = UniqueTable {table :: Table id a, reverseTable :: HashTable a id}

uTblEmpty :: (Default id) => IO (UniqueTable id a)
uTblEmpty = UniqueTable <$> tblEmpty <*> HT.new

uTblGet :: (IntIdType id) => id -> UniqueTable id a -> IO a
uTblGet i tbl = tblGet i tbl.table

uTblGetByValue :: (Hashable a) => a -> UniqueTable id a -> IO (Maybe id)
uTblGetByValue x tbl = HT.lookup tbl.reverseTable x

data IsValueNew = NewValue | AlreadyAdded
  deriving (Show, Eq)

uTblInsert'' :: (IntIdType id, Hashable v) => v -> UniqueTable id v -> IO (id, v, IsValueNew)
uTblInsert'' value bi = do
  x <- HT.lookup bi.reverseTable value
  case x of
    (Just id) -> do
      x' <- tblGet id bi.table
      pure (id, x', AlreadyAdded)
    _ -> do
      id <- tblInsert value bi.table
      HT.insert bi.reverseTable value id
      pure (id, value, NewValue)

-- Returns the copy of the value that was already in the table.
-- This is so the value that was passed in can be garbage collected.
uTblInsert' :: (IntIdType id, Hashable v) => v -> UniqueTable id v -> IO (id, v)
uTblInsert' value bi = fst2Of3 <$> uTblInsert'' value bi

uTblInsert :: (IntIdType id, Hashable v) => v -> UniqueTable id v -> IO id
uTblInsert value bi = fst3 <$> uTblInsert'' value bi

uTblToList :: (Hashable id) => UniqueTable id a -> IO [(id, a)]
uTblToList tbl = HT.toList tbl.table.m

uTblMember :: (IntIdType id, Hashable v) => v -> UniqueTable id v -> IO Bool
uTblMember x tbl = HT.lookup tbl.reverseTable x <&> isJust

uTblForEach :: ((id, a) -> IO x) -> UniqueTable id a -> IO ()
uTblForEach f tbl = tblForEach f tbl.table
