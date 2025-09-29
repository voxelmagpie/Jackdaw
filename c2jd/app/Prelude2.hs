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
    Generic,
    Generic1,
    fromList,
    first,
    second,
    foldl',
    foldM,
    traceIO,
    traceM,
    trace,
    traceShow,
    traceShowM,
  )
where

import Control.Arrow ((<<<), (>>>))
import Control.Exception (assert)
import Control.Monad (foldM)
import Data.Bifunctor (Bifunctor (first, second))
import Data.Foldable (foldl')
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.HashTable.IO qualified as HT
import Data.Hashable (Hashable (..))
import Data.Text (Text)
import Data.Text qualified as T
import Debug.Trace
import GHC.Generics (Generic, Generic1)
import GHC.IsList (IsList (fromList))
import GHC.Stack (HasCallStack)
import Prelude hiding (cycle, filter, foldl, foldl1, foldr1, id, init, last, length, map, maximum, minimum, tail, (!!))

type HashTable k v = HT.BasicHashTable k v

-- type HashSet k = HT.BasicHashTable k ()

{-# WARNING todo "'todo' left in code" #-}
todo :: (HasCallStack) => a
todo = undefined

tail :: [a] -> [a]
tail [] = []
tail (_ : xs) = xs

removeElemAt :: Int -> [a] -> [a]
removeElemAt i xs = splitAt i xs & \(a, b) -> a ++ tail b

tShow :: (Show a) => a -> Text
tShow = show >>> T.pack
