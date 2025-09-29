-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module State where

import Data.IORef (modifyIORef')
import GHC.IORef (IORef)
import Prelude2
import Token (Token')

data State = State
  { -- Tracks all C declarations and the name that definition has been given in the Jackdaw code
    -- If a name is unchanged then it maps to itself
    nameMap :: HashTable Text Text,
    outputRev :: IORef [Text],
    nextAnonId :: IORef Int,
    -- Tracks forward declarations. States are:
    -- (no entry): no struct with this name has been seen
    -- False: struct has been forward declared
    -- True: struct definition has been seen (may or may not have been forward declared (doesn't matter))
    gotStructDef :: HashTable Text Bool,
    ppDefs :: HashTable Text [Token'],
    ppMacros :: HashTable Text ([Text], [Token']),
    ppDefsCache :: HashTable Text [Token']
  }

addLine :: State -> Text -> IO ()
addLine s x = modifyIORef' s.outputRev (x :)

-- TODO ReaderT monad
