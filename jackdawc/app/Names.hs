-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Names where

import Prelude2
import SrcLoc (SrcRange)

-- E.g. "", "stlib/json", etc.
newtype Namespace = Namespace Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

data ImportNames = AllNames | VisibleNames [Text] | HiddenNames [Text]
  deriving (Show, Generic, Eq)

-- a, _f9, etc.
newtype VName = VName Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

type VName' = (VName, SrcRange)

-- +, !, etc.
newtype OpName = OpName Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

type OpName' = (OpName, SrcRange)

-- X, Y_9, etc.
newtype TName = TName Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

type TName' = (TName, SrcRange)

-- A.a, etc.
newtype VFqn = VFqn Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

-- A.B, xyz/abc:A.B, etc.
newtype TFqn = TFqn Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

newtype Attribute = Attribute Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)