-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Primitives where

import Prelude2

data IntSize = Int8 | Int16 | Int32 | Int64
  deriving (Show, Eq, Generic, Hashable)

intSizeToInt :: IntSize -> Int
intSizeToInt = \case
  Int8 -> 8
  Int16 -> 16
  Int32 -> 32
  Int64 -> 64

intSizeToText :: IntSize -> Text
intSizeToText = \case
  Int8 -> "8"
  Int16 -> "16"
  Int32 -> "32"
  Int64 -> "64"

data FloatT = F32T | F64T
  deriving (Show, Eq, Generic, Hashable)

data IntT = IntT {size :: IntSize, signed :: Signedness}
  deriving (Show, Eq, Generic, Hashable)

data Signedness = Signed | Unsigned
  deriving (Show, Eq, Generic, Hashable)

data NumPrim = AnIntT IntT | AFloatT FloatT
  deriving (Show, Eq, Generic, Hashable)

numPrimTypeToText :: NumPrim -> Text
numPrimTypeToText = \case
  AnIntT IntT {..} -> s <> i
    where
      s = case signed of Signed -> "I"; _ -> "U"
      i = intSizeToText size
  AFloatT F32T -> "F32"
  AFloatT F64T -> "F64"

f32t :: NumPrim
f32t = AFloatT F32T

f64t :: NumPrim
f64t = AFloatT F64T

i8t :: NumPrim
i8t = AnIntT (IntT Int8 Signed)

u8t :: NumPrim
u8t = AnIntT (IntT Int8 Unsigned)

i16t :: NumPrim
i16t = AnIntT (IntT Int16 Signed)

u16t :: NumPrim
u16t = AnIntT (IntT Int16 Unsigned)

i32t :: NumPrim
i32t = AnIntT (IntT Int32 Signed)

u32t :: NumPrim
u32t = AnIntT (IntT Int32 Unsigned)

i64t :: NumPrim
i64t = AnIntT (IntT Int64 Signed)

u64t :: NumPrim
u64t = AnIntT (IntT Int64 Unsigned)
