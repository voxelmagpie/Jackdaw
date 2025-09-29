-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.Builtins where

import Primitives
import Tc.TcIr qualified as I

f32 :: I.Type
f32 = I.NumPrimType f32t

f64 :: I.Type
f64 = I.NumPrimType f64t

i8 :: I.Type
i8 = I.NumPrimType i8t

u8 :: I.Type
u8 = I.NumPrimType u8t

i16 :: I.Type
i16 = I.NumPrimType i16t

u16 :: I.Type
u16 = I.NumPrimType u16t

i32 :: I.Type
i32 = I.NumPrimType i32t

u32 :: I.Type
u32 = I.NumPrimType u32t

i64 :: I.Type
i64 = I.NumPrimType i64t

u64 :: I.Type
u64 = I.NumPrimType u64t

bool :: I.Type
bool = I.BoolType
