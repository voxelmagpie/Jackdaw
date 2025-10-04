-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use head" #-}

module Tc.Casts where

import Control.Monad (unless)
import Hir qualified
import Prelude2
import Primitives
import SrcLoc (SrcRange)
import Tc.Ctx
import Tc.State (MonadHirRead', MonadTc)
import Tc.TcErr
import Tc.TcIr qualified as I

iCastNeeded :: (MonadHirRead' m) => I.Type -> I.Type -> m Bool
iCastNeeded fromType toType = case (fromType, toType) of
  (I.AFnType x, I.AFnType y) | x.params == y.params && x.ret == y.ret && not x.isNullable && y.isNullable -> pure True
  (I.PtrType (Just _), I.PtrType Nothing) -> pure True
  (I.AFnType _, I.PtrType Nothing) -> pure True
  (I.AnAccessorType _, I.PtrType Nothing) -> pure True
  (I.AnIteratorType _, I.PtrType Nothing) -> pure True
  (I.AnAccessorIteratorType _, I.PtrType Nothing) -> pure True
  (I.NumPrimType from, I.NumPrimType to) ->
    pure
      $ (to == f64t && from `elem` [i8t, u8t, i16t, u16t, i32t, u32t, f32t])
      || (to == f32t && from `elem` [i8t, u8t, i16t, u16t])
      || (to == i16t && from `elem` [i8t, u8t])
      || (to == i32t && from `elem` [i8t, u8t, i16t, u16t])
      || (to == i64t && from `elem` [i8t, u8t, i16t, u16t, i32t, u32t])
      || (to == u16t && from == u8t)
      || (to == u32t && from `elem` [u8t, u16t])
      || (to == u64t && from `elem` [u8t, u16t, u32t])
  _ -> pure False

iCast :: (MonadHirRead' m) => I.Type -> I.Expr -> m I.Expr
iCast toType (I.LoadConstantExpr c, fromType, sr) = do
  (c', t) <- iCastConstant toType (c, fromType)
  pure (I.LoadConstantExpr c', t, sr)
iCast toType expr@(_, fromType, sr) =
  iCastNeeded fromType toType
    <&> \case True -> (I.BitCast expr, toType, sr); False -> expr

iCastConstant :: (MonadHirRead' m) => I.Type -> I.Constant -> m I.Constant
iCastConstant toType@(I.NumPrimType (AFloatT to)) c@(I.ConstFloatOrDouble d, _) = do
  if to == F32T || to == F64T then pure (I.ConstFloatOrDouble d, toType) else pure c
--
iCastConstant toType@(I.NumPrimType to) c@(I.ConstInt i, _)
  | to == f32t && i >= -16777216 && i <= 16777216 = pure (I.ConstFloatOrDouble $ tShow i, toType)
  | to == f64t && i >= -9007199254740992 && i <= 9007199254740992 = pure (I.ConstFloatOrDouble $ tShow i, toType)
  | to == i8t && i >= -128 && i <= 127 = pure (I.ConstInt i, toType)
  | to == u8t && i >= 0 && i <= 255 = pure (I.ConstInt i, toType)
  | to == i16t && i >= -32768 && i <= 32767 = pure (I.ConstInt i, toType)
  | to == u16t && i >= 0 && i <= 65535 = pure (I.ConstInt i, toType)
  | to == i32t && i >= -2147483648 && i <= 2147483647 = pure (I.ConstInt i, toType)
  | to == u32t && i >= 0 && i <= 4294967295 = pure (I.ConstInt i, toType)
  | to == i64t && i >= -9223372036854775808 && i <= 9223372036854775807 = pure (I.ConstInt i, toType)
  | to == u64t && i >= 0 && i <= 18446744073709551615 = pure (I.ConstInt i, toType)
  | otherwise = pure c
--
iCastConstant toType@(I.NumPrimType to) (I.ConstSizeof t, _)
  | to == i64t =
      pure (I.ConstSizeof t, toType)
--
iCastConstant toType@(I.PtrType (Just elementType')) c@(I.ConstArray _ _, I.ArrayType elementType _) = do
  if elementType' == elementType
    then pure (I.ConstAddrOfArray0 c, toType)
    else
      pure c
iCastConstant toType@(I.PtrType (Just t)) c@(_, t') = do
  if t' == t
    then pure (I.ConstAddrOf c, toType)
    else
      pure c
iCastConstant toType@(I.AFnType x) (c, I.AFnType y)
  | x.params == y.params && x.ret == y.ret && x.isNullable && not y.isNullable =
      pure (c, toType)
iCastConstant _ c = pure c

bitCastIsValid :: (MonadTc m) => Ctx -> SrcRange -> I.Type -> I.Type -> m Bool
bitCastIsValid ctx sr from to = case (from, to) of
  (I.NumPrimType (AnIntT _), I.BoolType) -> pure True
  (I.NumPrimType _, I.NumPrimType _) -> pure True
  _ -> do
    let isIntOrPtr = \case
          I.PtrType _ -> True
          I.ConstPtrType _ -> True
          I.AFnType _ -> True
          I.AnAccessorType _ -> True
          I.AnIteratorType _ -> True
          I.AnAccessorIteratorType _ -> True
          I.NumPrimType (AnIntT _) -> True
          _ -> False
    if isIntOrPtr from && isIntOrPtr to
      then do
        unless ctx.inUnsafeCode $ addError ctx.et sr "Cast not valid in safe code"
        case to of
          I.NumPrimType (AnIntT x) | x.size /= Int64 -> pure False
          _ -> pure True
      else
        pure False
