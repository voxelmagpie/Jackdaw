-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.Fmt where

import AccessMode
import Control.Monad (forM)
import Data.Maybe (fromMaybe)
import Data.Text qualified as T
import Hir qualified
import Prelude2
import Primitives
import Tc.State (MonadHirRead' (getTDef, getVDef))
import Tc.TcIr qualified as I

formatConstant :: (MonadHirRead' m) => I.Constant -> m Text
formatConstant = \case
  (I.ConstFloatOrDouble c, _) -> pure c
  (I.ConstBool c, _) -> pure $ if c then "true" else "false"
  (I.ConstInt c, _) -> pure $ tShow c
  (I.ConstNullPtr, _) -> pure "nullptr"
  (I.ConstStructOrTuple cs, t') -> do
    values <- forM cs formatConstant <&> \cs' -> T.intercalate ", " cs'
    case t' of
      I.TupleType _ ->
        pure $ "(" <> values <> ")"
      _ ->
        formatType False t' <&> \t'' -> t'' <> "{" <> values <> "}"
  (I.ConstArray t cs, _) -> forM (cs <&> (,t)) formatConstant <&> \cs' -> "{" <> T.intercalate ", " (toList cs') <> "}"
  (I.ConstSizeof t, _) -> formatType False t <&> \t'' -> "sizeOf[" <> t'' <> "]"
  (I.ConstFnPtr c, _) -> getVDef c <&> \d -> un $ fst (I.vDefCommon d).name
  (I.ConstExtern c, _) -> getVDef c <&> \d -> un $ fst (I.vDefCommon d).name
  (I.ConstAddrOf c, _) -> formatConstant c <&> ("&" <>)
  (I.ConstAddrOfArray0 c, _) -> formatConstant c <&> ("&" <>)

formatGenArg :: (MonadHirRead' m) => Bool -> I.GenericArg -> m Text
formatGenArg showFqn = \case
  I.TypeGenericArg x -> formatType showFqn x
  I.ValueGenericArg x -> formatConstant x

formatType :: (MonadHirRead' m) => Bool -> I.Type -> m Text
formatType showFqn = \case
  I.BoolType -> pure "Bool"
  I.NumPrimType x -> pure $ numPrimTypeToText x
  I.ANamedType id -> do
    d <- getTDef id
    let c = I.tDefCommon d
    args <- forM c.genericArgs $ formatGenArg showFqn
    let n = if showFqn then un c.fqn else un c.name
    pure $ if null args then n else T.concat [n, "[", T.intercalate ", " args, "]"]
  I.TupleType xs -> do
    xs' <- forM xs $ formatType showFqn
    pure $ T.concat ["(", T.intercalate ", " $ toList xs', ")"]
  I.AFnType x -> do
    r <- forM x.ret $ formatType showFqn
    p <- forM x.params $ \(mode, t) -> do
      let mode' = case mode of Shared -> ""; Exclusive -> "ref "; Move -> "var "
      formatType showFqn t <&> (mode' <>)
    pure $ T.concat [if x.isNullable then "?" else "", "fn (", T.intercalate ", " p, ")", maybe "" (" => " <>) r]
  I.AnAccessorType x -> do
    r <- formatType showFqn x.ret
    p <- forM (toList x.params) $ \(mode, t) -> do
      let mode' = case mode of Shared -> ""; Exclusive -> "ref "; Move -> "var "
      formatType showFqn t <&> (mode' <>)
    pure $ T.concat ["accessor (", T.intercalate ", " p, ") => ", r]
  I.AnIteratorType x -> do
    r <- formatType showFqn x.ret
    p <- forM x.params $ \(mode, t) -> do
      let mode' = case mode of Shared -> ""; Exclusive -> "ref "; Move -> "var "
      formatType showFqn t <&> (mode' <>)
    pure $ T.concat ["iterator (", T.intercalate ", " p, ")", r]
  I.AnAccessorIteratorType x -> do
    r <- formatType showFqn x.ret
    p <- forM (toList x.params) $ \(mode, t) -> do
      let mode' = case mode of Shared -> ""; Exclusive -> "ref "; Move -> "var "
      formatType showFqn t <&> (mode' <>)
    pure $ T.concat ["accessor iterator (", T.intercalate ", " p, ") => ", r]
  I.PtrType x -> case x of
    Just y -> ("*" <>) <$> formatType showFqn y
    _ -> pure "*void"
  I.ConstPtrType y -> ("*" <>) <$> formatType showFqn y
  I.ArrayType t n -> do
    t' <- formatType showFqn t
    pure $ "Array[" <> t' <> "," <> tShow n <> "]"
  I.SliceType t -> do
    t' <- formatType showFqn t
    pure $ "Slice[" <> t' <> "]"

format2Types :: (MonadHirRead' m) => I.Type -> I.Type -> m (Text, Text)
format2Types t0 t1 = do
  x0 <- formatType False t0
  x1 <- formatType False t1
  if x0 == x1
    then do
      y0 <- formatType True t0
      y1 <- formatType True t1
      pure (y0, y1)
    else
      pure (x0, x1)

format2MaybeTypes :: (MonadHirRead' m) => Text -> Maybe I.Type -> Maybe I.Type -> m (Text, Text)
format2MaybeTypes voidTypeText t0 t1 = case (t0, t1) of
  (Just t0', Just t1') -> format2Types t0' t1'
  _ -> do
    x0 <- forM t0 $ formatType False
    x1 <- forM t1 $ formatType False
    pure (fromMaybe voidTypeText x0, fromMaybe voidTypeText x1)
