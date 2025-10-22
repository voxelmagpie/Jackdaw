-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.MkCtx where

import Ast qualified as A
import Control.Monad (forM, forM_, when)
import Data.HashMap.Strict qualified as HM
import Data.Maybe (mapMaybe)
import Data.Text qualified as T
import Names
import Prelude2
import Primitives (numPrimTypeToText)
import SrcLoc (SrcRange)
import Tc.Builtins
import Tc.Ctx
import Tc.Error (MonadTcError)
import Tc.Fmt
import Tc.State
import Tc.TcErr (throw)
import Tc.TcIr qualified as I

-- If this is a member function then the context includes generic parameters from containing type as well as the function
-- 'userCtx' is the context of the code that is accessing this definition
-- 'outerCtx' is the context of the source file or type that the definition is within
makeVDefCtx ::
  (MonadHirRead' m, MonadTcError m) =>
  Ctx ->
  Ctx ->
  [I.GenericArg] ->
  [A.GenericParameter] ->
  Bool ->
  Bool ->
  VName ->
  Bool ->
  SrcRange ->
  m Ctx
makeVDefCtx userCtx outerCtx genericArgs astGp isIterator isAccessor name isUnsafe sr = do
  when (userCtx.depth > 300) $ throw userCtx.et sr "Definition depth limit reached"
  let gp = zip astGp genericArgs
  let newTypeParams =
        mapMaybe (\case (A.TypeGenericParameter n, I.TypeGenericArg t) -> Just (fst n, t); _ -> Nothing) gp
  let newValParams =
        mapMaybe (\case (A.ValueGenericParameter n, I.ValueGenericArg v) -> Just (fst n, v); _ -> Nothing) gp
  gArgsText <- forM genericArgs $ formatGenArg False
  let loc' = if null genericArgs then un name else un name <> "[" <> T.intercalate "," gArgsText <> "]"
  let loc = if T.null outerCtx.et.location then loc' else outerCtx.et.location <> "." <> loc'
  pure
    $ outerCtx
      { genericParams = outerCtx.genericParams <> genericArgs,
        tNameToGp = HM.fromList $ HM.toList outerCtx.tNameToGp <> newTypeParams,
        vNameToGp = HM.fromList $ HM.toList outerCtx.vNameToGp <> newValParams,
        inIterator = isIterator,
        inAccessor = isAccessor,
        inUnsafeCode = isUnsafe,
        et = ErrorTrace loc (if null genericArgs then [(userCtx.et.location, sr)] else (userCtx.et.location, sr) : userCtx.et.trace),
        depth = userCtx.depth + 1
      }

makeTSDefCtx ::
  (MonadHirRead' m, MonadTcError m) =>
  Ctx ->
  Ctx ->
  TFqn ->
  [A.GenericParameter] ->
  [I.GenericArg] ->
  Maybe I.Type ->
  TName ->
  Bool ->
  SrcRange ->
  m Ctx
makeTSDefCtx userCtx outerCtx fqn astGp genericArgs typ name isUnsafe sr = do
  when (userCtx.depth > 300) $ throw userCtx.et sr "Definition depth limit reached"
  let gp = zip astGp genericArgs
  let newTypeParams =
        mapMaybe (\case (A.TypeGenericParameter n, I.TypeGenericArg t) -> Just (fst n, t); _ -> Nothing) gp
  let newValParams =
        mapMaybe (\case (A.ValueGenericParameter n, I.ValueGenericArg v) -> Just (fst n, v); _ -> Nothing) gp
  gArgsText <- forM genericArgs $ formatGenArg False
  let loc' = if null genericArgs then un name else un name <> "[" <> T.intercalate "," gArgsText <> "]"
  let loc = if T.null outerCtx.et.location then loc' else outerCtx.et.location <> "." <> loc'
  pure
    $ Ctx
      { namespace = outerCtx.namespace,
        thisAst = outerCtx.thisAst,
        thisAstImports = outerCtx.thisAstImports,
        tcIn = outerCtx.tcIn,
        selfType = typ <&> (fqn,),
        tNameToGp = HM.fromList newTypeParams,
        vNameToGp = HM.fromList newValParams,
        genericParams = genericArgs,
        variables = [],
        returnType = Nothing,
        inIterator = False,
        inAccessor = False,
        inLoop = False,
        inUnsafeCode = isUnsafe,
        et = ErrorTrace loc (if null genericArgs then [(userCtx.et.location, sr)] else (userCtx.et.location, sr) : userCtx.et.trace),
        depth = userCtx.depth + 1
      }

-- If this type has a type definition in code (Xyz, Array, Slice, etc.) then this function gets the relevant context
getTypeCtx :: (MonadTc m) => Ctx -> SrcRange -> I.Type -> m (Maybe Ctx)
getTypeCtx ctx sr t = do
  getCachedTypeCtx t >>= \case
    Just x -> pure $ Just x
    _ -> do
      let outerCtx = mkFileCtx (Namespace "@stlib/primitives") ctx.tcIn.primitivesAst ctx.tcIn
      ctx' <- case t of
        I.ArrayType el n ->
          let c = (fst ctx.tcIn.primitivesAst).tsDefs & HM.lookup (TName "Array") & must & A.getTDefCommonMaybe & must
              astGp = c.c.genericParams
              gArgs = [I.TypeGenericArg el, I.ValueGenericArg (I.ConstInt $ fromIntegral n, i32)]
           in Just <$> makeTSDefCtx ctx outerCtx (TFqn "@stlib/primitives:Array") astGp gArgs (Just t) (TName "Array") False sr
        I.SliceType el ->
          let c = (fst ctx.tcIn.primitivesAst).tsDefs & HM.lookup (TName "Slice") & must & A.getTDefCommonMaybe & must
              astGp = c.c.genericParams
              gArgs = [I.TypeGenericArg el]
           in Just <$> makeTSDefCtx ctx outerCtx (TFqn "@stlib/primitives:Slice") astGp gArgs (Just t) (TName "Slice") False sr
        I.NumPrimType p ->
          Just <$> makeTSDefCtx ctx outerCtx (TFqn $ "@stlib/primitives:" <> numPrimTypeToText p) [] [] (Just t) (TName $ numPrimTypeToText p) False sr
        I.BoolType ->
          Just <$> makeTSDefCtx ctx outerCtx (TFqn "@stlib/primitives:Bool") [] [] (Just t) (TName "Bool") False sr
        I.ANamedType _ ->
          -- Named type context was made when the type definition (1) was visited
          undefined
        _ -> pure Nothing
      forM_ ctx' $ addTypeCtx t
      pure ctx'
