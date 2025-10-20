-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.Hir where

import Ast qualified as A
import Data.HashMap.Strict qualified as HM
import Data.Maybe (fromMaybe)
import Hir qualified
import Names
import Prelude2
import Primitives
import Tc.Ctx
import Tc.State
import Tc.TcIr qualified as I

getAstTDefCommonFromType :: (MonadHirRead' m) => TcInputs -> I.Type -> m (Maybe A.TypeDefCommon)
getAstTDefCommonFromType tcIn t = do
  y <- getAstTDefFromType tcIn t
  case y of
    Just (A.ATypeDef x) -> pure $ Just x.c
    Just (A.AStructDef x) -> pure $ Just x.c
    Just (A.AnEnumDef x) -> pure $ Just x.c
    _ -> pure Nothing

getAstTDefFromType :: (MonadHirRead' m) => TcInputs -> I.Type -> m (Maybe A.AnyTSDef)
getAstTDefFromType tcIn = \case
  I.ANamedType tDefId -> do
    d <- getTDef tDefId
    let hirTDefCommon = I.tDefCommon d
    let (ast, _) = must $ HM.lookup hirTDefCommon.namespace tcIn.allAsts
    pure $ HM.lookup hirTDefCommon.name ast.tsDefs
  I.ArrayType _ _ -> pure $ HM.lookup (TName "Array") (fst tcIn.primitivesAst).tsDefs
  I.SliceType _ -> pure $ HM.lookup (TName "Slice") (fst tcIn.primitivesAst).tsDefs
  I.NumPrimType x -> pure $ HM.lookup (TName $ numPrimTypeToText x) (fst tcIn.primitivesAst).tsDefs
  I.BoolType -> pure $ HM.lookup (TName "Bool") (fst tcIn.primitivesAst).tsDefs
  _ -> pure Nothing

fnIsNoThrow :: (MonadHirRead' m) => I.VDefId -> m Bool
fnIsNoThrow id = do
  d <- getVDef id
  x <- getFnDefBodyMaybe id <&> ((<&> snd) >>> fromMaybe False)
  pure $ x || Attribute "NoThrow" `elem` (Hir.vDefCommon d).attributes
