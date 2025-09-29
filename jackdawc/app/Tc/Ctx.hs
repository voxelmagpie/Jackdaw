-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.Ctx where

import Ast qualified as A
import Data.Foldable (find)
import Names
import Prelude2
import SrcLoc (SrcLoc')
import Tc.TcIr qualified as I

data TcInputs = TcInputs
  { allAsts :: HashMap Namespace (A.Ast, [(Namespace, ImportNames)]),
    primitivesAst :: (A.Ast, [(Namespace, ImportNames)]),
    stLibAst :: (A.Ast, [(Namespace, ImportNames)]),
    hashAst :: (A.Ast, [(Namespace, ImportNames)]),
    toStringAst :: (A.Ast, [(Namespace, ImportNames)]),
    dropFn :: A.AnyVDef,
    equalFn :: A.AnyVDef,
    notEqualFn :: A.AnyVDef,
    cloneFn :: A.AnyVDef,
    hashFn :: A.AnyVDef,
    addToHashFn :: A.AnyVDef,
    toStringFn :: A.AnyVDef,
    uncheckedArithmetic :: Bool
  }
  deriving (Show)

data Ctx = Ctx
  { namespace :: Namespace,
    thisAst :: A.Ast,
    thisAstImports :: [(Namespace, ImportNames)],
    tcIn :: TcInputs,
    selfType :: Maybe (TFqn, I.Type),
    tNameToGp :: HashMap TName I.Type,
    vNameToGp :: HashMap VName I.Constant,
    genericParams :: [I.GenericArg],
    variables :: [Variable],
    returnType :: Maybe I.Type,
    inIterator :: Bool,
    inAccessor :: Bool,
    inLoop :: Bool,
    inUnsafeCode :: Bool,
    et :: [(Text, SrcLoc')] -- Error trace
  }
  deriving (Show)

mkFileCtx :: Namespace -> (A.Ast, [(Namespace, ImportNames)]) -> TcInputs -> Ctx
mkFileCtx namespace (thisAst, thisAstImports) tcIn =
  Ctx
    { namespace = namespace,
      thisAst = thisAst,
      thisAstImports = thisAstImports,
      tcIn = tcIn,
      selfType = def,
      tNameToGp = def,
      vNameToGp = def,
      genericParams = def,
      variables = def,
      returnType = def,
      inIterator = False,
      inAccessor = False,
      inLoop = False,
      inUnsafeCode = True, -- Disables unsafe errors when checking definitions
      et = []
    }

mkFileCtx' :: Ctx -> Ctx
mkFileCtx' c = mkFileCtx c.namespace (c.thisAst, c.thisAstImports) c.tcIn

data Variable = Variable
  { name :: VName',
    uidOrVal :: Either I.LocalVarUid I.Constant',
    typ :: I.Type
  }
  deriving (Show, Eq)

findLocalVarByName :: Ctx -> VName -> Maybe Variable
findLocalVarByName ctx name =
  find ((.name) >>> fst >>> (== name)) ctx.variables
