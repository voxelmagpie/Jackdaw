-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.Ctx where

import Ast qualified as A
import Data.Foldable (find)
import Names
import Prelude2
import SrcLoc (SrcRange)
import Tc.TcIr qualified as I

data TypeHint = NoHint | TypeHint I.Type | FnReturningHint TypeHint
  deriving (Show, Eq)

type ImportsList = [(Namespace, Maybe TName, ImportNames)]

data TcInputs = TcInputs
  { allAsts :: HashMap Namespace (A.Ast, ImportsList),
    primitivesAst :: (A.Ast, ImportsList),
    stLibAst :: (A.Ast, ImportsList),
    hashAst :: (A.Ast, ImportsList),
    toStringAst :: (A.Ast, ImportsList),
    dropFn :: A.AnyVDef,
    equalFn :: A.AnyVDef,
    notEqualFn :: A.AnyVDef,
    cloneFn :: A.AnyVDef,
    hashFn :: A.AnyVDef,
    addToHashFn :: A.AnyVDef,
    toStringFn :: A.AnyVDef,
    addToStringFn :: A.AnyVDef,
    uncheckedArithmetic :: Bool
  }
  deriving (Show)

data ErrorTrace = ErrorTrace {location :: Text, trace :: [(Text, SrcRange)]}
  deriving (Show, Generic, Default)

data Ctx = Ctx
  { namespace :: Namespace,
    thisAst :: A.Ast,
    thisAstImports :: ImportsList,
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
    et :: ErrorTrace,
    depth :: Int -- For preventing infinite loops in generic definitions
  }
  deriving (Show)

mkFileCtx :: Namespace -> (A.Ast, ImportsList) -> TcInputs -> Ctx
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
      et = ErrorTrace "" [],
      depth = 0
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
