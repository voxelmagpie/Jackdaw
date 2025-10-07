-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Lir where

import Data.Foldable (Foldable (maximum))
import Data.Int (Int32)
import IdTypes
import Prelude2
import Primitives
import SrcLoc (SrcRange)

tShowNumPrim :: NumPrim -> Text
tShowNumPrim (AFloatT F32T) = "F32"
tShowNumPrim (AFloatT F64T) = "F64"
tShowNumPrim (AnIntT x) = s' <> t
  where
    t = case x.size of
      Int8 -> "8"
      Int16 -> "16"
      Int32 -> "32"
      Int64 -> "64"
    s' = case x.signed of
      Signed -> "I"
      Unsigned -> "U"

type IsRestrict = Bool

data Type
  = NumPrimType NumPrim
  | BoolType
  | FnPtrType FnType
  | PtrType (Maybe Type)
  | StructType (List1 Type)
  | UnionType (List1 Type)
  | ArrayType Type Int32
  | CoroutineState FnName
  deriving (Show, Eq, Generic, Hashable)

data FnType = FnType {params :: [(Type, IsRestrict)], isVarArgs :: Bool, ret :: Maybe Type}
  deriving (Show, Eq, Generic, Hashable)

typeSizeEstimate :: Type -> Int32
typeSizeEstimate = \case
  NumPrimType (AnIntT (IntT sz _)) -> fromIntegral $ intSizeToInt sz `div` 8
  NumPrimType (AFloatT F32T) -> 4
  NumPrimType (AFloatT F64T) -> 8
  BoolType -> 1
  FnPtrType _ -> 8
  PtrType _ -> 8
  StructType xs -> sum $ typeSizeEstimate <$> toList xs
  UnionType xs -> maximum $ typeSizeEstimate <$> toList xs
  ArrayType t sz -> typeSizeEstimate t * sz
  CoroutineState _ -> 100

data Constant'
  = ConstLit LExpr
  | ConstCastLit LExpr Type -- Adds an explicit cast
  | ConstStruct [Constant] -- TODO Rename ConstStructUnion
  | -- TODO Is there a more efficient way of storing array constants?
    ConstArray (List1 Constant') Type -- Type is the type of the elements
  | ConstSizeof Type
  deriving (Show, Eq, Generic, Hashable)

type Constant = (Constant', Type)

data Function = Function
  { dbgName :: Text,
    dbgFile :: Text,
    sr :: SrcRange,
    cName :: FnName,
    fnType :: FnType,
    -- if isCoroutine then fnType then gives the init parameters and yield type
    isCoroutine :: Bool,
    vars :: [(VarId, Type)],
    blocks :: [(BlockId, [Instr])]
  }
  deriving (Show, Generic)

-- Expressions that do not cause side effects and do not access mutable data
-- InitStruct/Array, SizeOf, BitCast, etc. are not in here in order to simplify the C transpiler
data LExpr
  = FloatOrDoubleLit Text -- Number is stored in textual form
  | BoolLit Bool
  | IntLit Integer
  | NullPtr
  | ConstName CName -- Use this for copies of constants and for function pointers
  | ConstNameAddrOf CName -- Use this for getting a pointer to constant data
  | ConstIdLit ConstId
  | LTmp TmpId
  | LGetVarPtr VarId
  | LAddPtr LExpr LExpr -- ptr + i
  | LSubPtr LExpr LExpr -- ptr - i
  | LEq LExpr LExpr
  | LNEq LExpr LExpr
  | LStructUnionElem LExpr Int
  | LStructUnionElemPtr LExpr Int
  deriving (Show, Eq, Generic, Hashable)

-- Instruction produces a value
-- In C, the order of evaluation of subexpressions is undefined so any instruction taking multiple values takes LExprs
data InstrV'
  = ILExpr LExpr
  | ICall LExpr [LExpr]
  | ILoadVar VarId
  | IPtrRead InstrV'
  | IIndexPtr LExpr LExpr -- ptr[i]
  | IArrayIndexPtr InstrV' Int32
  | IArrayIndex InstrV' Int32
  | IArrayIndexPtr' LExpr LExpr
  | IArrayIndex' LExpr LExpr
  | IStructUnionElemPtr InstrV' Int
  | IInitStruct (List1 LExpr) Type
  | IInitArray (List1 LExpr) Type
  | ISizeOf Type
  | IBitCast InstrV' Type
  | IInitCoroutine FnName [LExpr]
  | -- Produces Bool: true if value was produced, false if coroutine is done.
    -- If true, writes yielded value into given pointer
    IStepCoroutine' IStepCoroutine
  | ITakeException
  deriving (Show, Generic, Eq, Hashable)

data ICheckForException = ICheckForException
  { onThrowGoto :: BlockId,
    noThrowGoto :: BlockId
  }
  deriving (Show, Generic, Eq, Hashable)

data IStepCoroutine = IStepCoroutine {co :: FnName, coPtr :: LExpr, outPtr :: LExpr}
  deriving (Show, Generic, Eq, Hashable)

type InstrV = (InstrV', TmpId, Type)

type InstrVT = (InstrV', Type)

data Instr'
  = IInstrV InstrV
  | IGoTo BlockId
  | IGoToIfElse InstrV' BlockId BlockId
  | ICallVoid' ICallVoid
  | IPtrWrite' IPtrWrite
  | ISetVar VarId InstrV'
  | IReturn InstrV'
  | IReturnVoid
  | IYield' IYield
  | IAbortCoroutine InstrV' FnName
  | IAddUninitTmp TmpId Type
  | ISetUnion LExpr Int InstrV' -- TODO Take TmpId instead of LExpr, Rename to ISetUnionStructField
  | ISetUnionPtr LExpr Int InstrV'
  | IPanic Text
  | IThrow InstrV'
  | IBubbleException
  | ICheckForException' ICheckForException
  deriving (Show, Generic, Eq, Hashable)

type Instr = (Instr', SrcRange)

data IYield = IYield {yieldValue :: InstrV', continuationBlock :: BlockId, onFreeBlock :: BlockId}
  deriving (Show, Generic, Eq, Hashable)

data ICallVoid = ICallVoid {fn :: LExpr, args :: [LExpr], noReturn :: Bool}
  deriving (Show, Generic, Eq, Hashable)

data IPtrWrite = IPtrWrite {ptr :: LExpr, value :: LExpr}
  deriving (Show, Generic, Eq, Hashable)

newtype ConstId = ConstId IntId
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable, Default, IdType, IntIdType)
  deriving anyclass (Newtype)

newtype CName = CName Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

newtype FnName = FnName CName
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

newtype BlockId = BlockId IntId
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable, Default, IdType, IntIdType)
  deriving anyclass (Newtype)

-- Exclusive variables, IDs may be per-function
newtype VarId = VarId TextId
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable, Default, IdType, TextIdType)
  deriving anyclass (Newtype)

-- Immutable temporaries, id may be specific to a block
newtype TmpId = TmpId IntId
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable, Default, IdType, IntIdType)
  deriving anyclass (Newtype)
