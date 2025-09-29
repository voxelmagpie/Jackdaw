-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Hir where

import AccessMode
import Data.HashTable.IO qualified as HT
import Data.Int (Int32)
import IdTypes
import InsOrdMap (InsOrdMap)
import Names
import Prelude2
import Primitives
import SrcLoc (SrcRange)
import Tables (tblEmpty, tblToList)
import Tables qualified as Tbl

type IsNoThrow = Bool

data Ir = Ir
  { vDefs :: Tbl.Table VDefId AnyVDef,
    fnBodies :: HashTable VDefId (Statement, IsNoThrow),
    -- Dependant -> depends-on
    -- This is so the lowerer can compile C coroutine functions in the correct order
    -- There are guaranteed to be no circular dependencies (TODO)
    fnDeps :: HashTable VDefId [VDefId],
    tDefs :: Tbl.Table TDefId AnyTDef,
    tDefs2 :: HashTable TDefId AnyTDef2
  }

data Ir' = Ir'
  { tDefs :: [(TDefId, AnyTDef)],
    vDefs :: [(VDefId, AnyVDef)],
    fnBodies :: [(VDefId, (Statement, IsNoThrow))],
    fnDeps :: [(VDefId, [VDefId])]
  }
  deriving (Show)

emptyHir :: IO Ir
emptyHir = Ir <$> tblEmpty <*> HT.new <*> HT.new <*> tblEmpty <*> HT.new

-- Type definitions are split in 2 to allow recursive types via pointers
-- (same as in C but without needing to forward declare the type)
-- The first type contains all the information that can be gathered from the AST,
-- without getting the types of fields

data AnyTDef = AStructDef TDefCommon | AnEnumDef EnumDef
  deriving (Show, Generic)

data AnyTDef2 = AStructDef2 StructDef2 | AnEnumDef2 EnumDef2
  deriving (Show, Generic)

data AnyVDef = AConstDef ConstDef | AFnDef FnDef
  deriving (Show, Generic)

newtype VDefId = VDefId IntId
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable, Default, IdType, IntIdType)
  deriving anyclass (Newtype)

newtype TDefId = TDefId IntId
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable, Default, IdType, IntIdType)
  deriving anyclass (Newtype)

data TDefCommon = TDefCommon
  { name :: TName,
    fqn :: TFqn,
    namespace :: Namespace,
    genericArgs :: [GenericArg],
    attributes :: [Attribute]
  }
  deriving (Show, Generic)

newtype TypeDef = TypeDef
  { c :: TDefCommon
  }
  deriving (Show, Generic)

data StructDef2 = StructDef2
  { c :: TDefCommon,
    nonCopyable :: Bool, -- Has onDrop or no-copy fields
    fields :: InsOrdMap VName (Type, [Attribute])
  }
  deriving (Show, Generic)

data EnumDef = EnumDef
  { c :: TDefCommon,
    canBeCastedToInt :: Bool,
    dataConsCount :: Int
  }
  deriving (Show, Generic)

data EnumDef2 = EnumDef2
  { e :: EnumDef,
    tagType :: Type,
    nonCopyable :: Bool, -- Has onDrop
    dataCons :: InsOrdMap TName (Maybe Type)
  }
  deriving (Show, Generic)

class IsTypeDef a where
  tDefCommon :: a -> TDefCommon

instance IsTypeDef TypeDef where
  tDefCommon x = x.c

instance IsTypeDef EnumDef where
  tDefCommon x = x.c

instance IsTypeDef StructDef2 where
  tDefCommon x = x.c

instance IsTypeDef EnumDef2 where
  tDefCommon x = x.e.c

instance IsTypeDef AnyTDef where
  tDefCommon = \case AStructDef d -> d; AnEnumDef d -> d.c

instance IsTypeDef AnyTDef2 where
  tDefCommon = \case AStructDef2 d -> d.c; AnEnumDef2 d -> d.e.c

data VDefCommon = VDefCommon
  { name :: VName',
    fqn :: VFqn,
    genericArgs :: [GenericArg],
    typ :: Type,
    reachableFromStart :: Bool,
    attributes :: [Attribute]
  }
  deriving (Show, Generic)

data ConstDef = ConstDef
  { c :: VDefCommon,
    value :: Maybe Constant'
  }
  deriving (Show, Generic)

data FnDef = FnDef
  { c :: VDefCommon,
    isAccessor :: Bool,
    isIterator :: Bool,
    parameters :: [(AccessMode, Type, Maybe VName)],
    isVarArgs :: Bool,
    returnType :: Maybe Type
  }
  deriving (Show, Generic)

class IsVDef a where
  vDefCommon :: a -> VDefCommon

instance IsVDef ConstDef where
  vDefCommon x = x.c

instance IsVDef FnDef where
  vDefCommon x = x.c

instance IsVDef AnyVDef where
  vDefCommon = \case AConstDef d -> d.c; AFnDef d -> d.c

data Type
  = ANamedType TDefId
  | TupleType (List2 Type)
  | AFnType FnType
  | AnAccessorType AccessorType
  | AnIteratorType IteratorType
  | AnAccessorIteratorType AccessorType
  | PtrType (Maybe Type)
  | ConstPtrType Type
  | ArrayType Type Int32
  | NumPrimType NumPrim
  | BoolType
  | SliceType Type
  deriving (Show, Eq, Generic, Hashable)

typeHasRuntimeRepr :: Type -> Bool
typeHasRuntimeRepr = \case
  ANamedType _ -> True
  TupleType xs -> all typeHasRuntimeRepr xs
  AFnType _ -> True
  AnAccessorType _ -> True
  AnIteratorType _ -> True
  AnAccessorIteratorType _ -> True
  PtrType _ -> True
  ConstPtrType _ -> True
  ArrayType x _ -> typeHasRuntimeRepr x
  NumPrimType _ -> True
  BoolType -> True
  SliceType _ -> False

data FnType = FnType {params :: [(AccessMode, Type)], isVarArgs :: Bool, ret :: Maybe Type, isNullable :: Bool}
  deriving (Show, Eq, Generic, Hashable)

data AccessorType = AccessorType {params :: List1 (AccessMode, Type), isVarArgs :: Bool, ret :: Type}
  deriving (Show, Eq, Generic, Hashable)

data IteratorType = IteratorType {params :: [(AccessMode, Type)], ret :: Type}
  deriving (Show, Eq, Generic, Hashable)

data Constant'
  = ConstFloatOrDouble Text -- Number is stored in textual form
  | ConstBool Bool
  | ConstInt Integer
  | ConstNullPtr
  | ConstStructOrTuple [Constant]
  | ConstArray Type (List1 Constant')
  | ConstSizeof Type
  | ConstFnPtr VDefId
  | ConstExtern VDefId
  | ConstAddrOf Constant
  | ConstAddrOfArray0 Constant -- Address of first element in constant array
  deriving (Show, Eq, Generic, Hashable)

type Constant = (Constant', Type)

data GenericArg
  = TypeGenericArg Type
  | ValueGenericArg Constant
  deriving (Show, Eq, Generic, Hashable)

-- Expressions which produce and r-value
data Expr'
  = LoadConstantExpr Constant
  | MkTupleExpr (List2 Expr)
  | AStructInitExpr StructInitExpr
  | ArrayInitExpr (List1 Expr)
  | AFnCallExpr FnCallExpr
  | ACondOpExpr CondOpExpr
  | AGetFieldExpr GetFieldExpr
  | AGetFieldFromAccExpr GetFieldFromAccExpr
  | DerefAccessorExpr AccessorExpr
  | MoveLocalVarExpr LocalVarUid VName
  | BitCast Expr Type
  | APtrAddExpr PtrAddExpr
  | APtrSubExpr PtrSubExpr
  | AndExpr Expr Expr
  | OrExpr Expr Expr
  | PtrEqExpr Expr Expr
  | PtrNEqExpr Expr Expr
  | AddressOfExpr AccessorExpr
  | UninitExpr Type
  | DataConsExpr Type Int (Maybe Expr)
  | ActiveDataConsExpr (Either Expr AccessorExpr)
  | DataConsUnsafeAddrOfExpr Expr Int
  | SliceAsRawExpr AccessorExpr
  | BubbleExpr Expr DropFns
  deriving (Show, Generic)

type Expr = (Expr', SrcRange)

-- E.g. ptr + (3+y)
data PtrAddExpr = PtrAddExpr {expr :: Expr, index :: Expr, pointeeType :: Type}
  deriving (Show, Generic)

data PtrSubExpr = PtrSubExpr {expr :: Expr, index :: Expr, pointeeType :: Type}
  deriving (Show, Generic)

data StructInitExpr = StructInitExpr {exprs :: List1 Expr, fieldIndexToExprsIndex :: List1 Int}
  deriving (Show, Generic)

data LocalVarExpr = LocalVarExpr {uid :: LocalVarUid, name :: VName}
  deriving (Show, Generic)

-- First IDs are always the function parameters (if any)
-- Starts from zero for every constant/function
newtype LocalVarUid = LocalVarUid Int
  deriving (Show, Eq, Generic)
  deriving newtype (Hashable)
  deriving anyclass (Newtype)

-- Expressions which produce a reference
data AccessorExpr'
  = ALocalVarAccessorExpr LocalVarAccessorExpr
  | ConstantAccessorExpr Constant
  | AFieldAccessorExpr FieldAccessorExpr
  | AccessorCallExpr AccessorFnCallExpr
  | PtrDerefExpr Expr Type -- Type is pointee type
  | DataConsUnsafeAccessorExpr AccessorExpr Int
  | RawSliceToSliceExpr Expr Type -- Type is pointee type
  deriving (Show, Generic)

type AccessorExpr = (AccessorExpr', SrcRange)

data LocalVarAccessorExpr = LocalVarAccessorExpr {uid :: LocalVarUid, name :: VName}
  deriving (Show, Generic)

-- E.g. x.a.3.b
data FieldAccessorExpr = FieldAccessorExpr {expr :: AccessorExpr, index :: Int}
  deriving (Show, Generic)

-- E.g. x.a.3.b
data GetFieldExpr = GetFieldExpr
  { expr :: Expr,
    index :: Int,
    dropFn :: Maybe DropFn
  }
  deriving (Show, Generic)

data GetFieldFromAccExpr = GetFieldFromAccExpr
  { expr :: AccessorExpr,
    index :: Int
  }
  deriving (Show, Generic)

-- a ? b : c
data CondOpExpr = CondOpExpr
  { condExpr :: Expr,
    thenExpr :: Expr,
    elseExpr :: Expr,
    -- Drop fns to be run at end of branch (for vars moved in other branch)
    dropFnsForThen :: DropFns,
    dropFnsForElse :: DropFns
  }
  deriving (Show, Generic)

data AccessorFnCallExpr = AccessorFnCallExpr
  { mode :: AccessMode,
    fn :: Expr,
    selfArg :: AccessorExpr,
    args :: [FnArg],
    dropFnsIfMayThrow :: Maybe DropFns
  }
  deriving (Show, Generic)

type DropFn = VDefId

data FnArg = RValueArg Expr | RefArg (AccessorExpr, AccessMode) | RValueRefArg (Expr, AccessMode, Maybe DropFn)
  deriving (Show, Generic)

data FnCallExpr = FnCallExpr
  { fn :: Expr,
    args :: [FnArg],
    dropFnsIfMayThrow :: Maybe DropFns
  }
  deriving (Show, Generic)

data CodeBlock = CodeBlock {statements :: [Statement], finalExpr :: Expr}
  deriving (Show, Generic)

type DropFns = [(LocalVarUid, DropFn)]

data Statement'
  = VarStmnt Destructure Expr
  | UninitVarStmnt LocalVarUid VName (Maybe DropFn) Type
  | AnAssignmentStmnt AssignmentStmnt
  | FnCallStmnt FnCallExpr
  | ExprStmnt Expr (Maybe DropFn)
  | AnIfElseStmnt IfElseStmnt
  | LoopStmnt Statement
  | BreakStmnt DropFns
  | ContinueStmnt DropFns
  | CodeBlockStmnt [Statement] DropFns
  | ReturnStmnt (Maybe Expr) DropFns
  | AccessorReturnStmnt AccessorExpr DropFns -- For accessor functions only
  | YieldStmnt Expr DropFns -- Drop fns are for if the loop is terminated early
  | AccessorYieldStmnt AccessorExpr DropFns -- For accessor iterator functions only
  | AForEachLoopStmnt ForEachLoopStmnt
  | AForLoopStmnt ForLoopStmnt
  | MatchStmnt AccessMode (Either Expr AccessorExpr) (List1 MatchBranch)
  | ThrowStmnt Expr DropFns -- Expr always loads a *const String
  | TryCatchStmnt Statement (Maybe (LocalVarUid, VName, Type)) Statement
  | BubbleStmnt Expr DropFns
  deriving (Show, Generic)

type Statement = (Statement', SrcRange)

data MatchBranch = MatchBranch
  { pattern :: Pattern,
    patternSr :: SrcRange,
    code :: Statement,
    dropFns :: DropFns
  }
  deriving (Show, Generic)

-- Drop fns ignored if pattern matching on a reference
data Pattern
  = PatternAny (Maybe DropFn)
  | PatternName LocalVarUid VName' (Maybe DropFn)
  | PatternDataCons0 Int
  | PatternDataCons1 Int Pattern
  deriving (Show, Generic)

data Destructure
  = NameDes LocalVarUid VName' (Maybe DropFn)
  | IgnoreDes (Maybe DropFn)
  | TupleDes (List2 Destructure)
  | ArrayDes (List1 Destructure)
  | AStructDes (List1 (Destructure, FieldIndex))
  -- TODO Need drop fns for missing fields
  deriving (Show, Generic)

data ForLoopStmnt = ForLoopStmnt
  { vars :: [(Destructure, Expr)],
    cond :: Expr,
    assignments :: [Statement],
    innerStmnt :: Statement,
    dropFns :: DropFns
  }
  deriving (Show, Generic)

data ForEachLoopStmnt = ForEachLoopStmnt
  { var :: Destructure,
    varMode :: AccessMode,
    yieldType :: Type,
    iterFn :: VDefId,
    args :: Either [FnArg] (AccessMode, AccessorExpr, [FnArg]),
    body :: Statement,
    dropFns :: DropFns,
    onIterThrowDropFns :: Maybe DropFns
  }
  deriving (Show, Generic)

data IfElseStmnt = IfElseStmnt
  { cond :: Expr,
    thenStmnt :: Statement,
    elseStmntMaybe :: Maybe Statement,
    -- Drop fns to be run at end of branch (for vars moved in other branch)
    dropFnsForThen :: DropFns,
    dropFnsForElse :: DropFns
  }
  deriving (Show, Generic)

type FieldIndex = Int

data AssignmentStmnt = AssignmentStmnt {lhs :: AccessorExpr, value :: Expr, lhsDestructor :: Maybe DropFn}
  deriving (Show, Generic)

showIr :: Ir -> IO Text
showIr ir = do
  ir' <- Ir' <$> tblToList ir.tDefs <*> tblToList ir.vDefs <*> HT.toList ir.fnBodies <*> HT.toList ir.fnDeps
  pure $ tShow ir'

class (Monad m) => MonadHirRead m where
  getVDef :: VDefId -> m AnyVDef
  getFnDefBodyMaybe :: VDefId -> m (Maybe (Statement, IsNoThrow))
  getFnDeps :: VDefId -> m [VDefId]
  getTDef :: TDefId -> m AnyTDef
  getTDef2 :: TDefId -> m AnyTDef2
  loopOverVDefs :: (VDefId -> m ()) -> m ()
  loopOverTSDefs :: (TDefId -> m ()) -> m ()
