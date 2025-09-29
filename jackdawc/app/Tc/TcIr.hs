-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.TcIr (module Tc.TcIr, module Hir) where

import AccessMode (AccessMode)
import Hir
  ( AccessorType (..),
    AnyTDef (..),
    AnyTDef2 (..),
    AnyVDef (..),
    ConstDef (..),
    Constant,
    Constant' (..),
    Destructure (..),
    DropFn,
    EnumDef (..),
    EnumDef2 (..),
    FnDef (..),
    FnType (..),
    GenericArg (..),
    IsTypeDef (..),
    IsVDef (..),
    IteratorType (..),
    LocalVarUid (..),
    Pattern (..),
    StructDef2 (..),
    TDefCommon (..),
    TDefId (..),
    Type (..),
    TypeDef (..),
    VDefCommon (..),
    VDefId (..),
    typeHasRuntimeRepr,
  )
import Names
import Prelude2
import SrcLoc

type GenericArg' = (GenericArg, SrcRange)

data Expr'
  = LoadConstantExpr Constant'
  | MkTupleExpr (List2 Expr)
  | AStructInitExpr StructInitExpr
  | ArrayInitExpr (List1 Expr)
  | ALocalVarExpr LocalVarExpr
  | AFieldAccessorExpr FieldAccessorExpr
  | APtrAddExpr PtrAddExpr
  | APtrSubExpr PtrSubExpr
  | PtrDerefExpr Expr
  | AFnCallExpr FnCallExpr
  | ACondOpExpr CondOpExpr
  | BitCast Expr
  | AndExpr Expr Expr
  | OrExpr Expr Expr
  | PtrEqExpr Expr Expr
  | PtrNEqExpr Expr Expr
  | AddressOfExpr Expr
  | UninitExpr
  | DataConsExpr Type Int (Maybe Expr)
  | ActiveDataConsExpr Expr
  | RawSliceToSliceExpr Expr
  | BubbleExpr Expr
  deriving (Show, Generic)

type Expr = (Expr', Type, SrcRange)

instance HasSrcRange Expr where
  startLoc (_, _, sr) = startLoc sr
  endLoc (_, _, sr) = endLoc sr
  filePath (_, _, sr) = filePath sr

data StructInitExpr = StructInitExpr {exprs :: List1 Expr, fieldIndexToExprsIndex :: List1 Int}
  deriving (Show, Generic)

data LocalVarExpr = LocalVarExpr {uid :: LocalVarUid, name :: VName'}
  deriving (Show, Generic)

data IfElseExpr = IfElseExpr {condExpr :: Expr, thenExpr :: Expr, elseExpr :: Expr}
  deriving (Show, Generic)

-- E.g. x.a.3.b
data FieldAccessorExpr = FieldAccessorExpr {expr :: Expr, index :: Int, dropFn :: Maybe DropFn}
  deriving (Show, Generic)

-- E.g. ptr + (3+y)
data PtrAddExpr = PtrAddExpr {expr :: Expr, index :: Expr}
  deriving (Show, Generic)

data PtrSubExpr = PtrSubExpr {expr :: Expr, index :: Expr}
  deriving (Show, Generic)

-- a ? b : c
data CondOpExpr = CondOpExpr {condExpr :: Expr, thenExpr :: Expr, elseExpr :: Expr}
  deriving (Show, Generic)

-- Args include drop fn in case arg is rvalue passed by reference
data FnCallExpr = FnCallExpr {fn :: Expr, args :: [(Expr, Maybe DropFn)], fnIsNoThrow :: Bool}
  deriving (Show, Generic)

data CodeBlock = CodeBlock {statements :: [Statement], finalExpr :: Expr}
  deriving (Show, Generic)

data Statement'
  = VarStmnt Destructure Expr
  | UninitVarStmnt LocalVarUid VName (Maybe DropFn) Type
  | AnAssignmentStmnt AssignmentStmnt
  | FnCallStmnt FnCallExpr
  | ExprStmnt Expr (Maybe DropFn) -- Value ignored
  | AnIfElseStmnt IfElseStmnt
  | LoopStmnt Statement
  | BreakStmnt
  | ContinueStmnt
  | CodeBlockStmnt [Statement]
  | ReturnStmnt (Maybe Expr) IsAccRawRet
  | YieldStmnt Expr
  | AForEachLoopStmnt ForEachLoopStmnt
  | ForLoopStmnt [(Destructure, Expr)] Expr [(AssignmentStmnt, SrcRange)] Statement
  | MatchStmnt AccessMode Expr (List1 MatchBranch)
  | ThrowStmnt Expr
  | TryCatchStmnt Statement (Maybe (LocalVarUid, VName, Type)) Statement
  | BubbleStmnt Expr
  deriving (Show, Generic)

type Statement = (Statement', SrcRange)

-- True if the value needs casting from a raw ptr/slice
type IsAccRawRet = Bool

data MatchBranch = MatchBranch
  { pattern :: Pattern,
    patternSr :: SrcRange,
    code :: Statement
  }
  deriving (Show, Generic)

data ForEachLoopStmnt = ForEachLoopStmnt
  { var :: Destructure,
    varMode :: AccessMode,
    yieldType :: Type,
    fn :: (VDefId, Type),
    iterFnIsNoThrow :: Bool,
    args :: [(Expr, Maybe DropFn)],
    body :: Statement
  }
  deriving (Show, Generic)

data IfElseStmnt = IfElseStmnt
  { cond :: Expr,
    thenStmnt :: Statement,
    elseStmntMaybe :: Maybe Statement
  }
  deriving (Show, Generic)

data AssignmentStmnt = AssignmentStmnt {lhs :: Maybe Expr, value :: Expr, lhsDestructor :: Maybe DropFn}
  deriving (Show, Generic)
