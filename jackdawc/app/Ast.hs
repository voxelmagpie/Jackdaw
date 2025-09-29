-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Ast where

import AccessMode
import HashMultiMap (HashMultiMap)
import InsOrdMap (InsOrdMap)
import Names
import Prelude2
import SrcLoc

data Ast = Ast
  { imports :: [Import],
    vDefs :: HashMap VName AnyVDef,
    tsDefs :: HashMap TName AnyTSDef,
    requireStmntsRev :: [RequireStmnt]
  }
  deriving (Show, Generic, Default)

data Import = Import Text SrcRange ImportNames
  deriving (Show, Generic, Eq)

newtype RequireStmnt = RequireStmnt Expr
  deriving (Show, Generic)
  deriving anyclass (Newtype)

data AnyTSDef = ATypeDef TypeDef | AStructDef StructDef | AnEnumDef EnumDef | ATypeAlias TypeAlias
  deriving (Show, Generic)

type MemberFns = (HashMap VName FnDef, HashMultiMap OpName FnDef)

data TSDefCommon = TSDefCommon
  { name :: TName',
    genericParams :: [GenericParameter],
    attributes :: [Attribute]
  }
  deriving (Show, Generic)

data TypeDefCommon = TypeDefCommon
  { c :: TSDefCommon,
    memberFns :: MemberFns,
    requireStmnts :: [RequireStmnt]
  }
  deriving (Show, Generic)

newtype TypeDef = TypeDef
  { c :: TypeDefCommon
  }
  deriving (Show, Generic)

data StructDef = StructDef
  { c :: TypeDefCommon,
    fields :: InsOrdMap VName (SrcRange, TypeExpr, [Attribute])
  }
  deriving (Show, Generic)

data EnumDef = EnumDef
  { c :: TypeDefCommon,
    dataCons :: InsOrdMap TName (SrcRange, Maybe TypeExpr)
  }
  deriving (Show, Generic)

data TypeAlias = TypeAlias
  { c :: TSDefCommon,
    typ :: Maybe TypeExpr
  }
  deriving (Show, Generic)

class IsTypeDef a where
  tDefCommon :: a -> TypeDefCommon

instance IsTypeDef TypeDef where
  tDefCommon x = x.c

instance IsTypeDef StructDef where
  tDefCommon x = x.c

instance IsTypeDef EnumDef where
  tDefCommon x = x.c

getTDefCommonMaybe :: AnyTSDef -> Maybe TypeDefCommon
getTDefCommonMaybe = \case
  ATypeDef d -> Just d.c
  AStructDef d -> Just d.c
  AnEnumDef d -> Just d.c
  ATypeAlias _ -> Nothing

class IsTSDef a where
  tsDefCommon :: a -> TSDefCommon

instance IsTSDef TypeDef where
  tsDefCommon x = x.c.c

instance IsTSDef EnumDef where
  tsDefCommon x = x.c.c

instance IsTSDef StructDef where
  tsDefCommon x = x.c.c

instance IsTSDef AnyTSDef where
  tsDefCommon = \case ATypeDef d -> d.c.c; AStructDef d -> d.c.c; AnEnumDef d -> d.c.c; ATypeAlias a -> a.c

data GenericParameter
  = TypeGenericParameter TName'
  | ValueGenericParameter VName'
  deriving (Show, Generic)

data VDefCommon = VDefCommon
  { name :: VName',
    genericParams :: [GenericParameter]
  }
  deriving (Show, Generic)

data ConstDef = ConstDef
  { c :: VDefCommon,
    typeExpr :: TypeExpr,
    expr :: Maybe Expr,
    attributes :: [Attribute]
  }
  deriving (Show, Generic)

data FnDef = FnDef
  { c :: VDefCommon,
    opMaybe :: Maybe OpName',
    isAccessor :: Bool,
    isIterator :: Bool,
    parameters :: [(Maybe VName', AccessMode, TypeExpr)],
    isVarArgs :: Bool,
    retType :: Maybe TypeExpr, -- Nothing == void
    attributes :: [Attribute],
    code :: Maybe Statement
  }
  deriving (Show, Generic)

data AnyVDef
  = AConstDef ConstDef
  | AFnDef FnDef
  deriving (Show, Generic)

class IsVDef a where
  vDefCommon :: a -> VDefCommon

instance IsVDef ConstDef where
  vDefCommon x = x.c

instance IsVDef FnDef where
  vDefCommon x = x.c

instance IsVDef AnyVDef where
  vDefCommon = \case AConstDef d -> d.c; AFnDef d -> d.c

data TypeExpr'
  = ANamedType NamedType
  | TupleType (List2 TypeExpr)
  | AFnType FnType
  | AnAccessorType AccessorType
  | SelfType
  | PtrType (Maybe TypeExpr)
  | ConstPtrType TypeExpr
  | TypeOf Expr
  deriving (Show, Generic)

data GenericArg
  = TypeGenericArg TypeExpr
  | ValueGenericArg Expr
  deriving (Show, Generic)

instance HasSrcRange GenericArg where
  startLoc = \case TypeGenericArg x -> startLoc x; ValueGenericArg x -> startLoc x
  endLoc = \case TypeGenericArg x -> endLoc x; ValueGenericArg x -> endLoc x
  filePath = \case TypeGenericArg x -> filePath x; ValueGenericArg x -> filePath x

data NamedType = NamedType {name :: TName', genericArgs :: [GenericArg]}
  deriving (Show, Generic)

data FnType = FnType
  { params :: [(AccessMode, TypeExpr)],
    isVarArgs :: Bool,
    ret :: Maybe TypeExpr, -- Nothing = void
    isNullable :: Bool
  }
  deriving (Show, Generic)

data AccessorType = AccessorType
  { params :: List1 (AccessMode, TypeExpr),
    isVarArgs :: Bool,
    ret :: TypeExpr
  }
  deriving (Show, Generic)

type TypeExpr = (TypeExpr', SrcRange)

data Expr'
  = IntLitExpr Integer
  | FloatLitExpr Text
  | BoolLitExpr Bool
  | StringLitExpr Text
  | CharLitExpr Char
  | NullPtrExpr
  | ANameExpr NameExpr
  | TypeAccessExpr TypeExpr NameExpr
  | TypeDataConsExpr (Maybe TypeExpr') SrcRange TName'
  | MkTupleExpr (List2 Expr)
  | StructInitExpr (Maybe TypeExpr') SrcRange StructFields
  | ArrayInitExpr (List1 Expr)
  | AnAccessorExpr AccessorExpr
  | AFnCallExpr FnCallExpr
  | AnInfixOpExpr InfixOpExpr
  | APrefixOpExpr PrefixOpExpr
  | AddressOfExpr Expr
  | AndExpr Expr SrcRange Expr
  | OrExpr Expr SrcRange Expr
  | ACondOpExpr CondOpExpr
  | CastExpr Expr TypeExpr
  | UninitExpr
  | BubbleExpr Expr
  deriving (Show, Generic)

type Expr = (Expr', SrcRange)

type StructFields = InsOrdMap VName (SrcRange, Maybe Expr)

data TypeMetadataExpr = TypeMetadataExpr {typ :: TypeExpr, name :: VName'}
  deriving (Show, Generic)

data NameExpr = NameExpr {name :: VName', genericArgsMaybe :: Maybe [GenericArg]}
  deriving (Show, Generic)

data InfixOpExpr = InfixOpExpr {op :: OpName', lhs :: Expr, rhs :: Expr}
  deriving (Show, Generic)

data PrefixOpExpr = PrefixOpExpr {op :: OpName', arg :: Expr}
  deriving (Show, Generic)

-- a ? b : c
data CondOpExpr = CondOpExpr {condExpr :: Expr, thenExpr :: Expr, elseExpr :: Expr}
  deriving (Show, Generic)

-- E.g. x.a, x.3
data AccessorExpr = AccessorExpr {expr :: Expr, accessor :: AccessorPart}
  deriving (Show, Generic)

-- Name accessor generic args are for member fn calls
data AccessorPart'
  = ANameAccessor VName (Maybe [GenericArg])
  | AnIndexAccessor Int
  | AnIndexExprAccessor Expr
  | AStarAccessor
  deriving (Show, Generic)

type AccessorPart = (AccessorPart', SrcRange)

data FnCallExpr = FnCallExpr {fn :: Expr, args :: [Expr]}
  deriving (Show, Generic)

data Statement'
  = AVarStmnt Destructure Expr
  | UninitVarStmnt VName' TypeExpr
  | AnAssignmentStmnt AssignmentStmnt
  | CompoundAssignmentOpStmnt InfixOpExpr
  | FnCallStmnt (FnCallExpr, SrcRange)
  | BubbleStmnt Expr
  | AnIfElseStmnt IfElseStmnt
  | LoopStmnt Statement
  | BreakStmnt
  | ContinueStmnt
  | CodeBlockStmnt [Statement]
  | ReturnStmnt (Maybe Expr)
  | AForEachLoopStmnt ForEachLoopStmnt
  | YieldStmnt Expr
  | ForLoopStmnt [(Destructure, Expr)] Expr [Statement] Bool Statement
  | ARequireStmnt RequireStmnt
  | MatchStmnt AccessMode Expr (List1 MatchBranch)
  | UnsafeStmnt Statement
  | ThrowStmnt Expr
  | TryCatchStmnt Statement (Maybe VName, SrcRange) Statement
  deriving (Show, Generic)

type Statement = (Statement', SrcRange)

data MatchBranch = MatchBranch
  { pattern :: Pattern,
    code :: Statement
  }
  deriving (Show, Generic)

data Pattern'
  = PatternAny
  | PatternName VName'
  | PatternDataCons0 TName
  | PatternDataCons1 TName' Pattern
  deriving (Show, Generic)

type Pattern = (Pattern', SrcRange)

data ForEachLoopStmnt = ForEachLoopStmnt
  { isConst :: Bool,
    mode :: AccessMode,
    var :: Destructure,
    inExpr :: Expr,
    body :: Statement
  }
  deriving (Show, Generic)

data IfElseStmnt = IfElseStmnt
  { isConst :: Bool,
    cond :: Expr,
    thenExpr :: Statement,
    elseExprMaybe :: Maybe Statement
  }
  deriving (Show, Generic)

data Destructure'
  = NameDes VName' (Maybe TypeExpr)
  | IgnoreDes (Maybe TypeExpr)
  | TupleDes (List2 Destructure)
  | ArrayDes (List1 Destructure)
  | StructDes (InsOrdMap VName (SrcRange, Destructure))
  deriving (Show, Generic)

type Destructure = (Destructure', SrcRange)

data AssignmentStmnt = AssignmentStmnt {lhs :: Maybe Expr', lhsSr :: SrcRange, value :: Expr}
  deriving (Show, Generic)
