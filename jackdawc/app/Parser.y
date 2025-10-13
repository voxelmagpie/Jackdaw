-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

{
{-# LANGUAGE FieldSelectors #-}
{-# LANGUAGE ImplicitPrelude #-}
{-# LANGUAGE NoStrictData #-}
{-# OPTIONS_GHC -O2 #-}

module Parser(parseJackdawAst) where

import Tokens
import Ast qualified as A
import Names
import SrcLoc
import Prelude2((<&>), Text, consMaybe, List1(..), List2(..), HashMap, first, second, Default (..), un, fst3)
import ParserHelperCode
import Data.HashMap.Strict qualified as HM
import Data.Default (Default (def))
import Data.Maybe (fromMaybe, isJust)
import AccessMode
import InsOrdMap qualified as Ins


}


%name parseJackdawAst
%tokentype { TokenL }
%error { parseError }
%errorhandlertype explist
%monad { ParseM }

%token
    ';'     { (Symbol ';', _) }
    ':'     { (Symbol ':', _) }
    ','     { (Symbol ',', _) }
    '.'     { (Symbol '.', _) }
    '?'     { (Symbol '?', _) }
    '@'     { (Symbol '@', _) }
    '='     { (Symbol '=', _) }
    '...'   { (VarArgsToken, _) }
    '_'     { ((IdentOrKw (VName "_")), _) }

    'Self'      { (TypeName (TName "Self"), _) }
    
    typeName    { ((TypeName _), _) }
    floatlit    { ((FloatLiteral _), _) }
    intlit      { ((IntLiteral _), _) }
    stringlit   { ((StringLiteral _), _) }
    charlit     { ((CharLiteral _), _) }

    -- Operators
    '+'     { (Op (OpName "+"), _) }
    '-'     { (Op (OpName "-"), _) }
    '*'     { (Op (OpName "*"), _) }
    '+%'     { (Op (OpName "+%"), _) }
    '-%'     { (Op (OpName "-%"), _) }
    '*%'     { (Op (OpName "*%"), _) }
    '/'     { (Op (OpName "/"), _) }
    '%'     { (Op (OpName "%"), _) }
    '=='    { (Op (OpName "=="), _) }
    '!='    { (Op (OpName "!="), _) }
    '>'     { (Op (OpName ">"), _) }
    '<'     { (Op (OpName "<"), _) }
    '>='    { (Op (OpName ">="), _) }
    '<='    { (Op (OpName "<="), _) }
    '!'     { (Op (OpName "!"), _) }
    '<<'    { (Op (OpName "<<"), _) }
    '>>'    { (Op (OpName ">>"), _) }
    '&'     { (Op (OpName "&"), _) }
    '|'     { (Op (OpName "|"), _) }
    '~'     { (Op (OpName "~"), _) }
    '++'    { (Op (OpName "++"), _) }
    '+='    { (Op (OpName "+="), _) }
    '-='    { (Op (OpName "-="), _) }
    '+%='   { (Op (OpName "+%="), _) }
    '-%='   { (Op (OpName "-%="), _) }
    '<<='   { (Op (OpName "<<="), _) }
    '>>='   { (Op (OpName ">>="), _) }
    '&='    { (Op (OpName "&="), _) }
    '|='    { (Op (OpName "|="), _) }
    '~='    { (Op (OpName "~="), _) }
    '++='   { (Op (OpName "++="), _) }
    '*='    { (Op (OpName "*="), _) }
    '*%='   { (Op (OpName "*%="), _) }
    '/='    { (Op (OpName "/="), _) }
    '%='    { (Op (OpName "%="), _) }

    -- Brackets
    '(' { (Symbol '(', _) }
    ')' { (Symbol ')', _) }
    '[' { (Symbol '[', _) }
    ']' { (Symbol ']', _) }
    '{' { (Symbol '{', _) }
    '}' { (Symbol '}', _) }
    
    -- Keywords
    'if'            { (IdentOrKw (VName "if"), _) }
    'else'          { (IdentOrKw (VName "else"), _) }
    'type'          { (IdentOrKw (VName "type"), _) }
    'enum'          { (IdentOrKw (VName "enum"), _) }
    'struct'        { (IdentOrKw (VName "struct"), _) }
    'union'        { (IdentOrKw (VName "union"), _) }
    'var'           { (IdentOrKw (VName "var"), _) }
    'fn'            { (IdentOrKw (VName "fn"), _) }
    'accessor'      { (IdentOrKw (VName "accessor"), _) }
    'iterator'      { (IdentOrKw (VName "iterator"), _) }
    'const'         { (IdentOrKw (VName "const"), _) }
    'alias'         { (IdentOrKw (VName "alias"), _) }
    'loop'          { (IdentOrKw (VName "loop"), _) }
    'break'         { (IdentOrKw (VName "break"), _) }
    'continue'      { (IdentOrKw (VName "continue"), _) }
    'ref'           { (IdentOrKw (VName "ref"), _) }
    'in'            { (IdentOrKw (VName "in"), _) }
    'return'        { (IdentOrKw (VName "return"), _) }
    'true'          { (IdentOrKw (VName "true"), _) }
    'false'         { (IdentOrKw (VName "false"), _) }
    'void'          { (IdentOrKw (VName "void"), _) }
    'nullptr'       { (IdentOrKw (VName "nullptr"), _) }
    'as'            { (IdentOrKw (VName "as"), _) }
    'for'           { (IdentOrKw (VName "for"), _) }
    'foreach'       { (IdentOrKw (VName "foreach"), _) }
    'and'           { (IdentOrKw (VName "and"), _) }
    'or'            { (IdentOrKw (VName "or"), _) }
    'yield'         { (IdentOrKw (VName "yield"), _) }
    'require'       { (IdentOrKw (VName "require"), _) }
    'uninitialised' { (IdentOrKw (VName "uninitialised"), _) }
    'match'         { (IdentOrKw (VName "match"), _) }
    'import'        { (IdentOrKw (VName "import"), _) }
    'unsafe'        { (IdentOrKw (VName "unsafe"), _) }
    'throw'         { (IdentOrKw (VName "throw"), _) }
    'try'           { (IdentOrKw (VName "try"), _) }
    'catch'         { (IdentOrKw (VName "catch"), _) }
    'borrow'        { (IdentOrKw (VName "borrow"), _) }
    

    name { (IdentOrKw __, _) }

%nonassoc 'and' 'or'
-- %nonassoc AnyLogicalOp AnyLogicalOp
%nonassoc '>' '>=' '<' '<='
%left '+' '-' '+%' '-%'
%left '*' '/' '*%'
%right '?' ':'

%%

--

Ast :: {A.Ast}
    : Many(Import) Ast_ {$2 { A.imports = $1 }}


Import :: {A.Import}
    : 'import' stringlit MaybeQual {A.Import (getStringLit $2) (snd $2) $3 AllNames}
    | 'import' stringlit MaybeQual '(' List(VNameOrTName, ',') ')' {A.Import (getStringLit $2) (snd $2) $3 $ VisibleNames $5}
    | 'import' stringlit MaybeQual '~' '(' List(VNameOrTName, ',') ')' {A.Import (getStringLit $2) (snd $2) $3 $ HiddenNames $6}


MaybeQual :: {Maybe TName'}
    : {Nothing}
    | 'as' TName {Just $2}


VNameOrTName :: {Text}
    : VName {un $ fst $1}
    | TName {un $ fst $1}


Ast_ :: {A.Ast}
    : { def }
    | Ast_ ConstDef  {% addVDef ($1).astVDefs $2 <&> \x -> $1 { A.astVDefs = x } }
    | Ast_ FnDef  {% addVDef ($1).astVDefs $2 <&> \x -> $1 { A.astVDefs = x } }
    | Ast_ TSDef     {% hmTryInsert (snd $ fst $2) (fst $ fst $2) (snd $2) ($1).tsDefs <&> \x -> $1 { A.tsDefs = x } }
    | Ast_ RequireStmnt { $1 { A.requireStmntsRev = (fst $2) : ($1).requireStmntsRev } }


Attribute :: {Attribute}
    : '@' TName { Attribute $ un $ fst $2 }


RequireStmnt :: {(A.RequireStmnt, SrcRange)}
    : 'require' Expr {(A.RequireStmnt $2, srcRangeOf $1 $2)}


TSDef :: {(TName', A.AnyTSDef)}
    : Many(Attribute) 'type' Empty TName GPsMaybe '{' Many(RequireStmnt) VDefs '}' { ($4, A.ATypeDef $ A.TypeDef $ A.TypeDefCommon (A.TSDefCommon $4 $5 $1) $8 ($7 <&> fst)) }
    | Many(Attribute) 'struct' Empty TName GPsMaybe '{' Many(RequireStmnt) StructFields VDefs '}' { ($4, A.AStructDef $ A.StructDef (A.TypeDefCommon (A.TSDefCommon $4 $5 $1) $9 ($7 <&> fst)) $8) }
    | Many(Attribute) 'union' Empty TName GPsMaybe '{' Many(RequireStmnt) UnionFields VDefs '}' { ($4, A.AUnionDef $ A.UnionDef (A.TypeDefCommon (A.TSDefCommon $4 $5 $1) $9 ($7 <&> fst)) $8) }
    | Many(Attribute) 'enum' Empty TName GPsMaybe '{' Many(RequireStmnt) EnumFields VDefs '}' { ($4, A.AnEnumDef $ A.EnumDef (A.TypeDefCommon (A.TSDefCommon $4 $5 $1) $9 ($7 <&> fst)) $8) }
    | Many(Attribute) 'alias' TName GPsMaybe Maybe(AliasTypeExpr) { ($3, A.ATypeAlias $ A.TypeAlias (A.TSDefCommon $3 $4 $1) $5) }


AliasTypeExpr :: {A.TypeExpr}
    :  '=' TypeExpr {$2}


StructFields :: {Ins.InsOrdMap VName (SrcRange, A.TypeExpr, [Attribute])}
    : StructField { Ins.singleton (fst $1) (snd $1) }
    | StructFields ',' StructField {% maybe (parseError' ("Duplicate field name", fst3 $ snd $3)) pure $ Ins.tryInsert (fst $3) (snd $3) $1 }


StructField :: {(VName, (SrcRange, A.TypeExpr, [Attribute]))}
    : Many(Attribute) VName ':' TypeExpr { (fst $2, (snd $2, $4, $1)) }


EnumFields :: {Ins.InsOrdMap VName (SrcRange, Maybe A.TypeExpr, [Attribute])}
    : EnumField { Ins.singleton (fst $1) (snd $1) }
    | EnumFields ',' EnumField {% maybe (parseError' ("Duplicate field name", fst3 $ snd $3)) pure $ Ins.tryInsert (fst $3) (snd $3) $1 }


EnumField :: {(VName, (SrcRange, Maybe A.TypeExpr, [Attribute]))}
    : Many(Attribute) VName { ((fst $2), (snd $2, Nothing, $1)) }
    | Many(Attribute) VName '(' TypeExpr ')' { ((fst $2), (snd $2, Just $4, $1)) }


UnionFields :: {Ins.InsOrdMap VName (SrcRange, A.TypeExpr, [Attribute])}
    : UnionField { Ins.singleton (fst $1) (snd $1) }
    | UnionFields ',' UnionField {% maybe (parseError' ("Duplicate field name", fst3 $ snd $3)) pure $ Ins.tryInsert (fst $3) (snd $3) $1 }


UnionField :: {(VName, (SrcRange, A.TypeExpr, [Attribute]))}
    : Many(Attribute) VName '(' TypeExpr ')' { ((fst $2), (snd $2, $4, $1)) }


VDefs :: {A.VDefs}
    : {def}
    | VDefs FnDef {% addVDef $1 $2 }
    | VDefs ConstDef {% addVDef $1 $2 }


Empty :: {()}
    : {()}


ConstDef :: {(VName', A.AnyVDef)}
    : Many(Attribute) 'const' Maybe(AnyOp) VName GPsMaybe ':' TypeExpr '=' Expr { ($4, A.AConstDef $ A.ConstDef (A.VDefCommon $4 $5 $3 $1) $7 (Just $9)) }
    | Many(Attribute) 'const' Maybe(AnyOp) VName GPsMaybe ':' TypeExpr { ($4, A.AConstDef $ A.ConstDef (A.VDefCommon $4 $5 $3 $1) $7 Nothing) }


FnDef :: {(VName', A.AnyVDef)}
    : Many(Attribute) 'fn' Maybe(AnyOp) VName GPsMaybe '(' FnParams ')' Maybe(ReturnTypeExpr) FnDefCodeBlockStmnt { ($4, A.AFnDef $ A.FnDef (A.VDefCommon $4 $5 $3 $1) False False (fst $7) (snd $7) $9 $10) }
    | Many(Attribute) AccOrIterOrBoth Maybe(AnyOp) VName GPsMaybe '(' FnParams ')' Maybe(ReturnTypeExpr) FnDefCodeBlockStmnt { ($4, A.AFnDef $ A.FnDef (A.VDefCommon $4 $5 $3 $1) (fst $2) (snd $2) (fst $7) (snd $7) $9 $10) }


FnDefCodeBlockStmnt :: {Maybe A.Statement}
    : {Nothing}
    | CodeBlockStmnt {Just $1}
    | 'unsafe' CodeBlockStmnt {Just (A.UnsafeStmnt $2, srcRangeOf $1 $2)}


AccOrIterOrBoth :: {(Bool, Bool)}
    : 'accessor' {(True, False)}
    | 'iterator' {(False, True)}
    | 'accessor' 'iterator' {(True, True)}

ReturnTypeExpr :: {A.TypeExpr}
    : ':' TypeExpr {$2}


FnParam :: { Either (Maybe VName', AccessMode, A.TypeExpr) SrcRange }
    : AccessMode TypeExpr {Left (Nothing, $1, $2)}
    | AccessMode VName ':' TypeExpr {Left (Just $2, $1, $4)}
    | '...' {Right $ snd $1}


FnParams :: { ([(Maybe VName', AccessMode, A.TypeExpr)], Bool) }
    : List(FnParam, ',') {% getParams $1}



AnyOp :: {OpName'}
    : '==' {getOp $1}
    | '!=' {getOp $1}
    | '>' {getOp $1}
    | '>=' {getOp $1}
    | '<' {getOp $1}
    | '<=' {getOp $1}
    | '++' {getOp $1}
    | '+' {getOp $1}
    | '-' {getOp $1}
    | '*' {getOp $1}
    | '+%' {getOp $1}
    | '-%' {getOp $1}
    | '*%' {getOp $1}
    | '/' {getOp $1}
    | '%' {getOp $1}
    | '!' {getOp $1}
    | '<<' {getOp $1}
    | '>>' {getOp $1}
    | '&' {getOp $1}
    | '|' {getOp $1}
    | '~' {getOp $1}
    | '+=' {getOp $1}
    | '-=' {getOp $1}
    | '+%=' {getOp $1}
    | '-%=' {getOp $1}
    | '<<=' {getOp $1}
    | '>>=' {getOp $1}
    | '&=' {getOp $1}
    | '|=' {getOp $1}
    | '~=' {getOp $1}
    | '++=' {getOp $1}
    | '*=' {getOp $1}
    | '*%=' {getOp $1}
    | '/=' {getOp $1}
    | '%=' {getOp $1}


AccessMode :: {AccessMode}
    : {Shared}
    | 'ref' {Exclusive}
    | 'var' {Move}


GPsMaybe :: {[A.GenericParameter]}
    : {def}
    | '[' ListNE(GenParam, ',') ']' {$2}


GenParam :: {A.GenericParameter}
    : TName {A.TypeGenericParameter $1}
    | VName {A.ValueGenericParameter $1}


TypeExpr :: {A.TypeExpr}
    : AtomTypeExpr {$1}
    | NullableMaybe 'fn' '(' FnTypeParams ')' Maybe(ReturnTypeExpr) {(A.AFnType $ A.FnType (fst $4) (snd $4) $6 (isJust $1), srcRangeOf (case $1 of Just x -> x; _ -> snd $2) (case $6 of Just x -> snd x; _ -> snd $5))}
    | 'accessor' '(' FnTypeParams ')' ReturnTypeExpr {(A.AnAccessorType $ A.AccessorType (List1 (head $ fst $3) $ tail $ fst $3) (snd $3) $5, srcRangeOf $1 $5)}
 

FnTypeParam :: {Either (AccessMode, A.TypeExpr) SrcRange}
    : AccessMode TypeExpr {Left ($1, $2)}
    | '...' {Right $ snd $1}
 

FnTypeParams :: { ([(AccessMode, A.TypeExpr)], Bool) }
    : List(FnTypeParam, ',') {% getParams $1 }


NullableMaybe :: {Maybe SrcRange}
    : {Nothing}
    | '?' {Just $ snd $1}


AtomTypeExpr :: {A.TypeExpr}
    : TName GenericArgs {(A.NamedType Nothing $1 (Just $2), srcRangeOf $1 $2)}
    | TName {(A.NamedType Nothing $1 Nothing, snd $1)}
    | AtomTypeExpr '.' TName {(A.NamedType (Just $1) $3 Nothing, srcRangeOf $1 $3)}
    | AtomTypeExpr '.' TName GenericArgs {(A.NamedType (Just $1) $3 (Just $4), srcRangeOf $1 $4)}
    | 'Self' {(A.SelfType, snd $1)}
    | '(' TupleContents ')' { (A.TupleType $2, srcRangeOf $1 $3) }
    | '*' 'void' {(A.PtrType Nothing, srcRangeOf $1 $2)}
    | '*' TypeExpr {(A.PtrType $ Just $2, srcRangeOf $1 $2)}
    | '*' 'const' TypeExpr {(A.ConstPtrType $3, srcRangeOf $1 $3)}
    | 'type' '(' Expr ')' {(A.TypeOf $3, srcRangeOf $1 $2)}



GenericArgs :: {[A.GenericArg]}
    : '[' ListNE(GenericArg, ',') ']' {$2}

GenericArg :: {A.GenericArg}
    : TypeExpr {A.TypeGenericArg $1}
    | Expr {A.ValueGenericArg $1}


GenericArgsMaybe :: {Maybe [A.GenericArg]}
    : {Nothing}
    | GenericArgs {Just $1}


TupleContents :: {List2 A.TypeExpr}
    : TypeExpr ',' ListNE(TypeExpr, ',') { List2 $1 (head $3) $ tail $3 }


VName :: {VName'}
    : name { (getValueName $1, snd $1) }


TName :: {TName'}
    : typeName { (getTypeName $1, snd $1) }

Expr :: {A.Expr}
    : IfElseExpr {$1}

IfElseExpr :: {A.Expr}
    : LogicalOp '?' LogicalOp ':' IfElseExpr { (A.ACondOpExpr $ A.CondOpExpr $1 $3 $5, srcRangeOf $1 $5) }
    | LogicalOp {$1}


LogicalOp :: {A.Expr}
    : LogicalOp 'and' CmpOp  { (A.AndExpr $1 (snd $2) $3, srcRangeOf $1 $3) }
    | LogicalOp 'or' CmpOp  { (A.OrExpr $1 (snd $2) $3, srcRangeOf $1 $3) }
    | CmpOp {$1}


AnyCmpOp :: {OpName'}
    : '==' {getOp $1}
    | '!=' {getOp $1}
    | '>' {getOp $1}
    | '>=' {getOp $1}
    | '<' {getOp $1}
    | '<=' {getOp $1}


CmpOp :: {A.Expr}
    : ArithOpExp AnyCmpOp ArithOpExp  { (A.AnInfixOpExpr $ A.InfixOpExpr $2 $1 $3, srcRangeOf $1 $3) }
    | ArithOpExp {$1}


AnyArithOp :: {OpName'}
    : '+' {getOp $1}
    | '-' {getOp $1}
    | '+%' {getOp $1}
    | '-%' {getOp $1}
    | '<<' {getOp $1}
    | '>>' {getOp $1}
    | '&' {getOp $1}
    | '|' {getOp $1}
    | '~' {getOp $1}
    | '++' {getOp $1}


ArithOpExp :: {A.Expr}
    : ArithOp2Exp {$1}
    | ArithOpExp AnyArithOp ArithOp2Exp { (A.AnInfixOpExpr $ A.InfixOpExpr $2 $1 $3, srcRangeOf $1 $3) }


AnyArith2Op :: {OpName'}
    : '*' {getOp $1}
    | '*%' {getOp $1}
    | '/' {getOp $1}
    | '%' {getOp $1}


ArithOp2Exp :: {A.Expr}
    : CastExp {$1}
    | ArithOp2Exp AnyArith2Op CastExp { (A.AnInfixOpExpr $ A.InfixOpExpr $2 $1 $3, srcRangeOf $1 $3) }


CastExp :: {A.Expr}
    : CastExp 'as' TypeExpr {(A.CastExpr $1 $3, srcRangeOf $1 $3)}
    | PrefixOpExp {$1}


AnyPrefixOp :: {OpName'}
    : '-' {getOp $1}
    | '!' {getOp $1}
    | '~' {getOp $1}


PrefixOpExp :: {A.Expr}
    : AnyPrefixOp AccExp { (getPrefixOpExpr $1 $2, srcRangeOf $1 $2) }
    | '&' AccExp { (A.AddressOfExpr $2, srcRangeOf $1 $2) }
    | AccExp {$1}


AccExp :: {A.Expr}
    : AccExp AccessorPart { (A.AnAccessorExpr $ A.AccessorExpr $1 $2, srcRangeOf $1 $2) }
    | AccExp '(' List(Expr, ',') ')' { (A.AFnCallExpr $ A.FnCallExpr $1 $3, srcRangeOf $1 $4) }
    | AccExp '!' {(A.BubbleExpr $1, srcRangeOf $1 $2)}
    | AtomExp {$1}


AccessorPart :: {A.AccessorPart}
    : '.' intlit { (A.AnIndexAccessor $ fromIntegral $ getIntLit $2, srcRangeOf $2 $2) }
    | '.' VName { (A.ANameAccessor (fst $2) Nothing, srcRangeOf $2 $2) }
    | '.' VName '[' ListNE(GenericArg, ',') ']' {(A.ANameAccessor (fst $2) (Just $4), srcRangeOf $2 $5)}
    | '.' '(' Expr ')' { (A.AnIndexExprAccessor $3, srcRangeOf $2 $4) }
    | '.' '*' {(A.AStarAccessor, srcRangeOf $2 $2)}


AtomExp :: {A.Expr}
    : '(' Expr ')' { $2 }
    | '(' TupleExprContents ')' { ($2, srcRangeOf $1 $3) }
    | AtomTypeExpr '{' '}' {(A.StructInitExpr (Just $ fst $1) (snd $1) def, srcRangeOf $1 $3)}
    | AtomTypeExpr '{' StructInitFields '}' {(A.StructInitExpr (Just $ fst $1) (snd $1) $3, srcRangeOf $1 $4)}
    | '.' '{' '}' {(A.StructInitExpr Nothing (snd $1) def, srcRangeOf $1 $3)}
    | '.' '{' StructInitFields '}' {(A.StructInitExpr Nothing (snd $1) $3, srcRangeOf $1 $4)}
    | '{' ListNE(Expr, ',') '}' {(A.ArrayInitExpr $ List1 (head $2) $ tail $2, srcRangeOf $1 $3)}
    | floatlit { (A.FloatLitExpr $ getFloatLit $1, snd $1) }
    | intlit { (A.IntLitExpr $ getIntLit $1, snd $1) }
    | stringlit { (A.StringLitExpr $ getStringLit $1, snd $1) }
    | charlit { (A.CharLitExpr $ getCharLit $1, snd $1) }
    | 'true' {(A.BoolLitExpr True, snd $1)}
    | 'false' {(A.BoolLitExpr False, snd $1)}
    | 'nullptr' {A.NullPtrExpr, snd $1}
    | 'uninitialised' {(A.UninitExpr, snd $1)}

    | VName {(A.NameExpr $1 Nothing, snd $1)}
    | VName GenericArgs {(A.NameExpr $1 (Just $2), srcRangeOf $1 $2)}
    | '.' VName {(A.TypeAccessorExpr Nothing $2 Nothing, srcRangeOf $1 $2)}
    | '.' VName GenericArgs {(A.TypeAccessorExpr Nothing $2 (Just $3), srcRangeOf $1 $3)}
    | AtomTypeExpr '.' VName {(A.TypeAccessorExpr (Just $1) $3 Nothing, srcRangeOf $1 $2)}
    | AtomTypeExpr '.' VName GenericArgs {(A.TypeAccessorExpr (Just $1) $3 (Just $4), srcRangeOf $1 $2)}


StructInitFields :: {Ins.InsOrdMap VName (SrcRange, Maybe A.Expr)}
    : StructInitField { Ins.singleton (fst $1) (snd $1) }
    | StructInitFields ',' StructInitField {% maybe (parseError' ("Duplicate field name", fst $ snd $3)) pure $ Ins.tryInsert (fst $3) (snd $3) $1 }


StructInitField :: {(VName, (SrcRange, Maybe A.Expr))}
    : VName '=' Expr { ((fst $1), (snd $1, Just $3)) }
    | VName { (fst $1, (snd $1, Nothing)) }


Statement :: {A.Statement}
    : 'var' Destructure '=' Expr ';' { (A.AVarStmnt $2 $4, srcRangeOf $1 $5) }
    | 'var' VName TypeSpecifier ';' { (A.UninitVarStmnt $2 $3, srcRangeOf $1 $4) }
    | AssignmentStmnt ';' { (fst $1, srcRangeOf $1 $2) }
    | Expr ';' {% mkExprStmnt $1 }
    | IfStmnt {$1}
    | 'loop' CodeBlockStmnt {(A.LoopStmnt $2, srcRangeOf $1 $2)}
    | 'break' ';' {(A.BreakStmnt, srcRangeOf $1 $2)}
    | 'continue' ';' {(A.ContinueStmnt, srcRangeOf $1 $2)}
    | CodeBlockStmnt {$1}
    | 'return' Maybe(Expr) ';' {(A.ReturnStmnt $2, srcRangeOf $1 $3)}
    | 'yield' Expr ';' { (A.YieldStmnt $2, srcRangeOf $1 $3) }
    -- TODO Is there a way to use the 'for' keyword? Is Happy not able to look 2 tokens ahead to check for ';' or 'var'? 
    | 'foreach' Maybe('const') AccessMode Destructure 'in' Expr CodeBlockStmnt {(A.AForEachLoopStmnt $ A.ForEachLoopStmnt (isJust $2) $3 $4 $6 $7, srcRangeOf $1 $7)}
    | 'for' Maybe('const') '(' ';' Expr ';' List(AssignmentStmnt, ',') ')' CodeBlockStmnt {(A.ForLoopStmnt [] $5 $7 (isJust $2) $9, srcRangeOf $1 $9)}
    | 'for' Maybe('const') '(' 'var' List(ForVar, ',') ';' Expr ';' List(AssignmentStmnt, ',') ')' CodeBlockStmnt {(A.ForLoopStmnt $5 $7 $9 (isJust $2) $11, srcRangeOf $1 $11)}
    | RequireStmnt ';' {(A.ARequireStmnt $ fst $1, srcRangeOf $1 $2)}
    | 'match' AccessMode Expr '{' ManyNe(MatchBranch) '}' {(A.MatchStmnt $2 $3 (List1 (head $5) $ tail $5), srcRangeOf $1 $6)}
    | 'unsafe' CodeBlockStmnt {(A.UnsafeStmnt $2, srcRangeOf $1 $2)}
    | 'throw' Expr ';' {(A.ThrowStmnt $2, srcRangeOf $1 $2)}
    | 'try' CodeBlockStmnt 'catch' VNameOrUnderscore CodeBlockStmnt {(A.TryCatchStmnt $2 $4 $5, srcRangeOf $1 $5)}
    | 'borrow' Maybe('ref') VName Maybe(TypeSpecifier) '=' Expr ';' {(A.BorrowStatement (if isJust $2 then Exclusive else Shared) $3 $4 $6, srcRangeOf $1 $7)}


VNameOrUnderscore :: {(Maybe VName, SrcRange)}
    : '_' {(Nothing, snd $1)}
    | VName {first Just $1}


MatchBranch :: {A.MatchBranch}
    : Pattern CodeBlockStmnt {A.MatchBranch $1 $2}


Pattern :: {A.Pattern}
    : '_' {(A.PatternAny, snd $1)}
    | VName {(A.PatternName $1, snd $1)}
    | '.' VName {(A.PatternDataCons0 (fst $2), srcRangeOf $1 $2)}
    | '.' VName '(' Pattern ')' {(A.PatternDataCons1 $2 $4, srcRangeOf $1 $5)}


ForVar :: {(A.Destructure, A.Expr)}
    : Destructure '=' Expr {($1, $3)}


AssignmentStmnt :: {A.Statement}
    : AccExp '=' Expr { (A.AnAssignmentStmnt $ A.AssignmentStmnt (Just $ fst $1) (snd $1) $3, srcRangeOf $1 $3) }
    | '_' '=' Expr { (A.AnAssignmentStmnt $ A.AssignmentStmnt Nothing (snd $1) $3, srcRangeOf $1 $3) }
    | AccExp AnyAsOp Expr {(A.CompoundAssignmentOpStmnt $ A.InfixOpExpr $2 $1 $3, srcRangeOf $1 $3)}


AnyAsOp :: {OpName'}
    : '+=' {getOp $1}
    | '-=' {getOp $1}
    | '+%=' {getOp $1}
    | '-%=' {getOp $1}
    | '<<=' {getOp $1}
    | '>>=' {getOp $1}
    | '&=' {getOp $1}
    | '|=' {getOp $1}
    | '~=' {getOp $1}
    | '++=' {getOp $1}
    | '*=' {getOp $1}
    | '*%=' {getOp $1}
    | '/=' {getOp $1}
    | '%=' {getOp $1}

TypeSpecifier :: {A.TypeExpr}
    : ':' TypeExpr {$2}


Destructure :: {A.Destructure}
    : VName Maybe(TypeSpecifier) {(A.NameDes $1 $2, snd $1)}
    | '_' Maybe(TypeSpecifier) {(A.IgnoreDes $2, snd $1)}
    | '(' TupleDesInner ')' {(A.TupleDes $2, srcRangeOf $1 $3)}
    | '{' ListNE(Destructure, ',') '}' {(A.ArrayDes $ List1 (head $2) $ tail $2, srcRangeOf $1 $3)}
    | '.' '{' StructDesInner '}' {(A.StructDes $3, srcRangeOf $1 $4)}


TupleDesInner :: {List2 A.Destructure}
    : Destructure ',' ListNE(Destructure, ',') { List2 $1 (head $3) $ tail $3 }


StructDesInner :: {Ins.InsOrdMap VName (SrcRange, A.Destructure)}
    : StructDesField { Ins.singleton (fst $1) (snd $1) }
    | StructDesInner ',' StructDesField {% maybe (parseError' ("Duplicate field name", fst $ snd $3)) pure $ Ins.tryInsert (fst $3) (snd $3) $1 }


StructDesField :: {(VName, (SrcRange, A.Destructure))}
    : VName ':' Destructure { ((fst $1), (snd $1, $3)) }
    | VName Maybe(TypeSpecifier) { (fst $1, (snd $1, (A.NameDes $1 $2, snd $1))) }


CodeBlockStmnt :: {A.Statement}
    : '{' ManyNe(Statement) '}' { (A.CodeBlockStmnt $2, srcRangeOf $1 $3) }
    | '{' '}' { (A.CodeBlockStmnt def, srcRangeOf $1 $2) }


IfStmnt :: {A.Statement}
    : 'if' Maybe('const') Expr CodeBlockStmnt {(A.AnIfElseStmnt $ A.IfElseStmnt (isJust $2) $3 $4 Nothing, srcRangeOf $1 $4)}
    | 'if' Maybe('const') Expr CodeBlockStmnt ElseOrElseIf {(A.AnIfElseStmnt $ A.IfElseStmnt (isJust $2) $3 $4 (Just $5), srcRangeOf $1 $5)}


ElseOrElseIf :: {A.Statement}
    : 'else' IfStmnt {(A.CodeBlockStmnt [$2], srcRangeOf $1 $2)}
    | 'else' CodeBlockStmnt {(fst $2, srcRangeOf $1 $2)}


TupleExprContents :: {A.Expr'}
    : Expr ',' ListNE(Expr, ',') { A.MkTupleExpr $ List2 $1 (head $3) $ tail $3 }


-- Macros

List(x, sep)
    : ListRev(x, sep) { reverse $1 }

ListRev(x, sep)
    : {[]}
    | ListNERev(x, sep) {$1}

ListNE(x, sep)
    : ListNERev(x, sep) { reverse $1 }

ListNERev(x, sep)
    : x {[$1]}
    | ListNERev(x, sep) sep x { $3 : $1 }

ManyRev(e)
    : {[]}
    | e {[$1]}
    | ManyRev(e) e { $2 : $1 }

Many(e)
    : ManyRev(e) { reverse $1 }

ManyNeRev(e)
    : e {[$1]}
    | ManyNeRev(e) e { $2 : $1 }

ManyNe(e)
    : ManyNeRev(e) { reverse $1 }

Maybe(e)
    : {Nothing}
    | e {Just $1}
