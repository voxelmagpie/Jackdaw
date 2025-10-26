-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.Expr where

import AccessMode
import Ast qualified as A
import Control.Monad (filterM, foldM, forM, forM_, unless, when)
import Data.Bits (Bits (complement, xor), (.&.), (.|.))
import Data.Char (ord)
import Data.Either (isRight)
import Data.HashMap.Strict qualified as HM
import Data.List (elemIndex, find, uncons)
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, maybeToList)
import Data.Text qualified as T
import HashMultiMap qualified as HMM
import Hir qualified
import InsOrdMap qualified as Ins
import Names
import Prelude2
import Primitives
import SrcLoc (SrcRange, srcRangeOf)
import Tc.Builtins
import Tc.Casts
import Tc.Ctx
import Tc.Error (ErrorSeverity (SevError, SevWarning), MonadTcError)
import Tc.Fmt
import Tc.Hir
import Tc.MkCtx
import Tc.Names
import Tc.State
import Tc.Tc
import Tc.TcErr
import Tc.TcIr qualified as I
import Tc.TypeAttribs (typeIsUnsafe)

getInt :: (MonadTcError m) => Ctx -> SrcRange -> Integer -> m I.Constant
getInt ctx sr x
  | x >= -2147483648 && x <= 2147483647 = pure (I.ConstInt x, i32)
  | x >= -9223372036854775808 && x <= 9223372036854775807 = pure (I.ConstInt x, i64)
  | x >= 0 && x <= 18446744073709551615 = pure (I.ConstInt x, u64)
  | otherwise = throw ctx.et sr "Int out of range"

getConstLitExpr :: (MonadTc m) => Ctx -> TypeHint -> A.Expr -> m I.Constant
getConstLitExpr ctx hint (e, sr) = case e of
  A.IntLitExpr x -> do
    c <- getInt ctx sr x
    case hint of
      TypeHint h -> iCastConstant h c
      _ -> pure c
  A.FloatLitExpr x -> do
    let isF32 = hint == TypeHint f32
    pure (I.ConstFloatOrDouble x, if isF32 then f32 else f64)
  A.BoolLitExpr x -> pure (I.ConstBool x, bool)
  A.StringLitExpr str -> makeConstStringLit ctx hint str
  A.CharLitExpr c -> pure (I.ConstInt $ fromIntegral $ ord c, u8)
  A.NullPtrExpr -> do
    unless ctx.inUnsafeCode $ addError SevError ctx.et sr "Pointers are not valid in safe code"
    case hint of
      TypeHint t@(I.PtrType _) ->
        pure (I.ConstNullPtr, t)
      TypeHint t@(I.AFnType x)
        | x.isNullable ->
            pure (I.ConstNullPtr, t)
      _ -> do
        addError SevError ctx.et sr "Unable to deduce pointer type"
        pure (I.ConstNullPtr, I.PtrType Nothing)
  A.NameExpr name gArgsMaybe -> do
    case findLocalVarByName ctx (fst name) of
      Just v -> case v.uidOrVal of
        Right c -> pure (c, v.typ)
        _ -> throw ctx.et sr "Not a constant value"
      _ -> do
        fqnOrConst <- lookupVName ctx name
        case fqnOrConst of
          Left (ctx', vFqn, astDef) -> do
            let astGArgs = fromMaybe def gArgsMaybe
            gArgs <- forM astGArgs $ getGenArg ctx

            (id, t, _) <- visitVDef ctx ctx' gArgs sr (vFqn, astDef) ctx.inUnsafeCode
            vDef <- getVDef id
            let c = case vDef of
                  I.AConstDef c' ->
                    case c'.value of
                      Just x -> x
                      _ -> I.ConstExtern id
                  I.AFnDef _ -> do
                    I.ConstFnPtr id
            pure (c, t)
          Right c ->
            pure c
  A.StructInitExpr astTypeExprMaybe sr' astFields -> do
    -- Get struct type
    (structType, fieldTypes) <- case (astTypeExprMaybe, hint) of
      (Just astTypeExpr, _) -> do
        -- Explicit struct type
        t <- getType ctx (astTypeExpr, sr')
        fs <- getStructFields ctx sr' t
        pure (t, fs)
      (Nothing, TypeHint t) -> do
        -- Infer struct type
        fs <- getStructFields ctx sr' t
        pure (t, fs)
      (Nothing, _) -> throw ctx.et sr' "Unable to deduce struct type"

    -- Get field values
    fieldsList <- forM (toList astFields) $ \(name, (sr'', astExMaybe)) -> do
      -- If no value is given then look for a variable/constant with the same name as the field
      let astEx = fromMaybe (A.NameExpr (name, sr) Nothing, sr) astExMaybe
      (expectedType, attribs) <- case Ins.lookup name fieldTypes of
        Just x -> pure x
        _ -> throw ctx.et sr'' "No such field"
      when (Attribute "Unsafe" `elem` attribs) $ addError SevError ctx.et sr "Unsafe types not valid for constants"
      c@(_, actualType) <- getConstLitExpr ctx (TypeHint expectedType) astEx >>= iCastConstant expectedType
      unless (actualType == expectedType) $ do
        (act, ex) <- format2Types actualType expectedType
        addError SevError ctx.et sr $ T.concat ["Wrong type for struct field ", un name, "\nExpected ", ex, ", got ", act]
      pure (name, c)

    let namesList = Ins.keys astFields

    -- Check all fields have a value
    exprs <- forM namesList $ \n ->
      case find (\(n', _) -> n == n') fieldsList of
        Nothing -> throw ctx.et sr $ "Missing field: " <> un n
        Just (_, e') -> pure e'

    pure (I.ConstStructOrTuple exprs, structType)
  A.MkTupleExpr es -> do
    es' <- case hint of
      TypeHint (I.TupleType hs) -> do
        forM (zipList2 es hs) $ \(e', t) ->
          getConstLitExpr ctx (TypeHint t) e' >>= iCastConstant t
      _ ->
        forM es $ getConstLitExpr ctx NoHint
    pure (I.ConstStructOrTuple $ toList es', I.TupleType $ snd <$> es')
  A.ArrayInitExpr astExprs@(List1 astExpr0 astExprs') -> do
    let hint' = case hint of TypeHint (I.ArrayType x _) -> TypeHint x; _ -> NoHint
    (c0, elementType) <- getConstLitExpr ctx hint' astExpr0
    cs' <- forM astExprs' $ \e' -> do
      getConstLitExpr ctx (TypeHint elementType) e' >>= iCastConstant elementType <&> fst
    let cs = List1 c0 cs'

    pure (I.ConstArray elementType cs, I.ArrayType elementType $ fromIntegral $ length astExprs)
  A.APrefixOpExpr A.PrefixOpExpr {..} -> do
    (c, t) <- getConstLitExpr ctx NoHint arg
    case (c, un $ fst op) of
      (I.ConstBool b, "!") -> pure (I.ConstBool $ not b, t)
      (I.ConstInt i, "-") -> getInt ctx sr (-i)
      (I.ConstInt i, "~") -> getInt ctx sr (complement i)
      (I.ConstFloatOrDouble i, "-") -> pure (I.ConstFloatOrDouble i', t)
        where
          i' = if "-" `T.isPrefixOf` i then T.tail i else T.cons '-' i
      _ -> throw ctx.et sr "Unknown constant operator"
  A.AnInfixOpExpr astExpr -> do
    (lhs, lhsType) <- getConstLitExpr ctx NoHint astExpr.lhs
    (rhs, rhsType) <- getConstLitExpr ctx NoHint astExpr.rhs
    case (un $ fst astExpr.op, lhs, rhs) of
      ("+", I.ConstInt x, I.ConstInt y) -> getInt ctx sr (x + y)
      ("*", I.ConstInt x, I.ConstInt y) -> getInt ctx sr (x * y)
      ("-", I.ConstInt x, I.ConstInt y) -> getInt ctx sr (x - y)
      ("/", I.ConstInt x, I.ConstInt y) -> do
        if y == 0
          then
            throw ctx.et sr "Division by 0"
          else
            getInt ctx sr (x `div` y)
      ("%", I.ConstInt x, I.ConstInt y) -> do
        if y == 0
          then
            throw ctx.et sr "Division by 0"
          else
            getInt ctx sr (x `rem` y)
      ("==", I.ConstInt x, I.ConstInt y) ->
        pure (I.ConstBool $ x == y, bool)
      ("!=", I.ConstInt x, I.ConstInt y) ->
        pure (I.ConstBool $ x /= y, bool)
      (">", I.ConstInt x, I.ConstInt y) ->
        pure (I.ConstBool $ x > y, bool)
      ("<", I.ConstInt x, I.ConstInt y) ->
        pure (I.ConstBool $ x < y, bool)
      (">=", I.ConstInt x, I.ConstInt y) ->
        pure (I.ConstBool $ x >= y, bool)
      ("<=", I.ConstInt x, I.ConstInt y) ->
        pure (I.ConstBool $ x <= y, bool)
      ("==", I.ConstBool x, I.ConstBool y) ->
        pure (I.ConstBool $ x == y, bool)
      ("==", I.ConstEnum x, I.ConstEnum y)
        | lhsType == rhsType ->
            pure (I.ConstBool $ x == y, bool)
      ("!=", I.ConstBool x, I.ConstBool y) ->
        pure (I.ConstBool $ x /= y, bool)
      ("!=", I.ConstEnum x, I.ConstEnum y)
        | lhsType == rhsType ->
            pure (I.ConstBool $ x /= y, bool)
      ("|", I.ConstInt x, I.ConstInt y) -> getInt ctx sr (x .|. y)
      ("&", I.ConstInt x, I.ConstInt y) -> getInt ctx sr (x .&. y)
      ("~", I.ConstInt x, I.ConstInt y) -> getInt ctx sr (x `xor` y)
      ("++", I.ConstStructOrTuple lhsFields, I.ConstStructOrTuple rhsFields) -> do
        unless (lhsType == rhsType) $ throw ctx.et sr "Mismatched types for ++"
        -- Extract the LHS data
        ((lhsElPtr, listElPtrType), listType, isString) <- case lhsType of
          I.ANamedType id ->
            getTDef id >>= \case
              I.AStructDef c -> case un c.fqn of
                "@stlib/list:List" ->
                  pure (lhsFields !! 0, lhsType, False)
                "@stlib/string:String" ->
                  -- Extract the List[U8] from the String
                  let x = case fst (lhsFields !! 0) of I.ConstStructOrTuple ys -> ys !! 0; _ -> undefined
                   in pure (x, snd (lhsFields !! 0), True)
                "@stlib/os_string:OsString" ->
                  let x = case fst (lhsFields !! 0) of I.ConstStructOrTuple ys -> ys !! 0; _ -> undefined
                   in pure (x, snd (lhsFields !! 0), True)
                _ -> throw ctx.et sr "Invalid ++ const operator"
              _ -> throw ctx.et sr "Invalid ++ const operator"
          _ -> throw ctx.et sr "Invalid ++ const operator"

        let (elType, lhsArray) = case lhsElPtr of I.ConstAddrOfArray0 (I.ConstArray el arr, _) -> (el, arr); _ -> undefined

        -- Extract the RHS data
        -- \*Array[U8, *]
        let (rhsElPtr, _) =
              if not isString
                then rhsFields !! 0
                else case fst (rhsFields !! 0) of I.ConstStructOrTuple ys -> ys !! 0; _ -> undefined

        -- Array[U8, *]
        let rhsArray = case rhsElPtr of I.ConstAddrOfArray0 (I.ConstArray _ arr, _) -> arr; _ -> undefined

        -- Create the new list/string
        let newArray =
              if isString
                then
                  -- Drop the null terminator then merge
                  must $ listToList1 $ take (length lhsArray - 1) (toList lhsArray) <> toList rhsArray
                else
                  lhsArray <> rhsArray

        let newArray' = (I.ConstArray elType newArray, I.ArrayType elType $ fromIntegral $ length newArray)
        let list =
              ( I.ConstStructOrTuple
                  [ (I.ConstAddrOfArray0 newArray', listElPtrType),
                    (I.ConstInt $ fromIntegral $ length newArray, i64),
                    (I.ConstInt 0, i64)
                  ],
                listType
              )

        pure (if isString then I.ConstStructOrTuple [list] else fst list, lhsType)
      _ -> throw ctx.et sr "Invalid/unknown constant operator"
  A.TypeAccessorExpr astTypeExprMaybe name gArgsMaybe -> do
    getTypeAccessExprConst ctx hint sr astTypeExprMaybe name gArgsMaybe
  A.AnAccessorExpr x -> do
    (lhs, lhsType) <- getConstLitExpr ctx NoHint x.expr
    let invalid = "Accessor not valid for type"
    let rangeErr = "Index out of range"
    let sr' = snd x.accessor
    case fst x.accessor of
      A.AnIndexAccessor i -> do
        -- Limit to range of Haskell Int
        unless (i >= -536870912 && i <= 536870911) $ throw ctx.et sr' rangeErr
        case lhs of
          I.ConstStructOrTuple xs -> case lhsType of
            I.TupleType _ -> case xs !? fromIntegral i of Just y -> pure y; _ -> throw ctx.et sr' rangeErr
            _ -> throw ctx.et sr' invalid
          _ -> throw ctx.et sr' invalid
      A.AnIndexExprAccessor idxExpr -> do
        c <- getConstLitExpr ctx NoHint idxExpr
        i <- case fst c of I.ConstInt i -> pure i; _ -> throw ctx.et sr' "Expected integer"
        unless (i >= -536870912 && i <= 536870911) $ throw ctx.et sr' rangeErr
        case lhs of
          I.ConstArray elType xs ->
            case xs !? fromIntegral i of Just y -> pure (y, elType); _ -> throw ctx.et sr' rangeErr
          I.ConstAddrOfArray0 (I.ConstArray elType xs, _) ->
            case xs !? fromIntegral i of Just y -> pure (y, elType); _ -> throw ctx.et sr' rangeErr
          _ -> throw ctx.et sr' invalid
      A.AStarAccessor ->
        case lhs of I.ConstAddrOf c -> pure c; _ -> throw ctx.et sr' invalid
      A.ANameAccessor name gArgs -> do
        unless (null gArgs) $ throw ctx.et sr' "Cannot call functions at compile-time"
        case (lhs, lhsType) of
          (I.ConstStructOrTuple xs, I.ANamedType tDefId) -> do
            s <- checkTDef2 tDefId >>= \case I.AStructDef2 y -> pure y; _ -> throw ctx.et sr' invalid
            case Ins.lookupWithIndex name s.fields of
              Just (_, fieldIdx) -> pure $ xs !! fieldIdx
              _ -> throw ctx.et sr' $ "No such field: " <> un name
          _ -> throw ctx.et sr invalid
  A.CastExpr astExpr astTypeExpr -> do
    to <- getType ctx astTypeExpr
    (c, from) <- getConstLitExpr ctx (TypeHint to) astExpr >>= iCastConstant to
    if from == to
      then pure (c, from)
      else case (c, from, to) of
        (I.ConstInt x, _, I.PtrType _) -> pure (I.ConstInt x, to)
        (I.ConstInt x, _, I.AFnType _) -> pure (I.ConstInt x, to)
        (I.ConstInt x, _, I.AnAccessorType _) -> pure (I.ConstInt x, to)
        (I.ConstInt x, _, I.AnIteratorType _) -> pure (I.ConstInt x, to)
        (I.ConstInt x, _, I.AnAccessorIteratorType _) -> pure (I.ConstInt x, to)
        (I.ConstInt x, _, I.NumPrimType (AnIntT i)) | i.size == Int64 -> pure (I.ConstInt x, to)
        _ -> throw ctx.et sr "Unsupported constant cast"
  A.AndExpr lhsExpr _ rhsExpr -> do
    (lhsExpr', lhsType) <- getConstLitExpr ctx NoHint lhsExpr
    unless (lhsType == bool) $ addError SevError ctx.et lhsExpr "Expected boolean"

    let l = case lhsExpr' of I.ConstBool x -> x; _ -> undefined
    if not l
      then
        -- RHS is not checked as 'and' is short-circuited
        pure (I.ConstBool False, bool)
      else do
        (rhsExpr', _) <- getConstLitExpr ctx NoHint rhsExpr
        r <- case rhsExpr' of I.ConstBool x -> pure x; _ -> throw ctx.et rhsExpr "Expected boolean"
        pure (I.ConstBool $ l && r, bool)
  A.OrExpr lhsExpr _ rhsExpr -> do
    (lhsExpr', lhsType) <- getConstLitExpr ctx NoHint lhsExpr
    unless (lhsType == bool) $ addError SevError ctx.et lhsExpr "Expected boolean"
    let l = case lhsExpr' of I.ConstBool x -> x; _ -> undefined

    if l
      then
        pure (I.ConstBool True, bool)
      else do
        (rhsExpr', _) <- getConstLitExpr ctx NoHint rhsExpr
        r <- case rhsExpr' of I.ConstBool x -> pure x; _ -> throw ctx.et rhsExpr "Expected boolean"
        pure (I.ConstBool $ l || r, bool)
  _ -> throw ctx.et sr "Only constant values are valid here"

getExpr :: (MonadTc m) => Ctx -> TypeHint -> A.Expr -> m I.Expr
getExpr ctx hint (e, sr) = case e of
  A.IntLitExpr _ -> getConstLitExpr ctx hint (e, sr) <&> \(c, t) -> (I.LoadConstantExpr c, t, sr)
  A.FloatLitExpr _ -> getConstLitExpr ctx hint (e, sr) <&> \(c, t) -> (I.LoadConstantExpr c, t, sr)
  A.BoolLitExpr _ -> getConstLitExpr ctx hint (e, sr) <&> \(c, t) -> (I.LoadConstantExpr c, t, sr)
  A.StringLitExpr _ -> getConstLitExpr ctx hint (e, sr) <&> \(c, t) -> (I.LoadConstantExpr c, t, sr)
  A.CharLitExpr _ -> getConstLitExpr ctx hint (e, sr) <&> \(c, t) -> (I.LoadConstantExpr c, t, sr)
  A.NullPtrExpr -> case hint of
    TypeHint t@(I.PtrType _) ->
      pure (I.LoadConstantExpr I.ConstNullPtr, t, sr)
    TypeHint t@(I.AFnType x)
      | x.isNullable ->
          pure (I.LoadConstantExpr I.ConstNullPtr, t, sr)
    _ -> do
      addError SevError ctx.et sr "Unable to deduce pointer type"
      pure (I.LoadConstantExpr I.ConstNullPtr, I.PtrType Nothing, sr)
  A.TypeAccessorExpr x y z -> getTypeAccessExpr ctx hint sr x y z
  A.NameExpr x y -> getNameExpr ctx sr x y
  A.MkTupleExpr x -> getMkTupleExpr ctx hint sr x
  A.StructInitExpr typeExpr sr' f -> getStructInitExpr ctx hint sr typeExpr sr' f
  A.ArrayInitExpr es -> getArrayInitExpr ctx hint sr es
  A.AnAccessorExpr x -> getAccessorExpr ctx sr x
  A.AFnCallExpr x -> do
    getFnCallExpr ctx hint sr x False >>= \case
      Left e' -> pure e'
      _ -> throw ctx.et sr "Function returns void"
  A.AnInfixOpExpr x -> getOpExpr ctx hint sr x.op x.lhs $ Just x.rhs
  A.APrefixOpExpr x -> getOpExpr ctx hint sr x.op x.arg Nothing
  A.AddressOfExpr x -> do
    e'@(e'', t, _) <- getExpr ctx NoHint x
    let t' = case e'' of
          I.LoadConstantExpr _ -> I.ConstPtrType t
          _ -> I.PtrType $ Just t
    pure (I.AddressOfExpr e', t', sr)
  A.ACondOpExpr x -> getCondOpExpr ctx hint sr x
  A.CastExpr e' t -> getCastExpr ctx sr e' t
  A.AndExpr lhsAstExpr _ rhsAstExpr -> do
    lhs@(_, t, _) <- getExpr ctx (TypeHint bool) lhsAstExpr >>= iCast bool
    unless (t == bool) $ addError SevError ctx.et lhsAstExpr "Expected boolean for lhs of 'and' operator"
    rhs@(_, t', _) <- getExpr ctx (TypeHint bool) rhsAstExpr >>= iCast bool
    unless (t' == bool) $ addError SevError ctx.et lhsAstExpr "Expected boolean for rhs of 'and' operator"
    pure (I.AndExpr lhs rhs, bool, sr)
  A.OrExpr lhsAstExpr _ rhsAstExpr -> do
    lhs@(_, t, _) <- getExpr ctx (TypeHint bool) lhsAstExpr >>= iCast bool
    unless (t == bool) $ addError SevError ctx.et lhsAstExpr "Expected boolean for lhs of 'or' operator"
    rhs@(_, t', _) <- getExpr ctx (TypeHint bool) rhsAstExpr >>= iCast bool
    unless (t' == bool) $ addError SevError ctx.et lhsAstExpr "Expected boolean for rhs of 'or' operator"
    pure (I.OrExpr lhs rhs, bool, sr)
  A.UninitExpr -> case hint of
    TypeHint t -> do
      unless ctx.inUnsafeCode $ addError SevError ctx.et sr "Uninitialised data cannot be used in a safe context"
      pure (I.UninitExpr, t, sr)
    _ -> throw ctx.et sr "Unable to deduce type"
  A.BubbleExpr e' -> getBubbleExpr ctx hint sr e'

getCastExpr :: (MonadTc m) => Ctx -> SrcRange -> A.Expr -> A.TypeExpr -> m I.Expr
getCastExpr ctx sr astExpr astTypeExpr = do
  to <- getType ctx astTypeExpr
  e@(_, from, _) <- getExpr ctx (TypeHint to) astExpr
  if from == to
    then pure e
    else case (from, to) of
      -- Enum -> Int
      (I.ANamedType id, I.NumPrimType (AnIntT _)) ->
        checkTDef2 id >>= \case
          I.AnEnumDef2 ed -> if isValid then pure castExpr else throw ctx.et sr "Invalid enum tag to int cast"
            where
              -- Check tag fits in 'to' type
              -- TODO Do this by comparing the length of ed.fields to the max value of the int types
              isValid
                | not ed.e.canBeCastedToInt = False
                | ed.tagType == u8 = to /= i8
                | ed.tagType == u16 = to `notElem` [i8, u8, i16]
                | ed.tagType == u32 = to `notElem` [i8, u8, i16, u16, i32]
                | otherwise = undefined
              castExpr = (castExpr', to, sr)
              -- Cast int type
              castExpr' =
                if ed.tagType == to
                  then
                    I.ActiveDataConsExpr e
                  else
                    I.BitCast (I.ActiveDataConsExpr e, ed.tagType, sr)
          _ -> throw ctx.et sr "Invalid cast"
      _ -> do
        valid <- bitCastIsValid ctx sr from to
        unless valid (throw ctx.et sr "Invalid cast")
        pure (I.BitCast e, to, sr)

getCondOpExpr :: (MonadTc m) => Ctx -> TypeHint -> SrcRange -> A.CondOpExpr -> m I.Expr
getCondOpExpr ctx hint sr astExpr = do
  condExpr <- getExpr ctx (TypeHint bool) astExpr.condExpr >>= iCast bool
  thenExpr@(_, t, _) <- getExpr ctx hint astExpr.thenExpr
  elseExpr@(_, t2, _) <- getExpr ctx (TypeHint t) astExpr.elseExpr >>= iCast t

  unless (t == t2) $ addError SevError ctx.et sr "Types on either side of conditional operator do not match"

  pure (I.ACondOpExpr $ I.CondOpExpr {condExpr = condExpr, thenExpr = thenExpr, elseExpr = elseExpr}, t, sr)

getMemberFnCallExpr ::
  (MonadTc m) =>
  Ctx ->
  TypeHint ->
  SrcRange ->
  A.Expr ->
  (Either VName OpName, SrcRange) ->
  [A.GenericArg] ->
  [A.Expr] ->
  Bool ->
  m (Either I.Expr I.Statement)
getMemberFnCallExpr ctx _hint sr lhsAstExpr (vOrOpName, nameSr) fnAstGArgs argsExprs expectIterator = do
  lhs@(_, lhsType, _) <- getExpr ctx NoHint lhsAstExpr
  let getOnlyGArg = case argsExprs of [x] -> pure x; _ -> throw ctx.et sr "Wrong number of arguments"
  resultMaybe <- case (lhsType, null fnAstGArgs) of
    -- Member functions for types without definitions written in jackdaw code
    (I.AFnType _, True) -> do
      case () of
        _ | vOrOpName == Left (VName "eq") || vOrOpName == Right (OpName "==") -> do
          argAstExpr <- getOnlyGArg
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError SevError ctx.et argSr "Incompatible types"
          pure $ Just $ Left (I.PtrEqExpr lhs argExpr, bool, sr)
        _ | vOrOpName == Left (VName "neq") || vOrOpName == Right (OpName "!=") -> do
          argAstExpr <- getOnlyGArg
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError SevError ctx.et argSr "Incompatible types"
          pure $ Just $ Left (I.PtrNEqExpr lhs argExpr, bool, sr)
        _ -> pure Nothing
    (I.PtrType pointeeType, True) -> do
      case () of
        _ | vOrOpName == Left (VName "add") || vOrOpName == Right (OpName "+") -> do
          argAstExpr <- getOnlyGArg
          when (isNothing pointeeType) $ throw ctx.et sr "Operation not valid on void pointers"
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint i64) argAstExpr >>= iCast i64
          unless (argType == i64) $ addError SevError ctx.et argSr "Pointer addition expects an I64"
          pure $ Just $ Left (I.APtrAddExpr $ I.PtrAddExpr {expr = lhs, index = argExpr}, lhsType, sr)
        _ | vOrOpName == Left (VName "sub") || vOrOpName == Right (OpName "-") -> do
          argAstExpr <- getOnlyGArg
          when (isNothing pointeeType) $ throw ctx.et sr "Operation not valid on void pointers"
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint i64) argAstExpr >>= iCast i64
          unless (argType == i64) $ addError SevError ctx.et argSr "Pointer subtraction expects an I64"
          pure $ Just $ Left (I.APtrSubExpr $ I.PtrSubExpr {expr = lhs, index = argExpr}, lhsType, sr)
        _ | vOrOpName == Left (VName "eq") || vOrOpName == Right (OpName "==") -> do
          argAstExpr <- getOnlyGArg
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError SevError ctx.et argSr "Incompatible types"
          pure $ Just $ Left (I.PtrEqExpr lhs argExpr, bool, sr)
        _ | vOrOpName == Left (VName "neq") || vOrOpName == Right (OpName "!=") -> do
          argAstExpr <- getOnlyGArg
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError SevError ctx.et argSr "Incompatible types"
          pure $ Just $ Left (I.PtrNEqExpr lhs argExpr, bool, sr)
        _ -> pure Nothing
    (I.ConstPtrType _, True) -> do
      case () of
        _ | vOrOpName == Left (VName "eq") || vOrOpName == Right (OpName "==") -> do
          argAstExpr <- getOnlyGArg
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError SevError ctx.et argSr "Incompatible types"
          pure $ Just $ Left (I.PtrEqExpr lhs argExpr, bool, sr)
        _ | vOrOpName == Left (VName "neq") || vOrOpName == Right (OpName "!=") -> do
          argAstExpr <- getOnlyGArg
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError SevError ctx.et argSr "Incompatible types"
          pure $ Just $ Left (I.PtrNEqExpr lhs argExpr, bool, sr)
        _ -> pure Nothing
    _ -> pure Nothing

  case resultMaybe of
    Just x -> pure x
    _ -> do
      -- Get list of member functions
      (memberFns, memberFnOps, lhsTFqn) <-
        getVDefsInType ctx.tcIn lhsType >>= \case
          Just (x, y) -> pure (x.defs, x.operators, y)
          _ -> pure (def, def, undefined)

      let visitVDef' d = do
            let c = A.vDefCommon d
            let fqn = VFqn $ un lhsTFqn <> "." <> un (fst c.name)

            typeCtx <- getTypeCtx ctx sr lhsType <&> must -- Type has value defs and therefore has a context
            fnGArgs <- forM fnAstGArgs $ getGenArg ctx

            unless (length fnAstGArgs == length c.genericParams)
              $ throw ctx.et sr "Wrong number of generic arguments"

            visitVDef ctx typeCtx fnGArgs sr (fqn, d) ctx.inUnsafeCode

      -- Find the function
      (fnDefMaybe, vOrOpName') <- case vOrOpName of
        Left n -> pure (maybeToList $ HM.lookup n memberFns, un n)
        -- Potential operator functions are filtered by length to allow
        -- overloading between prefix and unary operators
        -- TODO Filter by second arg type for operators
        Right n -> do
          x <- flip filterM (HMM.lookup n memberFnOps) $ \d -> do
            (_, t, _) <- visitVDef' d
            let paramsCount = case t of
                  I.AFnType f -> length f.params
                  I.AnAccessorType f -> length f.params
                  I.AnIteratorType f -> length f.params
                  I.AnAccessorIteratorType f -> length f.params
                  _ -> 0
            pure $ paramsCount == length argsExprs + 1
          pure (x, un n)

      fnDefOrAutoGenFn <- case fnDefMaybe of
        [] | null fnAstGArgs -> do
          -- Auto-generatable functions (compiler generates calls to the implementations in the stlib)
          case () of
            _ | vOrOpName == Left (VName "eq") || vOrOpName == Right (OpName "==") -> do
              let ctx' = mkFileCtx (Namespace "@stlib/stlib") ctx.tcIn.stLibAst ctx.tcIn
              pure $ Right (ctx', "@stlib/stlib:equal", ctx.tcIn.equalFn)
            _ | vOrOpName == Left (VName "neq") || vOrOpName == Right (OpName "!=") -> do
              let ctx' = mkFileCtx (Namespace "@stlib/stlib") ctx.tcIn.stLibAst ctx.tcIn
              pure $ Right (ctx', "@stlib/stlib:notEqual", ctx.tcIn.notEqualFn)
            _ | vOrOpName == Left (VName "clone") -> do
              let ctx' = mkFileCtx (Namespace "@stlib/stlib") ctx.tcIn.stLibAst ctx.tcIn
              pure $ Right (ctx', "@stlib/stlib:clone", ctx.tcIn.cloneFn)
            _ | vOrOpName == Left (VName "hash") -> do
              let ctx' = mkFileCtx (Namespace "@stlib/hash") ctx.tcIn.hashAst ctx.tcIn
              pure $ Right (ctx', "@stlib/hash:hash", ctx.tcIn.hashFn)
            _ | vOrOpName == Left (VName "addToHash") -> do
              let ctx' = mkFileCtx (Namespace "@stlib/hash") ctx.tcIn.hashAst ctx.tcIn
              pure $ Right (ctx', "@stlib/hash:addToHash", ctx.tcIn.addToHashFn)
            _ | vOrOpName == Left (VName "toString") -> do
              let ctx' = mkFileCtx (Namespace "@stlib/to_string") ctx.tcIn.toStringAst ctx.tcIn
              pure $ Right (ctx', "@stlib/to_string:toString", ctx.tcIn.toStringFn)
            _ | vOrOpName == Left (VName "addToString") -> do
              let ctx' = mkFileCtx (Namespace "@stlib/addToString") ctx.tcIn.toStringAst ctx.tcIn
              pure $ Right (ctx', "@stlib/to_string:addToString", ctx.tcIn.addToStringFn)
            _ -> throw ctx.et nameSr $ "No such member function: " <> vOrOpName'
        [] -> throw ctx.et nameSr $ "No such member function: " <> vOrOpName'
        [x] -> pure $ Left x
        _ -> throw ctx.et nameSr $ "Operator is ambiguous: " <> vOrOpName'

      case fnDefOrAutoGenFn of
        Left d -> do
          (id, t, vDef) <- visitVDef' d

          let isAccessor = case t of
                I.AnAccessorType _ -> True
                I.AnAccessorIteratorType _ -> True
                _ -> False

          let callee = case vDef of
                I.AConstDef cd -> (I.LoadConstantExpr $ case cd.value of Just x -> x; _ -> I.ConstExtern id, t, sr)
                _ -> (I.LoadConstantExpr $ I.ConstFnPtr id, t, sr)

          getCallExpr ctx nameSr sr callee (Just lhs) argsExprs expectIterator <&> \(ce, r) -> case (r, isAccessor) of
            (Just retType, _) -> Left (I.AFnCallExpr ce, retType, sr)
            (Nothing, True) -> error "Accessor returns void"
            (Nothing, False) -> Right (I.FnCallStmnt ce, sr)
        Right (ctx', fqn, vDefId) -> do
          (fnId, fnType, _) <- visitVDef ctx ctx' [(I.TypeGenericArg lhsType, sr)] sr (VFqn fqn, vDefId) ctx.inUnsafeCode
          let fnExpr = (I.LoadConstantExpr $ I.ConstFnPtr fnId, fnType, sr)
          getCallExpr ctx sr sr fnExpr (Just lhs) argsExprs False <&> \(ce, r) -> case r of
            Just retType -> Left (I.AFnCallExpr ce, retType, sr)
            Nothing -> Right (I.FnCallStmnt ce, sr)

getFnCallExpr :: (MonadTc m) => Ctx -> TypeHint -> SrcRange -> A.FnCallExpr -> Bool -> m (Either I.Expr I.Statement)
getFnCallExpr ctx hint sr astExpr expectIterator = do
  let f = do
        -- Not a member fn call
        fnExpr <- getExpr ctx (FnReturningHint hint) astExpr.fn
        getCallExpr ctx (snd astExpr.fn) sr fnExpr Nothing astExpr.args expectIterator <&> \(ce, r) ->
          case r of
            Just t -> Left (I.AFnCallExpr ce, t, sr)
            Nothing -> Right (I.FnCallStmnt ce, sr)

  -- Check if this is a member fn
  case fst astExpr.fn of
    A.AnAccessorExpr a -> case fst a.accessor of
      -- If an accessor has generic arguments then it must be a member function call (fields cannot be generic)
      A.ANameAccessor name (Just gArgs) -> do
        getMemberFnCallExpr ctx hint sr a.expr (Left name, snd a.accessor) gArgs astExpr.args expectIterator
      A.ANameAccessor name Nothing -> do
        let getMemberFn =
              getMemberFnCallExpr ctx hint sr a.expr (Left name, snd a.accessor) [] astExpr.args expectIterator
        (_, lhsType, _) <- getExpr ctx NoHint a.expr
        astTsDefMaybe <- getAstTDefFromType ctx.tcIn lhsType
        case astTsDefMaybe of
          Just (A.AStructDef s) -> if name `notElem` Ins.keys s.fields then getMemberFn else f
          -- Could be an enum, tuple, etc.
          _ -> getMemberFn
      _ -> f
    _ -> f

getCallExpr ::
  (MonadTc m) =>
  Ctx ->
  SrcRange ->
  SrcRange ->
  I.Expr ->
  Maybe I.Expr ->
  [A.Expr] ->
  Bool ->
  m (I.FnCallExpr, Maybe I.Type)
getCallExpr ctx fnSr sr fnExpr@(_, fnType, _) selfArgMaybe astArgExprs expectIterator = do
  (expectedArgs', isVarArgs, retTypeOrVoid) <- case fnType of
    I.AFnType f -> do
      when expectIterator $ addError SevError ctx.et sr "Not an iterator"
      pure (f.params, f.isVarArgs, f.ret)
    I.AnAccessorType f -> do
      when expectIterator $ addError SevError ctx.et sr "Not an iterator"
      pure (toList f.params, f.isVarArgs, Just f.ret)
    I.AnIteratorType f -> do
      unless expectIterator $ addError SevError ctx.et sr "Cannot call an iterator, consider using a for loop"
      pure (f.params, False, Just f.ret)
    I.AnAccessorIteratorType f -> do
      unless expectIterator $ addError SevError ctx.et sr "Cannot call an iterator, consider using a for loop"
      pure (toList f.params, False, Just f.ret)
    _ -> throw ctx.et fnSr "Type is not callable"

  -- Check the self type (in case the member function's first arg is not Self)
  forM_ selfArgMaybe $ \(_, act, argSr) -> do
    case uncons expectedArgs' of
      Just ((_, ex), _) ->
        unless (act == ex) $ do
          (act', ex') <- format2Types act ex
          addError SevError ctx.et argSr $ T.concat ["Incorrect type for function self argument\nExpected ", ex', ", got ", act']
      _ ->
        throw ctx.et argSr $ T.concat ["Member function takes no parameters"]

  -- Remove self arg from expectedArgs as it is dealt with separately ^
  let expectedArgs = if isJust selfArgMaybe then tail expectedArgs' else expectedArgs'

  if isVarArgs
    then
      unless (length astArgExprs >= length expectedArgs) $ addError SevError ctx.et sr "Wrong number of arguments to function"
    else
      unless (length astArgExprs == length expectedArgs) $ addError SevError ctx.et sr "Wrong number of arguments to function"

  -- Get argument expressions
  args1 <- forM (zip astArgExprs expectedArgs) $ \(astArgExpr, (mode, expectedType)) -> do
    e@(_, t', _) <- getExpr ctx (TypeHint expectedType) astArgExpr
    rawSliceToSlice <- case (t', expectedType) of
      (I.ANamedType id, I.SliceType elType) -> do
        c <- getTDef id <&> I.tDefCommon
        pure $ c.fqn == TFqn "@stlib/raw_slice:RawSlice" && (c.genericArgs !! 0) == I.TypeGenericArg elType
      _ -> pure False
    e'@(_, t, sr') <-
      if rawSliceToSlice
        then pure (I.RawSliceToSliceExpr e, expectedType, thd3 e)
        else
          if mode == Exclusive then pure e else iCast expectedType e
    d <- getDropFn ctx.tcIn t sr'
    pure (e', d)

  -- Varargs expressions (if any)
  args2 <- forM (drop (length expectedArgs) astArgExprs) $ \astArgExpr -> do
    getExpr ctx NoHint astArgExpr <&> (,Nothing)

  let args' = args1 ++ args2

  -- Check args types (self arg already checked)
  forM_ (zip3 (snd3 . fst <$> args') (snd <$> expectedArgs) (snd <$> astArgExprs)) $ \(act, ex, argSr) ->
    unless (act == ex) $ do
      (act', ex') <- format2Types act ex
      addError SevError ctx.et argSr $ T.concat ["Incorrect type for function argument\nExpected ", ex', ", got ", act']

  selfDropMaybe <- case selfArgMaybe of
    Just (_, t, sr') -> getDropFn ctx.tcIn t sr'
    _ -> pure Nothing

  noThrow <- case fst3 fnExpr of
    I.LoadConstantExpr (I.ConstFnPtr id) -> fnIsNoThrow id
    _ -> pure False
  unless noThrow $ setUsesThrowingFns True

  let args = fromMaybe args' $ selfArgMaybe <&> (\x -> (x, selfDropMaybe) : args')
  pure (I.FnCallExpr fnExpr args noThrow, retTypeOrVoid)

getOpExpr :: (MonadTc m) => Ctx -> TypeHint -> SrcRange -> OpName' -> A.Expr -> Maybe A.Expr -> m I.Expr
getOpExpr ctx hint sr opName lhsAstExpr rhsAstExprMaybe =
  let action = getMemberFnCallExpr ctx hint sr lhsAstExpr (first Right opName) def (maybeToList rhsAstExprMaybe) False
   in action >>= \case Left e -> pure e; _ -> throw ctx.et sr "Operator returns void"

getAccessorExpr :: (MonadTc m) => Ctx -> SrcRange -> A.AccessorExpr -> m I.Expr
getAccessorExpr ctx sr astAccessorExpr = do
  e@(_, t, _) <- getExpr ctx NoHint astAccessorExpr.expr
  case t of
    I.TupleType tupType -> case fst astAccessorExpr.accessor of
      A.AnIndexAccessor i -> do
        unless (i >= 0 && i < length tupType)
          $ addError SevError ctx.et astAccessorExpr.accessor "Index out of range"
        dropFn <- getDropFn ctx.tcIn t sr
        let accExpr = I.FieldAccessorExpr {expr = e, index = i, dropFn = dropFn}
        pure (I.AFieldAccessorExpr accExpr, toList tupType !! i, sr)
      _ -> throw ctx.et sr "Accessor is not valid for tuples"
    I.PtrType Nothing -> throw ctx.et sr "Accessors are not not valid for void pointers"
    I.PtrType (Just pointeeType) -> case fst astAccessorExpr.accessor of
      A.AnIndexExprAccessor idxAstExpr -> do
        idxExpr <- getExpr ctx NoHint idxAstExpr
        pure (I.PtrDerefExpr (I.APtrAddExpr $ I.PtrAddExpr {expr = e, index = idxExpr}, t, sr), pointeeType, sr)
      A.AStarAccessor ->
        pure (I.PtrDerefExpr e, pointeeType, sr)
      _ -> throw ctx.et sr "Accessor is not valid for pointers"
    I.ConstPtrType pointeeType -> case fst astAccessorExpr.accessor of
      A.AStarAccessor -> pure (I.PtrDerefExpr e, pointeeType, sr)
      _ -> throw ctx.et sr "Accessor is not valid for const pointers"
    I.ANamedType id -> do
      td <- checkTDef2 id
      case td of
        I.AStructDef2 s -> case fst astAccessorExpr.accessor of
          A.ANameAccessor name gArgsMaybe -> do
            -- Member function calls are handled in getFnCallExpr
            when (isJust gArgsMaybe) $ throw ctx.et astAccessorExpr.accessor "Member function call is not valid here"
            case Ins.lookupWithIndex name s.fields of
              Nothing ->
                throw ctx.et (snd astAccessorExpr.accessor) $ "No such field: " <> un name
              Just ((fieldType, attribs), fieldIdx) -> do
                when (not ctx.inUnsafeCode && Attribute "Unsafe" `elem` attribs)
                  $ addError SevError ctx.et sr "Cannot access unsafe field in safe context"
                dropFn <- getDropFn ctx.tcIn t sr
                pure (I.AFieldAccessorExpr $ I.FieldAccessorExpr e (fromIntegral fieldIdx) dropFn, fieldType, sr)
          _ -> throw ctx.et sr "Accessor type is not valid on structs"
        I.AUnionDef2 s -> case fst astAccessorExpr.accessor of
          A.ANameAccessor name gArgsMaybe -> do
            -- Member function calls are handled in getFnCallExpr
            when (isJust gArgsMaybe) $ throw ctx.et astAccessorExpr.accessor "Member function call is not valid here"
            case Ins.lookupWithIndex name s.dataCons of
              Nothing ->
                throw ctx.et (snd astAccessorExpr.accessor) $ "No such data constructor: " <> un name
              Just (fieldType, fieldIdx) ->
                pure (I.AFieldAccessorExpr $ I.FieldAccessorExpr e (fromIntegral fieldIdx) Nothing, fieldType, sr)
          _ -> throw ctx.et sr "Accessor type is not valid on unions"
        I.AnEnumDef2 _ -> throw ctx.et sr "Accessors are not valid on enums\nConsider using pattern matching"
    _ -> throw ctx.et sr "Accessor is not valid for this type"

checkVarType' :: (MonadTc m) => Ctx -> I.Type -> I.Type -> SrcRange -> m ()
checkVarType' ctx act ex sr =
  unless (ex == act) $ do
    (act', ex') <- format2Types act ex
    throw ctx.et sr $ "Wrong type for variable\nExpected " <> ex' <> ", got " <> act'

checkVarType :: (MonadTc m) => Ctx -> I.Type -> SrcRange -> Maybe A.TypeExpr -> m ()
checkVarType ctx t sr =
  \case
    Just ex'' -> do
      ex <- getType ctx ex''
      checkVarType' ctx t ex sr
    _ -> pure ()

makeDestructure :: (MonadTc m) => Ctx -> I.Type -> A.Destructure -> m (I.Destructure, Ctx)
makeDestructure ctx t (A.IgnoreDes astTypeMaybe, sr) = do
  checkVarType ctx t sr astTypeMaybe
  dropFn <- getDropFn ctx.tcIn t sr
  pure (I.IgnoreDes dropFn, ctx)
--
makeDestructure ctx t (A.NameDes name astTypeMaybe, sr) = do
  checkVarType ctx t sr astTypeMaybe
  (ctx', uid) <- makeLocalVar ctx t name
  dropFn <- getDropFn ctx.tcIn t sr
  pure (I.NameDes uid name dropFn, ctx')
--
makeDestructure ctx t (A.TupleDes xs, sr) = do
  ys <- case t of I.TupleType ys -> pure ys; _ -> throw ctx.et sr "Not a tuple"
  -- Recursively loop over tuple elements and build up a list of I.Destructure
  -- The context is updated on each iteration
  (ds, finalCtx) <- foldM (\(ds, c) (t', d) -> makeDestructure c t' d <&> first (: ds)) ([], ctx) (zipList2 ys xs)
  pure (I.TupleDes $ must $ listToList2 $ reverse ds, finalCtx)
--
makeDestructure ctx t (A.ArrayDes xs, sr) = do
  (t', n) <- case t of I.ArrayType t' n -> pure (t', n); _ -> throw ctx.et sr "Not an array"
  unless (n == fromIntegral (length xs)) $ throw ctx.et sr "Wrong number of elements"
  (ds, finalCtx) <- foldM (\(ds, c) d -> makeDestructure c t' d <&> first (: ds)) ([], ctx) (toList xs)
  pure (I.ArrayDes $ must $ listToList1 $ reverse ds, finalCtx)
--
makeDestructure ctx t (A.StructDes astFields, sr) = do
  s <- case t of
    I.ANamedType id -> checkTDef2 id >>= \case I.AStructDef2 s -> pure s; _ -> throw ctx.et sr "Not a struct"
    _ -> throw ctx.et sr "Not a struct"
  forM_ (Ins.keys astFields) $ \k -> unless (k `elem` Ins.keys s.fields) $ throw ctx.et sr "Unknown field"

  -- TODO Allow skipping fields, same as fieldName=_
  unless (Ins.keysSet astFields == Ins.keysSet s.fields) $ throw ctx.et sr "Missing field(s)"

  (ds, finalCtx) <-
    foldM
      ( \(ds, c) (name, (sr', d)) -> do
          (fieldType, fieldIdx) <- case Ins.lookupWithIndex name s.fields of
            Nothing -> throw ctx.et sr' $ "No such field: " <> un name
            Just ((ft, _), i) -> pure (ft, i)
          (d'', c') <- makeDestructure c fieldType d
          pure ((d'', fieldIdx) : ds, c')
      )
      ([], ctx)
      (toList astFields)

  pure (I.AStructDes $ must $ listToList1 $ reverse ds, finalCtx)

makeConstDestructure :: (MonadTc m) => Ctx -> I.Constant -> A.Destructure -> m Ctx
makeConstDestructure ctx (_, t) (A.IgnoreDes astTypeMaybe, sr) = do
  checkVarType ctx t sr astTypeMaybe
  pure ctx
--
makeConstDestructure ctx constVal@(_, exprType) (A.NameDes name astTypeMaybe, sr) = do
  constVal'@(_, actualType) <- case astTypeMaybe of
    Just astType -> do
      ty <- getType ctx astType
      c@(_, newType) <- iCastConstant ty constVal
      checkVarType' ctx newType ty sr
      pure c
    _ -> do
      checkVarType ctx exprType sr astTypeMaybe
      pure constVal

  pure $ ctx {variables = Variable name (Right $ fst constVal') actualType : ctx.variables}
--
makeConstDestructure ctx constVal (A.TupleDes xs, sr) = do
  ys <- case fst constVal of I.ConstStructOrTuple x -> pure x; _ -> throw ctx.et sr "Not a tuple"
  let zs = zip ys (toList xs)
  foldM (\newCtx (co, d) -> makeConstDestructure newCtx co d) ctx zs
--
makeConstDestructure ctx constVal@(_, t) (A.ArrayDes xs, sr) = do
  (_, n) <- case t of I.ArrayType t' n -> pure (t', n); _ -> throw ctx.et sr "Not an array"
  unless (n == fromIntegral (length xs)) $ throw ctx.et sr "Wrong number of elements"
  let vals = case fst constVal of I.ConstArray elType x -> x <&> (,elType); _ -> undefined
  let zs = zip (toList xs) (toList vals)
  foldM (\newCtx (d, c) -> makeConstDestructure newCtx c d) ctx zs
--
makeConstDestructure _ctx _constVal (A.StructDes _astFields, _sr) = do
  undefined -- TODO

-- If the destructure pattern contains type annotations then this returns the overall type
-- E.g. var (a: I32, b: I32) = ... produces the type (I32, I32)
-- TODO Return a TypeHint so destructures such as (a: I32, b) work
getDestructureTypeHint :: (MonadTc m) => Ctx -> A.Destructure -> m (Maybe I.Type)
getDestructureTypeHint ctx (d, sr) = case d of
  A.NameDes _ astTypeExpr -> forM astTypeExpr $ getType ctx
  A.IgnoreDes astTypeExpr -> forM astTypeExpr $ getType ctx
  A.TupleDes xs -> do
    xs' <- forM xs $ getDestructureTypeHint ctx
    pure $ case sequence xs' of
      Just xs'' -> Just $ I.TupleType xs''
      _ -> Nothing
  A.ArrayDes xs -> do
    xs' <- catMaybes . toList <$> forM xs (getDestructureTypeHint ctx)
    case xs' of
      [] -> pure Nothing
      [x] -> pure $ Just $ I.ArrayType x $ fromIntegral $ length xs
      (y : ys) -> do
        unless (all (== y) ys) $ addError SevError ctx.et sr "Conflicting types for array elements"
        pure $ Just y
  A.StructDes _ ->
    pure Nothing

getVarStmnt :: (MonadTc m) => Ctx -> A.Destructure -> A.Expr -> m ((I.Destructure, I.Expr), Ctx)
getVarStmnt ctx astDes astExpr = do
  hint <- getDestructureTypeHint ctx astDes
  let hint' = maybe NoHint TypeHint hint
  e@(_, t, _) <- getExpr ctx hint' astExpr >>= case hint of Just h -> iCast h; _ -> pure
  checkTypeHasRuntimeRepr ctx.et (snd astExpr) t
  (d, ctx') <- makeDestructure ctx t astDes
  pure ((d, e), ctx')

-- Changes `x += 1` to `x = x + 1`
-- This is only valid if the lhs is pure (e.g. accessing a field)
rewriteAstAssignmentStmnt :: (MonadTcError m) => Ctx -> A.Statement -> m A.AssignmentStmnt
rewriteAstAssignmentStmnt ctx (s, sr) = case s of
  A.AnAssignmentStmnt x -> pure x
  A.CompoundAssignmentOpStmnt o -> do
    let op = first (\(OpName n) -> OpName $ T.take (length n - 1) n) o.op -- Remove '=' from end
    let rhs = (A.AnInfixOpExpr $ A.InfixOpExpr op o.lhs o.rhs, sr)
    pure $ A.AssignmentStmnt (Just $ fst o.lhs) (snd o.lhs) rhs
  _ -> throw ctx.et sr "Expected assignment"

getAssignmentStmnt :: (MonadTc m) => Ctx -> A.AssignmentStmnt -> m I.AssignmentStmnt
getAssignmentStmnt ctx x = case x.lhs of
  Nothing -> do
    e@(_, lhsType, _) <- getExpr ctx NoHint x.value
    checkTypeHasRuntimeRepr ctx.et (snd x.value) lhsType
    des <- getDropFn ctx.tcIn lhsType x.lhsSr
    pure $ I.AssignmentStmnt {lhs = Nothing, value = e, lhsDestructor = des}
  Just astLhs -> do
    lhs@(_, lhsType, _) <- getExpr ctx NoHint (astLhs, x.lhsSr)
    e@(_, rhsType, sr) <- getExpr ctx (TypeHint lhsType) x.value >>= iCast lhsType
    unless (lhsType == rhsType) $ addError SevError ctx.et sr "Expression type does not match LHS type"
    des <- getDropFn ctx.tcIn lhsType x.lhsSr
    pure $ I.AssignmentStmnt {lhs = Just lhs, value = e, lhsDestructor = des}

getFnCallStmnt :: (MonadTc m) => Ctx -> A.FnCallExpr -> SrcRange -> m I.Statement
getFnCallStmnt ctx x sr = do
  getFnCallExpr ctx NoHint sr x False >>= \case
    Left e@(_, t, sr') -> do
      des <- getDropFn ctx.tcIn t sr'
      addError SevWarning ctx.et sr "Return value discarded"
      pure (I.ExprStmnt e des, sr)
    Right s -> pure s

getIfElseStmnt :: (MonadTc m) => Ctx -> A.IfElseStmnt -> SrcRange -> m (Maybe I.Statement)
getIfElseStmnt ctx x sr = do
  if x.isConst
    then do
      -- Evaluate condition and chosen branch at compile time
      c <- getConstLitExpr ctx (TypeHint bool) x.cond
      b <- case c of
        (I.ConstBool b, t) | t == bool -> pure b
        _ -> throw ctx.et x.cond "Expected boolean"
      if b
        then do
          Just <$> getCodeBlockStmnt ctx [x.thenExpr] []
        else do
          forM x.elseExprMaybe $ \e -> getCodeBlockStmnt ctx [e] []
    else do
      c <- getExpr ctx (TypeHint bool) x.cond
      th <- getCodeBlockStmnt ctx [x.thenExpr] []
      el <- forM x.elseExprMaybe $ \s -> getCodeBlockStmnt ctx [s] []
      pure $ Just (I.AnIfElseStmnt $ I.IfElseStmnt {cond = c, thenStmnt = th, elseStmntMaybe = el}, sr)

getReturnStmnt :: (MonadTc m) => Ctx -> SrcRange -> Maybe A.Expr -> m I.Statement
getReturnStmnt ctx sr e = do
  case e of
    Just e' -> do
      when ctx.inIterator $ addError SevError ctx.et sr "Iterators must return void; use yield to produce a value"

      e'' <- case ctx.returnType of
        Just r -> do
          e''@(_, actualType, _) <- getExpr ctx (TypeHint r) e' >>= if ctx.inAccessor then pure else iCast r

          let dontMatch = do
                (exp', act') <- format2Types r actualType
                addError SevError ctx.et e' $ "Expression type does not match function return type\nExpected " <> exp' <> ", got " <> act'

          if actualType == r || not ctx.inAccessor
            then do
              unless (actualType == r) dontMatch
              pure e''
            else do
              let isAccRawPtr = actualType == I.PtrType (Just r)
              -- Check if the function return type is Slice[A] and the returned value is RawSlice[A]
              isAccRawSlice <- case (r, actualType) of
                (I.SliceType t, I.ANamedType id) -> do
                  c <- getTDef id <&> I.tDefCommon
                  pure $ c.fqn == TFqn "@stlib/raw_slice:RawSlice" && (c.genericArgs !! 0) == I.TypeGenericArg t
                _ -> pure False

              unless (isAccRawPtr || isAccRawSlice) dontMatch

              pure $ if isAccRawPtr then (I.PtrDerefExpr e'', r, sr) else (I.RawSliceToSliceExpr e'', r, sr)
        _ -> do
          addError SevError ctx.et e' "Returning expression in function that returns void"
          getExpr ctx NoHint e'
      pure (I.ReturnStmnt (Just e''), sr)
    _ -> do
      unless (isNothing ctx.returnType || ctx.inIterator) $ addError SevError ctx.et sr "Expected an expression"
      pure (I.ReturnStmnt Nothing, sr)

-- TODO Could this use fold instead of recursion?
getCodeBlockStmnt :: (MonadTc m) => Ctx -> [A.Statement] -> [I.Statement] -> m I.Statement
getCodeBlockStmnt ctx ((s, sr) : astStmnts) hirStmnts = case s of
  A.AVarStmnt d e -> do
    ((d', e'), ctx') <- getVarStmnt ctx d e
    getCodeBlockStmnt ctx' astStmnts ((I.VarStmnt d' e', sr) : hirStmnts)
  A.UninitVarStmnt name'@(name, sr') astTypeExpr -> do
    t <- getType ctx astTypeExpr
    checkTypeHasRuntimeRepr ctx.et (snd astTypeExpr) t
    (ctx', uid) <- makeLocalVar ctx t name'
    dropFn <- getDropFn ctx'.tcIn t sr'
    let s' = (I.UninitVarStmnt uid name dropFn t, sr)
    getCodeBlockStmnt ctx' astStmnts (s' : hirStmnts)
  A.AnAssignmentStmnt x -> do
    s' <- getAssignmentStmnt ctx x
    getCodeBlockStmnt ctx astStmnts ((I.AnAssignmentStmnt s', sr) : hirStmnts)
  A.CompoundAssignmentOpStmnt o -> do
    let basic = do
          -- If there isn't a definition for the compound assignment then the assignment is transformed into:
          -- { borrow ref r = f(x()); r = r + y; }
          let op = first (\(OpName n) -> OpName $ T.take (length n - 1) n) o.op -- Remove '=' from end
          let r = A.NameExpr (VName "r", sr) Nothing
          let rhs = (A.AnInfixOpExpr $ A.InfixOpExpr op (r, sr) o.rhs, sr)
          let asStmnt = A.AnAssignmentStmnt $ A.AssignmentStmnt (Just r) sr rhs
          let bwStmnt = A.BorrowStatement Exclusive (VName "r", sr) Nothing o.lhs
          s' <- getCodeBlockStmnt ctx [(bwStmnt, sr), (asStmnt, sr)] []
          getCodeBlockStmnt ctx astStmnts (s' : hirStmnts)

    lhs@(_, lhsType, _) <- getExpr ctx NoHint o.lhs
    getVDefsInType ctx.tcIn lhsType >>= \case
      Nothing -> basic
      Just (memberFns, lhsTFqn) -> do
        let defMaybe = HMM.lookup (fst o.op) memberFns.operators
        case defMaybe of
          [] ->
            basic
          [d] -> do
            let c = A.vDefCommon d
            let fqn = VFqn $ un lhsTFqn <> "." <> un (fst c.name)
            typeCtx <- getTypeCtx ctx sr lhsType <&> must -- Type has value defs and therefore has a context
            unless (null c.genericParams)
              $ throw ctx.et sr "Operators cannot take generic arguments" -- TODO type inference?
            (id, t, vDef) <- visitVDef ctx typeCtx [] sr (fqn, d) ctx.inUnsafeCode

            let isAccessor = case t of
                  I.AnAccessorType _ -> True
                  I.AnAccessorIteratorType _ -> True
                  _ -> False

            let callee = case vDef of
                  I.AConstDef cd -> (I.LoadConstantExpr $ case cd.value of Just x -> x; _ -> I.ConstExtern id, t, sr)
                  _ -> (I.LoadConstantExpr $ I.ConstFnPtr id, t, sr)

            s' <-
              getCallExpr ctx (snd o.op) sr callee (Just lhs) [o.rhs] False >>= \(ce, r) ->
                case (r, isAccessor) of
                  (Just _, _) -> throw ctx.et sr "Compound assignment operator functions must return void"
                  (Nothing, True) -> throw ctx.et sr "Compound assignment operator functions cannot be accessors"
                  (Nothing, False) -> pure $ I.FnCallStmnt ce
            getCodeBlockStmnt ctx astStmnts ((s', sr) : hirStmnts)
          -- TODO Use type hint from arg to choose an operator function
          _ -> throw ctx.et o.op $ "Operator is ambiguous: " <> un (fst o.op)
  A.FnCallStmnt (x, _) -> do
    s' <- getFnCallStmnt ctx x sr
    getCodeBlockStmnt ctx astStmnts (s' : hirStmnts)
  A.AnIfElseStmnt x -> do
    s' <- getIfElseStmnt ctx x sr
    case s' of
      Just s'' -> getCodeBlockStmnt ctx astStmnts (s'' : hirStmnts)
      _ -> getCodeBlockStmnt ctx astStmnts hirStmnts
  A.LoopStmnt body -> do
    body' <- getCodeBlockStmnt ctx {inLoop = True} [body] []
    getCodeBlockStmnt ctx astStmnts ((I.LoopStmnt body', sr) : hirStmnts)
  A.BreakStmnt -> do
    unless ctx.inLoop $ throw ctx.et sr "Break is not valid outside of loops"
    getCodeBlockStmnt ctx astStmnts ((I.BreakStmnt, sr) : hirStmnts)
  A.ContinueStmnt -> do
    unless ctx.inLoop $ throw ctx.et sr "Continue is not valid outside of loops"
    getCodeBlockStmnt ctx astStmnts ((I.ContinueStmnt, sr) : hirStmnts)
  A.CodeBlockStmnt ss -> do
    (s', _) <- getCodeBlockStmnt ctx ss []
    let isEmpty = case s' of I.CodeBlockStmnt ss' | null ss' -> True; _ -> False
    getCodeBlockStmnt ctx astStmnts $ if isEmpty then hirStmnts else (s', sr) : hirStmnts
  A.ReturnStmnt x -> do
    when (ctx.inIterator && isJust x)
      $ addError SevError ctx.et sr "Iterators cannot return values; yield to produce a value or return void to terminate early"
    s' <- getReturnStmnt ctx sr x
    getCodeBlockStmnt ctx astStmnts (s' : hirStmnts)
  A.AForEachLoopStmnt fe -> do
    when fe.isConst undefined -- TODO
    fc <- case fst fe.inExpr of A.AFnCallExpr fc -> pure fc; _ -> throw ctx.et fe.inExpr "Expected iterator call"
    x <- getFnCallExpr ctx NoHint (snd fe.inExpr) fc True
    (e, yieldType, fnCallExprSr) <- case x of Left e -> pure e; Right _ -> throw ctx.et fe.inExpr "Iterators cannot yield void"

    let fnCallExpr = case e of I.AFnCallExpr y -> y; _ -> undefined
    (iterFn, iterFnIsNoThrow) <- case fst3 fnCallExpr.fn of
      I.LoadConstantExpr (I.ConstFnPtr id) -> fnIsNoThrow id <&> (id,)
      _ -> throw ctx.et fnCallExprSr "Iterator function must be compile-time known"

    addUsedIter iterFn -- For tracking dependencies between functions
    unless iterFnIsNoThrow $ setUsesThrowingFns True

    checkTypeHasRuntimeRepr ctx.et fnCallExprSr yieldType
    (d, ctx') <- makeDestructure ctx yieldType fe.var

    body <- getCodeBlockStmnt ctx' {inLoop = True} [fe.body] []
    let s' =
          I.AForEachLoopStmnt
            $ I.ForEachLoopStmnt
              d
              fe.mode
              yieldType
              (iterFn, snd3 fnCallExpr.fn)
              iterFnIsNoThrow
              fnCallExpr.args
              body
    getCodeBlockStmnt ctx astStmnts ((s', sr) : hirStmnts)
  A.YieldStmnt astExpr -> do
    expectedType <- case (ctx.returnType, ctx.inIterator) of
      (Just r, True) -> pure r
      _ -> throw ctx.et sr "Yield is only valid within iterator functions"
    e@(_, actualType, sr') <- getExpr ctx (TypeHint expectedType) astExpr
    (exp', act') <- format2Types expectedType actualType
    unless (expectedType == actualType)
      $ addError SevError ctx.et sr' ("Wrong type for yield expression\nExpected " <> exp' <> ", got " <> act')
    getCodeBlockStmnt ctx astStmnts ((I.YieldStmnt e, sr) : hirStmnts)
  A.ForLoopStmnt vars cond as False innerStmnt -> do
    (varsRev, ctx') <-
      foldM
        (\(acc :: [(I.Destructure, I.Expr)], c) (d, e) -> getVarStmnt c d e <&> first (: acc))
        ([], ctx)
        vars

    let ctx'' = ctx' {inLoop = True}
    condExpr <- getExpr ctx'' (TypeHint bool) cond

    as' <- forM as $ \a ->
      getCodeBlockStmnt ctx'' [a] []

    innerStmnt' <- getCodeBlockStmnt ctx'' [innerStmnt] []

    let s' = I.ForLoopStmnt (reverse varsRev) condExpr as' innerStmnt'
    getCodeBlockStmnt ctx astStmnts ((s', sr) : hirStmnts)
  -- Const for loop: vars, conditions, and assignments all evaluated at compile-time
  A.ForLoopStmnt vars cond as True innerStmnt -> do
    -- Get variables
    ctx' <-
      foldM
        ( \newCtx (astDes, astExpr) -> do
            hint <- getDestructureTypeHint newCtx astDes
            let hint' = maybe NoHint TypeHint hint
            c <- getConstLitExpr newCtx hint' astExpr
            makeConstDestructure newCtx c astDes
        )
        ctx
        vars

    -- Run loop
    let doIter :: (MonadTc m) => Ctx -> [I.Statement] -> Int -> m [I.Statement]
        doIter ctx'' irStmnts iterCount = do
          -- Check condition is still met
          cond' <- fst <$> getConstLitExpr ctx'' (TypeHint bool) cond
          case cond' of
            I.ConstBool True -> do
              -- Prevent infinite loops
              when (iterCount >= 1000) $ throw ctx.et sr "Reached iteration limit"
              -- Type check loop contents
              innerStmnt' <- getCodeBlockStmnt ctx'' [innerStmnt] []
              -- Apply assignments
              ctx''' <-
                foldM
                  ( \newCtx a' -> do
                      -- Rewriting the assignment statement is valid because everything is pure when doing const eval
                      a <- rewriteAstAssignmentStmnt ctx a'
                      case a.lhs of
                        Nothing -> do
                          _ <- getConstLitExpr newCtx NoHint a.value
                          pure newCtx
                        Just (A.NameExpr name gArgsMaybe) | isNothing gArgsMaybe -> do
                          let foundMaybe =
                                findWithIndex
                                  (\v -> isRight v.uidOrVal && fst v.name == fst name)
                                  newCtx.variables
                          case foundMaybe of
                            Just (va, i) -> do
                              c <- fst <$> getConstLitExpr newCtx (TypeHint va.typ) a.value
                              pure $ newCtx {variables = updateAt i (\v -> v {uidOrVal = Right c}) newCtx.variables}
                            _ -> throw ctx.et a.lhsSr "Variable not found"
                        _ ->
                          throw ctx.et a.lhsSr "Expected variable name"
                  )
                  ctx''
                  as
              doIter ctx''' (innerStmnt' : irStmnts) (iterCount + 1)
            I.ConstBool False ->
              pure irStmnts
            _ -> throw ctx.et cond "Expected boolean"
    ss <- doIter ctx' [] 0 <&> filter (\case (I.CodeBlockStmnt xs, _) | null xs -> False; _ -> True)
    getCodeBlockStmnt ctx astStmnts (ss ++ hirStmnts)
  A.ARequireStmnt e -> do
    checkRequireStmnt ctx e
    getCodeBlockStmnt ctx astStmnts hirStmnts
  A.MatchStmnt False mode astExpr arms -> do
    e@(_, t, _) <- getExpr ctx NoHint astExpr
    arms' <- forM arms $ \b -> do
      -- TODO Check for exhaustiveness
      (ctx', p) <- getMatchBranchCtx ctx b.pattern t
      code <- getCodeBlockStmnt ctx' [b.code] []
      pure $ I.MatchBranch p (snd b.pattern) code
    getCodeBlockStmnt ctx astStmnts $ (I.MatchStmnt mode e arms', sr) : hirStmnts
  A.MatchStmnt True mode astExpr arms -> do
    unless (mode == Shared) $ throw ctx.et sr "Access mode must be shared for compile-time match"
    c <- getConstLitExpr ctx NoHint astExpr
    s' <- visitConstMatchBranch ctx sr c (toList arms)
    getCodeBlockStmnt ctx astStmnts (s' : hirStmnts)
  A.UnsafeStmnt s' -> do
    s'' <- getCodeBlockStmnt ctx {inUnsafeCode = True} [s'] []
    getCodeBlockStmnt ctx astStmnts (s'' : hirStmnts)
  A.ThrowStmnt e -> do
    setUsesThrowingFns True
    stringType <- getBuiltinType ctx (Namespace "@stlib/string") $ TName "String"
    let expectedType = I.ConstPtrType stringType
    e'@(_, actualType, _) <- getExpr ctx (TypeHint stringType) e
    unless (actualType == expectedType) $ do
      (act, ex) <- format2Types actualType expectedType
      addError SevError ctx.et sr $ T.concat ["Wrong type for throw statement\nExpected ", ex, ", got ", act]

    getCodeBlockStmnt ctx astStmnts ((I.ThrowStmnt e', sr) : hirStmnts)
  A.TryCatchStmnt tryStmnt (nameMaybe, nameSr) catchStmnt -> do
    tryStmnt' <- getCodeBlockStmnt ctx [tryStmnt] []
    (ctx', uidMaybe) <- case nameMaybe of
      Just n -> do
        -- Add exception variable for catch block
        uid <- newLocalVarUid
        stringType <- getBuiltinType ctx (Namespace "@stlib/string") $ TName "String"
        let typ = I.ConstPtrType stringType
        pure (ctx {variables = Variable (n, nameSr) (Left uid) typ : ctx.variables}, Just (uid, n, typ))
      _ -> pure (ctx, Nothing)
    catchStmnt' <- getCodeBlockStmnt ctx' [catchStmnt] []
    let s' = (I.TryCatchStmnt tryStmnt' uidMaybe catchStmnt', sr)
    getCodeBlockStmnt ctx astStmnts (s' : hirStmnts)
  A.BubbleStmnt e' -> do
    e''@(_, lhsType, _) <- getExpr ctx NoHint e'

    returnType <- case ctx.returnType of
      Just x -> pure x
      _ -> throw ctx.et sr "Error bubble operator is not valid in functions returning void"

    retErrType <- case returnType of
      I.ANamedType tDefId -> do
        d <- checkTDef2 tDefId
        let fqn = un (I.tDefCommon d).fqn
        unless (fqn `elem` ["@stlib/errors:IsError", "@stlib/errors:MaybeError", "@stlib/maybe:Maybe", "@stlib/errors:Result"])
          $ throw ctx.et sr "Return type is not IsError/Maybe/MaybeError/Result"
        case d of I.AnEnumDef2 x -> pure $ Ins.elems x.dataCons !! 1; _ -> pure Nothing
      _ -> throw ctx.et sr "Return type is not IsError/Maybe/MaybeError/Result"

    errType <- case lhsType of
      I.ANamedType tDefId -> do
        d <- checkTDef2 tDefId
        let fqn = un (I.tDefCommon d).fqn
        unless (fqn == "@stlib/errors:IsError" || fqn == "@stlib/errors:MaybeError")
          $ throw ctx.et sr "Type is not IsError/MaybeError"
        case d of I.AnEnumDef2 x -> pure $ Ins.elems x.dataCons !! 1; _ -> undefined
      _ -> throw ctx.et sr "Not an enum"

    unless (retErrType == errType) $ do
      (retErrType', errType') <- format2MaybeTypes "()" retErrType errType
      addError SevError ctx.et sr $ T.concat ["Error types do not match\nExpected ", retErrType', ", got ", errType']

    getCodeBlockStmnt ctx astStmnts ((I.BubbleStmnt e'', sr) : hirStmnts)
  A.BorrowStatement mode name'@(name, _) astTypeExprMaybe e -> do
    typeMaybe <- forM astTypeExprMaybe $ getType ctx
    let hint = fromMaybe NoHint $ typeMaybe <&> TypeHint
    e'@(_, actualType, _) <- getExpr ctx hint e
    case typeMaybe of
      Nothing -> pure ()
      Just expectedType ->
        unless (actualType == expectedType) $ do
          (act, ex) <- format2Types actualType expectedType
          addError SevError ctx.et sr $ T.concat ["Wrong type for borrow statement\nExpected ", ex, ", got ", act]
    (ctx', uid) <- makeLocalVar ctx actualType name'
    getCodeBlockStmnt ctx' astStmnts ((I.BorrowStatement mode uid name e', sr) : hirStmnts)
getCodeBlockStmnt _ [] [] =
  pure (I.CodeBlockStmnt [], def)
getCodeBlockStmnt _ [] hirStmnts@(s1 : _) =
  pure (I.CodeBlockStmnt $ reverse hirStmnts, srcRangeOf s1 $ must $ last hirStmnts)

makeLocalVar :: (MonadTc m) => Ctx -> I.Type -> VName' -> m (Ctx, I.LocalVarUid)
makeLocalVar ctx typ name@(_, sr) = do
  unless ctx.inUnsafeCode
    $ typeIsUnsafe typ
    >>= \isUnsafe -> when isUnsafe $ addError SevError ctx.et sr "Cannot use unsafe type in safe code"
  id <- newLocalVarUid
  pure (ctx {variables = Variable name (Left id) typ : ctx.variables}, id)

getEnumDef2OrError :: (MonadTc m) => Ctx -> SrcRange -> I.Type -> m I.EnumDef2
getEnumDef2OrError ctx sr t = do
  case t of
    I.ANamedType tDefId -> do
      checkTDef2 tDefId >>= \case
        I.AnEnumDef2 x -> pure x
        _ -> throw ctx.et sr "Not an enum"
    _ -> throw ctx.et sr "Not an enum"

findDataCons :: (MonadTcError m) => Ctx -> SrcRange -> I.EnumDef2 -> VName -> m (Maybe I.Type, Int)
findDataCons ctx sr enumDef name =
  case Ins.lookupWithIndex name enumDef.dataCons of
    Just x -> pure x
    _ -> throw ctx.et sr $ "No such data constructor: " <> un name

-- Similar to makeDestructure but for pattern matching
getMatchBranchCtx :: (MonadTc m) => Ctx -> A.Pattern -> I.Type -> m (Ctx, I.Pattern)
getMatchBranchCtx ctx (A.PatternAny, sr) typ = do
  dropFn <- getDropFn ctx.tcIn typ sr
  pure (ctx, I.PatternAny dropFn)
getMatchBranchCtx ctx (A.PatternName name, sr) typ = do
  (ctx', uid) <- makeLocalVar ctx typ name
  dropFn <- getDropFn ctx.tcIn typ sr
  pure (ctx', I.PatternName uid name dropFn)
getMatchBranchCtx ctx (A.PatternDataCons0 consName, sr) enumType = do
  enumDef <- getEnumDef2OrError ctx sr enumType
  (consActualTypeMaybe, consIdx) <- findDataCons ctx sr enumDef consName
  when (isJust consActualTypeMaybe) $ throw ctx.et sr "Data constructor holds a value"
  pure (ctx, I.PatternDataCons0 consIdx)
getMatchBranchCtx ctx (A.PatternDataCons1 consName innerPattern, sr) enumType = do
  enumDef <- getEnumDef2OrError ctx sr enumType
  (consActualTypeMaybe, consIdx) <- findDataCons ctx sr enumDef (fst consName)
  consActualType <- case consActualTypeMaybe of
    Just x -> pure x
    _ -> throw ctx.et consName "Data constructor does not hold a value"
  (ctx', p) <- getMatchBranchCtx ctx innerPattern consActualType
  pure (ctx', I.PatternDataCons1 consIdx p)

visitConstMatchPattern :: (MonadTc m) => Ctx -> I.Constant -> A.Pattern -> m (Maybe Ctx)
visitConstMatchPattern ctx (c, t) (p, sr) = case p of
  A.PatternAny ->
    pure $ Just ctx
  A.PatternName name ->
    pure $ Just $ ctx {variables = Variable name (Right c) t : ctx.variables}
  A.PatternDataCons0 consName -> do
    enumDef <- getEnumDef2OrError ctx sr t
    (consActualTypeMaybe, consIdx) <- findDataCons ctx sr enumDef consName
    when (isJust consActualTypeMaybe) $ throw ctx.et sr "Data constructor holds a value"
    case c of
      I.ConstEnum actualIdx ->
        if actualIdx == consIdx
          then
            pure $ Just ctx
          else
            pure Nothing
      _ -> throw ctx.et sr "Not an enum"
  A.PatternDataCons1 consName p' -> do
    enumDef <- getEnumDef2OrError ctx sr t
    (consActualTypeMaybe, consIdx) <- findDataCons ctx sr enumDef (fst consName)
    consActualType <- case consActualTypeMaybe of
      Just x -> pure x
      _ -> throw ctx.et consName "Data constructor does not hold a value"
    case c of
      I.ConstEnum actualIdx ->
        if actualIdx == consIdx
          then do
            -- TODO Don't have constant enums with data constructors yet
            x <- undefined
            visitConstMatchPattern ctx (x, consActualType) p'
          else
            pure Nothing
      _ -> throw ctx.et sr "Not an enum"

visitConstMatchBranch :: (MonadTc m) => Ctx -> SrcRange -> I.Constant -> [A.MatchBranch] -> m I.Statement
visitConstMatchBranch ctx sr _ [] = throw ctx.et sr "Match was not exhaustive"
visitConstMatchBranch ctx sr c (b : bs) = do
  newCtxMaybe <- visitConstMatchPattern ctx c b.pattern
  case newCtxMaybe of
    Just ctx' -> do
      -- Match
      getCodeBlockStmnt ctx' [b.code] []
    _ -> do
      -- Next
      visitConstMatchBranch ctx sr c bs

getMkTupleExpr :: (MonadTc m) => Ctx -> TypeHint -> SrcRange -> List2 A.Expr -> m I.Expr
getMkTupleExpr ctx hint sr xs = do
  xs' <- case hint of
    TypeHint (I.TupleType hs) -> do
      forM (zipList2 xs hs) $ \(e', t) ->
        getExpr ctx (TypeHint t) e' >>= iCast t
    _ ->
      forM xs $ getExpr ctx NoHint

  pure (I.MkTupleExpr xs', I.TupleType $ snd3 <$> xs', sr)

getArrayInitExpr :: (MonadTc m) => Ctx -> TypeHint -> SrcRange -> List1 A.Expr -> m I.Expr
getArrayInitExpr ctx hint fullSrcRange astExprs@(List1 astExpr0 astExprs') = do
  let hint' = case hint of TypeHint (I.ArrayType x _) -> TypeHint x; _ -> NoHint
  e0@(_, elementType, _) <- getExpr ctx hint' astExpr0
  es' <- forM astExprs' $ \e' -> do
    e@(_, t, sr) <- getExpr ctx (TypeHint elementType) e' >>= iCast elementType
    unless (t == elementType) $ throw ctx.et sr "Element type does not match type of first element"
    pure e
  let es = List1 e0 es'

  pure (I.ArrayInitExpr es, I.ArrayType elementType $ fromIntegral $ length astExprs, fullSrcRange)

getStructInitExpr :: (MonadTc m) => Ctx -> TypeHint -> SrcRange -> Maybe A.TypeExpr' -> SrcRange -> A.StructFields -> m I.Expr
getStructInitExpr ctx hint fullSrcRange astTypeExprMaybe sr' astFields = do
  (structType, fieldTypes) <- case (astTypeExprMaybe, hint) of
    (Just astTypeExpr, _) -> do
      t <- getType ctx (astTypeExpr, sr')
      fs <- getStructFields ctx sr' t
      pure (t, fs)
    (Nothing, TypeHint t) -> do
      fs <- getStructFields ctx sr' t
      pure (t, fs)
    (Nothing, _) -> throw ctx.et sr' "Unable to deduce struct type"
  --
  fieldsList <- forM (toList astFields) $ \(name, (sr, astExMaybe)) -> do
    let astEx = fromMaybe (A.NameExpr (name, sr) Nothing, sr) astExMaybe
    (expectedType, attribs) <- case Ins.lookup name fieldTypes of
      Just x -> pure x
      _ -> throw ctx.et sr $ "No such field: " <> un name
    when (not ctx.inUnsafeCode && Attribute "Unsafe" `elem` attribs) $ addError SevError ctx.et sr "Cannot access unsafe fields in safe code"
    e@(_, actualType, _) <- getExpr ctx (TypeHint expectedType) astEx >>= iCast expectedType
    unless (actualType == expectedType) $ do
      (act, ex) <- format2Types actualType expectedType
      addError SevError ctx.et sr $ T.concat ["Wrong type for struct field ", un name, "\nExpected ", ex, ", got ", act]
    pure e

  let namesList = Ins.keys astFields

  fieldIndexToExprsIndex <- forM (Ins.keys fieldTypes) $ \name ->
    case elemIndex name namesList of
      Just i -> pure i
      Nothing -> throw ctx.et fullSrcRange $ "Missing field: " <> un name

  pure
    ( I.AStructInitExpr
        $ I.StructInitExpr
          { exprs = must $ listToList1 fieldsList,
            fieldIndexToExprsIndex = must $ listToList1 fieldIndexToExprsIndex
          },
      structType,
      fullSrcRange
    )

getTypeAccessExprConst :: (MonadTc m) => Ctx -> TypeHint -> SrcRange -> Maybe A.TypeExpr -> VName' -> Maybe [A.GenericArg] -> m I.Constant
getTypeAccessExprConst ctx hint sr astTypeExprMaybe (name, nameSr) gArgsMaybe = do
  typeOrNs <- case astTypeExprMaybe of
    Just e -> getNamespaceOrType ctx e
    Nothing -> case hint of
      TypeHint x -> pure $ Right x
      FnReturningHint (TypeHint x) -> pure $ Right x
      _ -> throw ctx.et sr "Unable to deduce type"

  dataConsMaybe <- do
    case typeOrNs of
      Right (I.ANamedType tDefId) -> do
        checkTDef2 tDefId >>= \case
          I.AnEnumDef2 d -> do
            case Ins.lookupWithIndex name d.dataCons of
              Just x -> pure $ Just (d.e.c, x)
              _ -> pure Nothing
          I.AUnionDef2 d -> do
            case Ins.lookupWithIndex name d.dataCons of
              Just (x, i) -> pure $ Just (d.e.c, (Just x, i))
              _ -> pure Nothing
          _ -> pure Nothing
      _ -> pure Nothing

  case (dataConsMaybe, typeOrNs) of
    (Just (defCommon, (consType, consIdx)), Right t) ->
      case consType of
        Nothing -> do
          -- Data constructor does not hold a value so just produce a value of the enum type
          pure (I.ConstEnum consIdx, t)
        Just dcType -> do
          -- Data constructor does hold a value so need to produce a function that returns the enum value

          let fnType = I.AFnType $ I.FnType [(Move, dcType)] False (Just t) False
          let fqn = VFqn $ un defCommon.fqn <> ".$" <> un name

          -- Function is cached
          vDefIdMaybe <- getCachedVDef fqn defCommon.genericArgs <&> (<&> fst)
          vDefId <- case vDefIdMaybe of
            Just x -> pure x
            Nothing -> do
              reachableFromStart <- getStartedFromStart
              let c =
                    I.VDefCommon
                      { name = (VName $ "_" <> un name, sr),
                        dbgName = "_" <> un name,
                        fqn = fqn,
                        genericArgs = defCommon.genericArgs,
                        typ = fnType,
                        reachableFromStart = reachableFromStart,
                        attributes = []
                      }
              let f =
                    I.FnDef
                      { c = c,
                        isAccessor = False,
                        isIterator = False,
                        parameters = [(Move, dcType, Just $ VName "x")],
                        isVarArgs = False,
                        returnType = Just t
                      }
              vDefId <- addVDef $ I.AFnDef f
              let getArg = Hir.MoveLocalVarExpr (Hir.LocalVarUid 0) (VName "x")
              let body = Hir.ReturnStmnt (Just (Hir.DataConsExpr t consIdx (getArg, sr), sr)) []
              addFnDefBody vDefId (body, sr) True
              pure vDefId
          pure (I.ConstFnPtr vDefId, fnType)
    (Nothing, Left (ns, ast, astImports)) -> do
      case HM.lookup name ast.astVDefs.defs of
        Nothing -> throw ctx.et sr $ "No such definition: " <> un name
        Just astVDef -> do
          let outerCtx = mkFileCtx ns (ast, astImports) ctx.tcIn
          let fqn = mkVFqn ns name
          args <- forM (fromMaybe [] gArgsMaybe) $ getGenArg ctx
          (id, t, vDef) <- visitVDef ctx outerCtx args sr (fqn, astVDef) ctx.inUnsafeCode
          pure $ case vDef of
            I.AConstDef c -> case c.value of
              Just v -> (v, t)
              _ -> (I.ConstExtern id, t)
            I.AFnDef _ ->
              (I.ConstFnPtr id, t)
    (Nothing, Right t) ->
      getVDefsInType ctx.tcIn t >>= \case
        Nothing ->
          throw ctx.et nameSr $ "Name not found: " <> un name
        Just (vDefs, lhsTFqn) ->
          case HM.lookup name vDefs.defs of
            Nothing ->
              throw ctx.et nameSr $ "Name not found: " <> un name
            Just d -> do
              let c = A.vDefCommon d
              let fqn = VFqn $ un lhsTFqn <> "." <> un (fst c.name)

              typeCtx <- getTypeCtx ctx sr t <&> must -- Type has value defs and therefore has a context
              let fnAstGArgs = fromMaybe [] gArgsMaybe
              fnGArgs <- forM fnAstGArgs $ getGenArg ctx

              unless (length fnAstGArgs == length c.genericParams)
                $ throw ctx.et sr "Wrong number of generic arguments"

              (id, t', vDef) <- visitVDef ctx typeCtx fnGArgs sr (fqn, d) ctx.inUnsafeCode

              _ <- case (t', hint) of
                (I.AFnType f, FnReturningHint (TypeHint r))
                  | f.ret == Just t && isJust astTypeExprMaybe && r == t ->
                      pure () -- Could add a hint to use type inference
                (I.AFnType f, FnReturningHint _)
                  | f.ret /= Just t && isNothing astTypeExprMaybe -> do
                      t'' <- formatType False t
                      throw ctx.et sr $ "Member function has wrong return type, expected " <> t''
                _ -> pure ()

              pure $ case vDef of
                I.AConstDef cd -> (case cd.value of Just x -> x; _ -> I.ConstExtern id, t')
                I.AFnDef _ -> (I.ConstFnPtr id, t')
    _ -> undefined

getTypeAccessExpr :: (MonadTc m) => Ctx -> TypeHint -> SrcRange -> Maybe A.TypeExpr -> VName' -> Maybe [A.GenericArg] -> m I.Expr
getTypeAccessExpr ctx hint sr astTypeExprMaybe name gArgsMaybe = do
  (c, t) <- getTypeAccessExprConst ctx hint sr astTypeExprMaybe name gArgsMaybe
  pure (I.LoadConstantExpr c, t, sr)

getNameExpr :: (MonadTc m) => Ctx -> SrcRange -> VName' -> Maybe [A.GenericArg] -> m I.Expr
getNameExpr ctx sr name gArgsMaybe =
  case findLocalVarByName ctx (fst name) of
    Just x -> do
      -- Local variable
      unless (null gArgsMaybe) $ throw ctx.et sr "Local variables cannot take generic parameters"
      case x.uidOrVal of
        Left uid -> do
          let v = I.LocalVarExpr {uid = uid, name = name}
          pure (I.ALocalVarExpr v, x.typ, sr)
        Right c -> do
          pure (I.LoadConstantExpr c, x.typ, sr)
    _ -> do
      -- Global value definition
      fqnOrConst <- lookupVName ctx name
      case fqnOrConst of
        Left (ctx', vFqn, astDef) -> do
          let astGArgs = fromMaybe def gArgsMaybe
          gArgs <- forM astGArgs $ getGenArg ctx

          visitVDef ctx ctx' gArgs sr (vFqn, astDef) ctx.inUnsafeCode <&> getVDefExpr sr
        Right c -> pure (I.LoadConstantExpr $ fst c, snd c, sr)

getVDefExpr :: SrcRange -> (I.VDefId, I.Type, I.AnyVDef) -> I.Expr
getVDefExpr sr (id, t, vDef) = case vDef of
  I.AConstDef c -> case c.value of
    Just v -> (I.LoadConstantExpr v, t, sr)
    _ -> (I.LoadConstantExpr $ I.ConstExtern id, t, sr)
  I.AFnDef _ -> do
    (I.LoadConstantExpr $ I.ConstFnPtr id, t, sr)

-- '!' operator, handles Result and Maybe
getBubbleExpr :: (MonadTc m) => Ctx -> TypeHint -> SrcRange -> A.Expr -> m I.Expr
getBubbleExpr ctx _ sr e' = do
  e''@(_, lhsType, _) <- getExpr ctx NoHint e'

  returnType <- case ctx.returnType of
    Just x -> pure x
    _ -> throw ctx.et sr "Error bubble operator is not valid in functions returning void"

  -- The type in the Err() data constructor (if there is one)
  retErrType <- case returnType of
    I.ANamedType tDefId -> do
      d <- checkTDef2 tDefId
      let fqn = un (I.tDefCommon d).fqn
      unless (fqn `elem` ["@stlib/errors:IsError", "@stlib/errors:MaybeError", "@stlib/maybe:Maybe", "@stlib/errors:Result"])
        $ throw ctx.et sr "Return type is not IsError/Maybe/MaybeError/Result"
      case d of I.AnEnumDef2 x -> pure $ Ins.elems x.dataCons !! 1; _ -> pure Nothing
    _ -> throw ctx.et sr "Return type is not IsError/Maybe/MaybeError/Result"

  -- The type in the Ok() data constructor
  (dataType, errType) <- case lhsType of
    I.ANamedType tDefId -> do
      d <- checkTDef2 tDefId
      let fqn = un (I.tDefCommon d).fqn
      unless (fqn == "@stlib/errors:Result" || fqn == "@stlib/maybe:Maybe")
        $ throw ctx.et sr "Type is not Result/Maybe"
      case d of
        I.AnEnumDef2 x -> pure (must $ Ins.elems x.dataCons !! 0, Ins.elems x.dataCons !! 1)
        _ -> undefined
    _ -> throw ctx.et sr "Not an enum"

  unless (retErrType == errType) $ do
    (retErrType', errType') <- format2MaybeTypes "()" retErrType errType
    addError SevError ctx.et sr $ T.concat ["Error types do not match\nExpected ", retErrType', ", got ", errType']

  pure (I.BubbleExpr e'', dataType, sr)
