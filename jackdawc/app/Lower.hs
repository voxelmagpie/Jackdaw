-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use maybe" #-}
{-# HLINT ignore "Use head" #-}
module Lower (runLowerer) where

import AccessMode
import CTranspiler qualified as CTr
import Control.Monad (foldM, forM, forM_, replicateM, unless, void, when)
import Control.Monad.Reader (MonadIO (liftIO), MonadReader (ask), ReaderT (runReaderT))
import Data.Foldable (find)
import Data.HashTable.IO qualified as HT
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, mapMaybe)
import Data.Text qualified as T
import GHC.Stack (HasCallStack)
import Hir (MonadHirRead (getVDef))
import Hir qualified as H
import IdTypes (TextIdType (idFromText))
import InsOrdMap qualified as Ins
import Lir qualified as L
import Names (Attribute (..), VName)
import Prelude2
import Primitives
import SrcLoc (SrcRange (SrcRange), srcRangeFirstChar, srcRangeLastChar, srcRangeOf)
import Tables (IntIdType (idFromInt, idToInt), IsValueNew (NewValue), UniqueTable, tblForEach, tblGet, uTblEmpty, uTblInsert'')

type LoM = ReaderT LowererState IO

data Ctx = Ctx
  { vars :: [(H.LocalVarUid, Variable)],
    continueBlock :: Maybe L.BlockId,
    breakBlock :: Maybe L.BlockId,
    catchBlock :: Maybe L.BlockId,
    inNoThrowFn :: Bool,
    returnType :: Maybe H.Type
  }

-- If varType is VarRefPtr then lirType is a pointer or slice struct
data Variable = Variable {varId :: L.VarId, lirType :: L.Type, varType :: VarType}
  deriving (Show)

data VarType = VarVal | VarSmallConstRefVal | VarRefPtr
  deriving (Show, Eq)

findVar :: (HasCallStack) => Ctx -> H.LocalVarUid -> Variable
findVar ctx uid = find (\(id, _) -> id == uid) ctx.vars & must' (uid, ctx.vars) & snd

runLowerer :: H.Ir -> Bool -> IO Text
runLowerer hir addDbgLineNumbers = do
  state <- newLowererState hir addDbgLineNumbers
  runReaderT lower state
  case state.trState of
    Left cSt -> runReaderT CTr.extract cSt
    _ -> error "TODO: LLVM"

lower :: (MonadLo m) => m ()
lower = do
  let go :: (MonadLo m) => H.VDefId -> m ()
      go id = do
        d <- H.getVDef id
        case d of
          H.AConstDef _ -> pure ()
          H.AFnDef f -> when f.c.reachableFromStart $ do
            deps <- H.getFnDeps id
            forM_ deps go
            visitFn id f
  H.loopOverVDefs go

getFnCName :: H.VDefId -> Text -> L.FnName
getFnCName vDefId name =
  L.FnName $ L.CName $ "f" <> tShow (idToInt vDefId) <> T.take 8 name

-- Gets the type of a function without lowering the function body
getFn :: (MonadLo m) => H.VDefId -> H.FnDef -> m (L.FnName, L.Type)
getFn vDefId vDef = do
  (_, n, cFnType) <- getFn' vDefId vDef
  pure (n, L.FnPtrType cFnType)

-- Gets the function type as well as information about the parameter variables (only needed when lowering the function body)
getFn' :: (MonadLo m) => H.VDefId -> H.FnDef -> m FnCacheData
getFn' vDefId vDef = do
  cached <- getFnFromCache vDefId
  case cached of
    Just x -> pure x
    _ -> do
      params <- forM (zip [0 :: Int ..] vDef.parameters)
        $ \(i, (a, t, n)) ->
          convertFnParamType (a, t) (vDef.isAccessor && i == 0)
            <&> \(t', vt) -> (t', vt, n)

      let paramsCTypes = fst3 <$> params

      retCType <-
        if vDef.isAccessor
          then do
            convertAccFnRetType (must vDef.returnType) <&> Just
          else
            forM vDef.returnType convertType

      let name = un $ fst vDef.c.name
          cFnType = L.FnType paramsCTypes vDef.isVarArgs retCType

      hasBody <- H.getFnDefBodyMaybe vDefId <&> isJust
      let cName =
            if hasBody
              then
                if name == "_kStart"
                  then
                    L.FnName $ L.CName "_kStart"
                  else
                    getFnCName vDefId name
              else
                L.FnName $ L.CName name

      let x = (params <&> \(a, b, c) -> (fst a, b, c), cName, cFnType)
      addFnToCache vDefId x
      pure x

visitFn :: (MonadLo m) => H.VDefId -> H.FnDef -> m ()
visitFn vDefId vDef = do
  (params, cName, cFnType) <- getFn' vDefId vDef

  bodyMaybe <- H.getFnDefBodyMaybe vDefId
  case bodyMaybe of
    Nothing ->
      addExternFunction cName cFnType
    Just s ->
      fnBodyVisited vDefId >>= \done -> unless done $ do
        markFnBodyVisited vDefId

        _ <- resetPerFnState
        parameterVars <- forM params
          $ \(lirType, varType, n) -> do
            id <- mkVarId lirType $ fromMaybe "" $ un <$> n
            pure $ Variable {varId = id, lirType = lirType, varType = varType}

        -- Function parameters are always the first variables
        let vars = zip ([0 ..] <&> H.LocalVarUid) parameterVars

        -- Add final return statement if needed (prevents empty block at end)

        let returnsVoid = isNothing vDef.returnType || vDef.isIterator
        let endsWithRetStmnt c =
              not (null c) && case must $ last c of
                (H.ReturnStmnt _ _, _) -> True
                _ -> False

        let ss = case fst s of
              (H.ReturnStmnt _ _, _) -> [fst s]
              (H.CodeBlockStmnt xs _, _) | endsWithRetStmnt xs -> [fst s]
              (_, sr) | returnsVoid -> [fst s, (H.ReturnStmnt Nothing [], sr)]
              (_, sr)
                | not vDef.isAccessor ->
                    [fst s, (H.ReturnStmnt (Just (H.UninitExpr $ must vDef.returnType, sr)) [], sr)]
              _ -> [fst s]

        --

        inNoThrowFn <- H.getVDef vDefId <&> (H.vDefCommon >>> (.attributes) >>> (Attribute "NoThrow" `elem`))
        _ <- visitStmnt (Ctx vars Nothing Nothing Nothing inNoThrowFn vDef.returnType) ss []

        blocksOrder <- getBlocksOrderRev <&> reverse

        blocks <-
          forM blocksOrder $ \id -> do
            getBlock id <&> (id,)

        varsRev <- getVarsRev

        let f =
              L.Function
                { dbgName = un $ fst vDef.c.name,
                  dbgFile = let SrcRange path _ _ = snd vDef.c.name in T.pack path,
                  sr = snd vDef.c.name,
                  cName = cName,
                  fnType = cFnType,
                  isCoroutine = vDef.isIterator,
                  vars = reverse varsRev,
                  blocks = blocks
                }

        addFunction f

convertConstant' :: (MonadLo m) => H.Constant -> m L.Constant
convertConstant' (c, t) = do
  cType <- convertType t
  case c of
    H.ConstNullPtr -> pure (L.ConstLit L.NullPtr, cType)
    H.ConstFnPtr id -> do
      vDef <- H.getVDef id
      (fnName, t') <- case vDef of
        H.AConstDef _ -> error "Not a fn"
        H.AFnDef f -> getFn id f
      pure (L.ConstLit $ L.ConstName $ un fnName, t')
    H.ConstExtern id -> do
      vDef <- H.getVDef id
      (cName, t') <- case vDef of
        H.AConstDef c' -> getExternGlobalConst id c'
        H.AFnDef _ -> error "Got a fn"
      pure (L.ConstLit $ L.ConstName cName, t')
    H.ConstBool b -> pure (L.ConstLit $ L.BoolLit b, cType)
    H.ConstFloatOrDouble d -> pure (L.ConstLit $ L.FloatOrDoubleLit d, cType)
    H.ConstInt i -> pure (L.ConstLit $ L.IntLit i, cType)
    H.ConstSizeof sizeOfType -> do
      sizeOfType' <- convertType sizeOfType
      assertM $ cType == L.NumPrimType i64t || cType == L.NumPrimType i32t
      pure (L.ConstSizeof sizeOfType', cType)
    H.ConstStructOrTuple cs -> do
      cs' <- forM cs convertConstant'
      pure (L.ConstStructUnion cs', cType)
    H.ConstArray elType cs -> do
      cs'@(List1 (_, innerType) _) <- forM (cs <&> (,elType)) convertConstant'
      pure (L.ConstArray (fst <$> cs') innerType, cType)
    H.ConstAddrOf target -> do
      id <- convertConstant' target >>= addConstant
      let l = L.ConstNameAddrOf $ L.CName $ "c" <> tShow (idToInt id)
      pure (L.ConstCastLit l cType, cType)
    H.ConstAddrOfArray0 target -> do
      id <- convertConstant' target >>= addConstant
      let l = L.ConstNameAddrOf $ L.CName $ "c" <> tShow (idToInt id)
      pure (L.ConstCastLit l cType, cType)
    H.ConstEnum idx -> do
      let tagType = case cType of L.UnionType (List1 x _) -> x; _ -> undefined
      pure (L.ConstStructUnion [(L.ConstLit $ L.IntLit $ fromIntegral idx, tagType)], cType)

-- Adds a constant to the LIR and returns the name
-- unless the constant is a literal value in which case an LExpr is returned
convertConstant :: (MonadLo m) => H.Constant -> m (Either L.LExpr L.CName, L.Type)
convertConstant c = do
  (c', t') <- convertConstant' c
  case c' of
    L.ConstLit l -> pure (Left l, t')
    _ -> do
      id <- addConstant (c', t')
      pure (Right $ L.CName $ "c" <> tShow (idToInt id), t')

getExternGlobalConst :: (MonadLo m) => H.VDefId -> H.ConstDef -> m (L.CName, L.Type)
getExternGlobalConst id c = do
  assertM $ isNothing c.value
  visited <- constVisited id
  cType <- convertType c.c.typ
  case visited of
    Just x ->
      pure (x, cType)
    _ -> do
      let n = L.CName $ un $ fst c.c.name
      markConstVisited id n
      addExternConstant n cType >> pure (n, cType)

instrVToLExpr :: (MonadLo m) => SrcRange -> L.Type -> L.InstrV' -> m L.LExpr
instrVToLExpr sr t e' = case e' of
  L.ILExpr l -> pure l
  _ -> do
    (x, _) <- addValInstr sr t e'
    pure $ L.LTmp x

visitAccessorExpr' :: (MonadLo m) => Ctx -> H.AccessorExpr -> m (L.LExpr, L.Type)
visitAccessorExpr' ctx e@(_, sr) = do
  (e', t) <- visitAccessorExpr ctx e
  instrVToLExpr sr t e' <&> (,t)

visitAccessorExpr :: (MonadLo m) => Ctx -> H.AccessorExpr -> m (L.InstrV', L.Type)
visitAccessorExpr ctx (hirExpr, sr) = case hirExpr of
  H.ALocalVarAccessorExpr e -> do
    let var = findVar ctx e.uid
    case var.varType of
      VarRefPtr ->
        pure (L.ILoadVar var.varId, var.lirType)
      _ ->
        pure (L.ILExpr $ L.LGetVarPtr var.varId, L.PtrType (Just var.lirType))
  H.ConstantAccessorExpr c -> do
    (a, cType) <- convertConstant c
    cName <- case a of
      Left (L.ConstName name) ->
        pure name
      Left (L.ConstIdLit id) ->
        pure $ L.CName $ "c" <> tShow (idToInt id)
      Left l -> do
        id <- addConstant (L.ConstLit l, cType)
        pure $ L.CName $ "c" <> tShow (idToInt id)
      Right cName ->
        pure cName
    pure (L.ILExpr $ L.ConstNameAddrOf cName, L.PtrType (Just cType))
  H.AFieldAccessorExpr e -> do
    (e', cType) <- visitAccessorExpr ctx e.expr
    case cType of
      L.PtrType (Just (L.StructType xs)) -> do
        let typ = xs !! fromIntegral e.index
            ptrType = L.PtrType (Just typ)
        case e' of
          L.ILExpr le -> pure (L.ILExpr $ L.LStructUnionElemPtr le (fromIntegral e.index), ptrType)
          _ -> pure (L.IStructUnionElemPtr e' (fromIntegral e.index), ptrType)
      L.PtrType (Just (L.ArrayType typ _)) -> do
        let ptrType = L.PtrType (Just typ)
        pure (L.IArrayIndexPtr e' (fromIntegral e.index), ptrType)
      _ -> error "Invalid type for index accessor"
  H.PtrDerefExpr e pointeeType -> do
    pointeeType' <- convertType pointeeType
    -- No-op since pointer value is used as the accessor pointer
    (i, _) <- visitExpr ctx e
    let t = L.PtrType $ Just pointeeType'
    addValInstrInstrV' sr t $ L.IBitCast i t
  H.AccessorCallExpr e -> do
    (e', fnType) <- visitExpr' ctx e.fn

    let retType = case fnType of
          L.FnPtrType f -> must f.ret
          _ -> error "Not a function type"

    self <- visitAccessorExpr' ctx e.selfArg
    args <- getFnArgs ctx e.args

    let callInstr = L.ICall e' $ fst <$> (self : (fst2Of3 <$> args))
    let argsDropFns = reverse $ mapMaybe thd3 args
    x <- addValInstrLExpr sr retType callInstr
    forM_ argsDropFns $ addInstr sr

    forM_ e.dropFnsIfMayThrow $ \ds -> do
      successBlk <- reserveBlockId
      (throwBlk, needGenOnThrow) <- getOnThrowBlockId (ctx.inNoThrowFn, ctx.catchBlock, ds)
      addInstr sr (L.ICheckForException' $ L.ICheckForException throwBlk successBlk)
      when needGenOnThrow $ mkOnThrowBlk ctx throwBlk ds sr
      addBlock' successBlk

    pure $ first L.ILExpr x
  H.DataConsUnsafeAccessorExpr e i -> do
    (e', t) <- visitAccessorExpr ctx e
    let t' = case t of
          L.PtrType (Just (L.UnionType ts)) ->
            case ts !! (i + 1) of
              L.StructType ts' -> L.PtrType (Just (ts' !! 1))
              _ -> undefined
          _ -> undefined
    x <- addValInstrLExpr sr t' $ L.IStructUnionElemPtr (L.IStructUnionElemPtr e' (i + 1)) 1
    pure $ first L.ILExpr x
  H.RawSliceToSliceExpr e pointeeType -> do
    pointeeType' <- convertType pointeeType
    (i, _) <- visitExpr' ctx e
    let ptrType = L.PtrType $ Just pointeeType'
    let t = L.StructType $ List1 ptrType $ [L.NumPrimType i64t]
    (x0, _) <- addValInstrLExpr sr ptrType $ L.IBitCast (L.ILExpr $ L.LStructUnionElem i 0) ptrType
    (x1, _) <- addValInstrLExpr sr (L.NumPrimType i64t) $ L.ILExpr $ L.LStructUnionElem i 1
    addValInstrInstrV' sr t $ L.IInitStruct (List1 x0 [x1]) t

visitExpr' :: (MonadLo m) => Ctx -> H.Expr -> m (L.LExpr, L.Type)
visitExpr' ctx e@(_, sr) = do
  (e', t) <- visitExpr ctx e
  instrVToLExpr sr t e' <&> (,t)

visitExpr :: (MonadLo m) => Ctx -> H.Expr -> m (L.InstrV', L.Type)
visitExpr ctx (hirExpr, sr) = case hirExpr of
  H.LoadConstantExpr c -> do
    (a, cType) <- convertConstant c
    pure $ (,cType) $ case a of
      Left l -> L.ILExpr l
      Right cName -> L.ILExpr $ L.ConstName cName
  H.MkTupleExpr e -> do
    xs <- forM (list2ToList1 e) $ visitExpr' ctx
    let t = L.StructType $ xs <&> snd
    pure (L.IInitStruct (xs <&> fst) t, t)
  H.AStructInitExpr x -> do
    es <- forM x.exprs $ visitExpr' ctx
    let xs = x.fieldIndexToExprsIndex <&> (es !!)
    let t = L.StructType $ xs <&> snd
    pure (L.IInitStruct (xs <&> fst) t, t)
  H.ArrayInitExpr es -> do
    es'@(List1 (_, elementType) _) <- forM es $ visitExpr' ctx
    let t = L.ArrayType elementType $ fromIntegral $ length es
    pure (L.IInitArray (es' <&> fst) t, t)
  H.DerefAccessorExpr hirAcExpr -> do
    (i, t) <- visitAccessorExpr ctx hirAcExpr
    case t of
      L.PtrType (Just t') -> pure (L.IPtrRead i, t')
      _ -> error "Not ptr"
  H.AGetFieldExpr e -> do
    (e', cType) <- visitExpr' ctx e.expr
    x <- case cType of
      L.StructType xs -> do
        pure (L.ILExpr $ L.LStructUnionElem e' e.index, xs !! e.index)
      L.ArrayType elementType _ ->
        pure (L.IArrayIndex (L.ILExpr e') (fromIntegral e.index), elementType)
      _ -> error "Invalid type for index accessor"
    case e.dropFn of
      Nothing -> pure ()
      Just id -> do
        varId <- mkVarId cType ""
        addInstr sr $ L.ISetVar varId (L.ILExpr e')
        dropFnVDef <- H.getVDef id
        (dropLirFn, _) <- case dropFnVDef of H.AConstDef _ -> undefined; H.AFnDef f -> getFn id f
        let i = L.ICallVoid' $ L.ICallVoid (L.ConstName $ un dropLirFn) [L.LGetVarPtr varId] False
        addInstr sr i
    pure x
  H.AGetFieldFromAccExpr e -> do
    (e', cType) <- visitAccessorExpr ctx e.expr
    case cType of
      L.PtrType (Just (L.StructType xs)) -> do
        let getPtr = L.IStructUnionElemPtr e' e.index
        pure (L.IPtrRead getPtr, xs !! e.index)
      L.PtrType (Just (L.ArrayType elementType _)) -> do
        let getPtr = L.IArrayIndexPtr e' (fromIntegral e.index)
        pure (L.IPtrRead getPtr, elementType)
      _ -> error "Invalid type for index accessor"
  H.AFnCallExpr e -> do
    (e', fnType) <- visitExpr' ctx e.fn

    let retType = case fnType of
          L.FnPtrType f -> must f.ret
          _ -> error "Not a function type"

    args <- getFnArgs ctx e.args
    let argsLExprs = fst3 <$> args
    let argsDropFns = reverse $ mapMaybe thd3 args -- For r-values taken as references
    x <- addValInstrLExpr sr retType (L.ICall e' argsLExprs)
    forM_ argsDropFns $ addInstr sr

    forM_ e.dropFnsIfMayThrow $ \ds -> do
      successBlk <- reserveBlockId
      (throwBlk, needGenOnThrow) <- getOnThrowBlockId (ctx.inNoThrowFn, ctx.catchBlock, ds)
      addInstr sr (L.ICheckForException' $ L.ICheckForException throwBlk successBlk)
      when needGenOnThrow $ mkOnThrowBlk ctx throwBlk ds sr
      addBlock' successBlk

    pure $ first L.ILExpr x
  H.ACondOpExpr e -> do
    (cond, _) <- visitExpr ctx e.condExpr

    blk <- getActiveBlock
    afterBlk <- reserveBlockId

    thenBlk <- addBlock
    (x, t) <- visitExpr' ctx e.thenExpr
    dst <- mkVarId t ""
    runDropFns ctx sr e.dropFnsForThen
    addInstr (snd e.thenExpr) $ L.ISetVar dst $ L.ILExpr x
    addInstr (snd e.thenExpr) $ L.IGoTo afterBlk

    elseBlk <- addBlock
    (y, t2) <- visitExpr' ctx e.elseExpr
    runDropFns ctx sr e.dropFnsForElse
    addInstr (snd e.elseExpr) $ L.ISetVar dst $ L.ILExpr y
    addInstr (snd e.elseExpr) $ L.IGoTo afterBlk

    assertM $ t == t2

    setActiveBlock blk
    addInstr sr $ L.IGoToIfElse cond thenBlk elseBlk

    addBlock' afterBlk
    pure (L.ILoadVar dst, t)
  H.BitCast e toType -> do
    (e', _) <- visitExpr ctx e
    toType' <- convertType toType
    pure (L.IBitCast e' toType', toType')
  H.APtrAddExpr x -> do
    pointeeType' <- convertType x.pointeeType
    (e, _) <- visitExpr ctx x.expr
    let ptrType = L.PtrType $ Just pointeeType'
    (e', _) <- addValInstrLExpr sr ptrType $ L.IBitCast e ptrType
    (i, _) <- visitExpr' ctx x.index
    addValInstrInstrV' sr (L.PtrType Nothing) $ L.IBitCast (L.ILExpr $ L.LAddPtr e' i) (L.PtrType Nothing)
  H.APtrSubExpr x -> do
    pointeeType' <- convertType x.pointeeType
    (e, _) <- visitExpr ctx x.expr
    let ptrType = L.PtrType $ Just pointeeType'
    (e', _) <- addValInstrLExpr sr ptrType $ L.IBitCast e ptrType
    (i, _) <- visitExpr' ctx x.index
    addValInstrInstrV' sr (L.PtrType Nothing) $ L.IBitCast (L.ILExpr $ L.LSubPtr e' i) (L.PtrType Nothing)
  H.AndExpr lhs rhs -> do
    afterBlk <- reserveBlockId

    dst <- mkVarId L.BoolType ""
    (lhs', _) <- visitExpr ctx lhs
    blk <- getActiveBlock

    blk1 <- addBlock
    (rhs', _) <- visitExpr ctx rhs

    addInstr sr $ L.ISetVar dst rhs'
    addInstr sr $ L.IGoTo afterBlk

    blk2 <- addBlock
    addInstr sr $ L.ISetVar dst $ L.ILExpr $ L.BoolLit False
    addInstr sr $ L.IGoTo afterBlk

    setActiveBlock blk
    addInstr sr $ L.IGoToIfElse lhs' blk1 blk2

    addBlock' afterBlk
    pure (L.ILoadVar dst, L.BoolType)
  H.OrExpr lhs rhs -> do
    afterBlk <- reserveBlockId

    dst <- mkVarId L.BoolType ""
    (lhs', _) <- visitExpr ctx lhs
    blk <- getActiveBlock

    blk1 <- addBlock
    addInstr sr $ L.ISetVar dst $ L.ILExpr $ L.BoolLit True
    addInstr sr $ L.IGoTo afterBlk

    blk2 <- addBlock
    (rhs', _) <- visitExpr ctx rhs
    addInstr sr $ L.ISetVar dst rhs'
    addInstr sr $ L.IGoTo afterBlk

    setActiveBlock blk
    addInstr sr $ L.IGoToIfElse lhs' blk1 blk2

    addBlock' afterBlk
    pure (L.ILoadVar dst, L.BoolType)
  H.PtrEqExpr lhs rhs -> do
    (lhs', _) <- visitExpr' ctx lhs
    (rhs', _) <- visitExpr' ctx rhs
    pure (L.ILExpr $ L.LEq lhs' rhs', L.BoolType)
  H.PtrNEqExpr lhs rhs -> do
    (lhs', _) <- visitExpr' ctx lhs
    (rhs', _) <- visitExpr' ctx rhs
    pure (L.ILExpr $ L.LNEq lhs' rhs', L.BoolType)
  H.MoveLocalVarExpr uid _ -> do
    let var = findVar ctx uid
    case var.varType of
      VarVal -> pure (L.ILoadVar var.varId, var.lirType)
      _ -> undefined
  H.AddressOfExpr e -> do
    -- Accessors are already stored as a pointer so this is a no-op
    (e', _) <- visitAccessorExpr ctx e
    addValInstrInstrV' sr (L.PtrType Nothing) $ L.IBitCast e' (L.PtrType Nothing)
  H.UninitExpr t -> do
    t' <- convertType t
    id <- newTmpId
    addInstr sr $ L.IAddUninitTmp id t'
    pure (L.ILExpr $ L.LTmp id, t')
  H.DataConsExpr enumType idx expr -> do
    enumType' <- convertType enumType
    (e, exprType) <- visitExpr' ctx expr

    id <- newTmpId
    addInstr sr $ L.IAddUninitTmp id enumType'

    tagTypeHir <- case enumType of
      H.ANamedType n -> H.getTDef2 n <&> \case H.AnEnumDef2 ed -> ed.tagType; _ -> undefined
      _ -> undefined
    tagType <- convertType tagTypeHir
    let xt = L.StructType $ List1 tagType [exprType]
    let (x, _) = (L.IInitStruct (List1 (L.IntLit $ fromIntegral idx) [e]) xt, xt)
    addInstr sr $ L.ISetUnion (L.LTmp id) (idx + 1) x

    pure (L.ILExpr $ L.LTmp id, enumType')
  H.ActiveDataConsExpr e -> do
    case e of
      Left e' -> do
        (e'', t) <- visitExpr' ctx e'
        let tagType = case t of L.UnionType ts -> list1Head ts; _ -> undefined
        addValInstrInstrV' sr tagType (L.ILExpr $ L.LStructUnionElem e'' 0)
      Right e' -> do
        (e'', t) <- visitAccessorExpr ctx e'
        let tagType = case t of L.PtrType (Just (L.UnionType ts)) -> list1Head ts; _ -> undefined
        addValInstrInstrV' sr tagType (L.IPtrRead $ L.IStructUnionElemPtr e'' 0)
  H.DataConsUnsafeAddrOfExpr e i -> do
    (e', t) <- visitExpr ctx e
    let t' = case t of
          L.PtrType (Just (L.UnionType ts)) ->
            case ts !! (i + 1) of
              L.StructType ts' -> L.PtrType (Just (ts' !! 1))
              _ -> undefined
          _ -> undefined
    x <- addValInstrLExpr sr t' $ L.IStructUnionElemPtr (L.IStructUnionElemPtr e' (i + 1)) 1
    pure $ first L.ILExpr x
  H.SliceAsRawExpr e -> do
    (i, _) <- visitAccessorExpr' ctx e
    let t = L.StructType $ List1 (L.PtrType Nothing) [L.NumPrimType i64t]
    (x0, _) <- addValInstrLExpr sr (L.PtrType Nothing) $ L.IBitCast (L.ILExpr $ L.LStructUnionElem i 0) (L.PtrType Nothing)
    (x1, _) <- addValInstrLExpr sr (L.NumPrimType i64t) $ L.ILExpr $ L.LStructUnionElem i 1
    addValInstrInstrV' sr t $ L.IInitStruct (List1 x0 [x1]) t
  H.BubbleExpr e dropFns -> do
    -- Get the Result/Maybe value
    (e', t) <- visitExpr' ctx e

    -- Extract types
    let (tagType, okType, tagAndErrType) = case t of
          L.UnionType ts -> (ts !! 0, okType', ts !! 2)
            where
              okType' = case ts !! 1 of L.StructType ts' -> ts' !! 1; _ -> undefined
          _ -> undefined

    -- Get tag value
    (tag, _) <- addValInstrLExpr sr tagType (L.ILExpr $ L.LStructUnionElem e' 0)

    -- Check if tag is 0 (Ok) or 1 (Err)
    tag1Blk <- reserveBlockId
    tag0Blk <- reserveBlockId
    addInstr (srcRangeLastChar sr) $ L.IGoToIfElse (L.ILExpr $ L.LNEq tag (L.IntLit 0)) tag1Blk tag0Blk

    -- Err
    addBlock' tag1Blk
    runDropFns ctx sr dropFns

    retType <- convertType $ must ctx.returnType
    id <- newTmpId
    addInstr sr $ L.IAddUninitTmp id retType -- Holds the union for the returned enum value
    case tagAndErrType of
      L.StructType _ -> do
        -- Result -> Result or MaybeError
        (errValue, _) <- addValInstrInstrV' sr tagAndErrType (L.ILExpr $ L.LStructUnionElem e' 2)
        addInstr sr $ L.ISetUnion (L.LTmp id) 2 errValue
      _ ->
        -- Maybe -> Maybe or IsError
        addInstr sr $ L.ISetUnion (L.LTmp id) 0 (L.ILExpr $ L.IntLit 1)

    addInstr sr $ L.IReturn $ L.ILExpr $ L.LTmp id

    -- Ok
    addBlock' tag0Blk
    x <- addValInstrLExpr sr okType $ L.ILExpr $ L.LStructUnionElem (L.LStructUnionElem e' 1) 1
    pure $ first L.ILExpr x

getFnArgs :: (MonadLo m) => Ctx -> [H.FnArg] -> m [(L.LExpr, L.Type, Maybe L.Instr')]
getFnArgs ctx args =
  forM args $ \case
    H.RValueArg ex ->
      visitExpr' ctx ex <&> \(a, b) -> (a, b, Nothing)
    H.RValueRefArg (ex@(_, sr), mode, dropFn) -> do
      (e, t) <- visitExpr' ctx ex

      let isCopyRef = mode == Shared && L.typeSizeEstimate t <= 16
      if isCopyRef && isNothing dropFn
        then
          -- Reference to an integer or something, nothing to do
          pure (e, t, Nothing)
        else do
          -- Value needs to be passed as a pointer so store it in a variable and take the address
          varId <- mkVarId t ""
          addInstr sr $ L.ISetVar varId $ L.ILExpr e
          let ptrType = L.PtrType (Just t)
          let ptrLit = L.LGetVarPtr varId
          case dropFn of
            Nothing ->
              pure (ptrLit, ptrType, Nothing)
            Just id -> do
              dropFnVDef <- H.getVDef id
              (dropLirFn, _) <- case dropFnVDef of H.AConstDef _ -> undefined; H.AFnDef f -> getFn id f
              let i = L.ICallVoid' $ L.ICallVoid (L.ConstName $ un dropLirFn) [ptrLit] False
              pure $ if isCopyRef then (e, t, Just i) else (ptrLit, ptrType, Just i)
    H.RefArg (acEx@(_, sr), mode) -> do
      (ptr, ptrType) <- visitAccessorExpr ctx acEx
      let pointeeTypeMaybe = case ptrType of
            L.PtrType (Just x) -> Just x
            L.StructType xs | length xs == 2 -> Nothing
            _ -> error "Not a ptr or slice"
      case pointeeTypeMaybe of
        Just pointeeType
          | mode == Shared && L.typeSizeEstimate pointeeType <= 16 ->
              addValInstrLExpr sr pointeeType (L.IPtrRead ptr) <&> \(a, b) -> (a, b, Nothing)
        _ -> do
          ptr' <- instrVToLExpr sr ptrType ptr
          pure (ptr', ptrType, Nothing)

-- Creates a code block to calls destructors and bubble the exception up to the caller
mkOnThrowBlk :: (MonadLo m) => Ctx -> L.BlockId -> [(H.LocalVarUid, H.VDefId)] -> SrcRange -> m ()
mkOnThrowBlk ctx throwBlk ds sr = do
  addBlock' throwBlk
  addOnThrowBlock (ctx.inNoThrowFn, ctx.catchBlock, ds) throwBlk
  if ctx.inNoThrowFn && isNothing ctx.catchBlock
    then do
      addInstr sr $ L.ICallVoid' $ L.ICallVoid (L.ConstName (L.CName "_panicExInNoThrow")) [] True
    else do
      runDropFns ctx sr ds
      case ctx.catchBlock of
        Just blk -> addInstr sr $ L.IGoTo blk
        _ -> addInstr sr L.IBubbleException

vDefIdToFnLit :: (MonadLo m) => H.VDefId -> m L.LExpr
vDefIdToFnLit id = do
  vDef <- H.getVDef id
  (fnName, _) <- case vDef of
    H.AConstDef _ -> error "Not a fn"
    H.AFnDef f -> getFn id f
  pure $ L.ConstName $ un fnName

runDropFns :: (MonadLo m, HasCallStack) => Ctx -> SrcRange -> [(H.LocalVarUid, H.VDefId)] -> m ()
runDropFns ctx sr ds = forM_ ds $ \(uid, varId) -> do
  let var = findVar ctx uid
  fn <- vDefIdToFnLit varId
  assertM $ var.varType == VarVal
  addInstr sr $ L.ICallVoid' $ L.ICallVoid fn [L.LGetVarPtr var.varId] False

visitDestructure :: (MonadLo m) => Ctx -> SrcRange -> L.LExpr -> L.Type -> H.Destructure -> m Ctx
visitDestructure ctx sr l t = \case
  H.NameDes uid name _ -> do
    varId <- mkVarId t $ un $ fst name
    addInstr sr $ L.ISetVar varId $ L.ILExpr l
    pure $ ctx {vars = (uid, Variable {varId = varId, lirType = t, varType = VarVal}) : ctx.vars}
  H.IgnoreDes dropFn -> do
    forM_ dropFn $ \id -> do
      fn <- vDefIdToFnLit id
      varId <- mkVarId t ""
      addInstr sr $ L.ISetVar varId $ L.ILExpr l
      addInstr sr $ L.ICallVoid' $ L.ICallVoid fn [L.LGetVarPtr varId] False
    pure ctx
  H.TupleDes ds -> do
    let ts = case t of L.StructType x -> toList x; _ -> undefined
    foldM
      (\c (i, t', d) -> visitDestructure c sr (L.LStructUnionElem l i) t' d)
      ctx
      (zip3 [0 :: Int ..] ts $ toList ds)
  H.ArrayDes ds -> do
    let t' = case t of L.ArrayType x _ -> x; _ -> undefined
    foldM
      ( \c (i, d) -> do
          (l', _) <- addValInstrLExpr sr t' (L.IArrayIndex (L.ILExpr l) i)
          visitDestructure c sr l' t' d
      )
      ctx
      (zip [0 ..] $ toList ds)
  H.AStructDes ds -> do
    let ts = case t of L.StructType x -> toList x; _ -> undefined
    foldM
      (\c (t', (d, fieldIdx)) -> visitDestructure c sr (L.LStructUnionElem l fieldIdx) t' d)
      ctx
      (zip ts $ toList ds)

visitRefDestructure :: (MonadLo m) => Ctx -> SrcRange -> L.LExpr -> L.Type -> H.Destructure -> m Ctx
visitRefDestructure ctx sr l t = \case
  H.NameDes uid name _ -> do
    varId <- mkVarId t $ un $ fst name
    addInstr sr $ L.ISetVar varId $ L.ILExpr l
    pure $ ctx {vars = (uid, Variable {varId = varId, lirType = t, varType = VarRefPtr}) : ctx.vars}
  H.IgnoreDes _ ->
    pure ctx
  H.TupleDes ds -> do
    let ts = case t of L.PtrType (Just (L.StructType x)) -> toList x; _ -> undefined
    foldM
      ( \c (i, t', d) -> do
          let t'' = L.PtrType (Just t')
          let x = L.LStructUnionElemPtr l i
          visitRefDestructure c sr x t'' d
      )
      ctx
      (zip3 [0 :: Int ..] ts $ toList ds)
  H.ArrayDes ds -> do
    let t' = case t of L.PtrType (Just (L.ArrayType x _)) -> x; _ -> undefined
    let t'' = L.PtrType (Just t')
    foldM
      ( \c (i, d) -> do
          (l', _) <- addValInstrLExpr sr t'' (L.IArrayIndexPtr (L.ILExpr l) i)
          visitRefDestructure c sr l' t'' d
      )
      ctx
      (zip [0 ..] $ toList ds)
  H.AStructDes ds -> do
    let ts = case t of L.PtrType (Just (L.StructType x)) -> toList x; _ -> undefined
    foldM
      ( \c (t', (d, fieldIdx)) -> do
          let x = L.LStructUnionElemPtr l fieldIdx
          visitRefDestructure c sr x t' d
      )
      ctx
      (zip ts $ toList ds)

visitVarStmnt :: (MonadLo m) => Ctx -> SrcRange -> H.Destructure -> H.Expr -> m Ctx
visitVarStmnt ctx sr d e = case d of
  (H.NameDes uid name _) -> do
    (e', t) <- visitExpr ctx e
    varId <- mkVarId t $ un $ fst name
    addInstr sr $ L.ISetVar varId e'
    pure ctx {vars = (uid, Variable {varId = varId, lirType = t, varType = VarVal}) : ctx.vars}
  (H.IgnoreDes Nothing) -> do
    _ <- visitExpr' ctx e
    pure ctx
  _ -> do
    (e', t) <- visitExpr' ctx e
    visitDestructure ctx sr e' t d

-- Returns True if last statement was a terminator
visitStmnt :: (MonadLo m) => Ctx -> [H.Statement] -> [(H.LocalVarUid, H.VDefId)] -> m Bool
visitStmnt ctx ((s', sr) : ss) dropVars = case s' of
  H.VarStmnt d e -> do
    ctx' <- visitVarStmnt ctx sr d e
    visitStmnt ctx' ss dropVars
  H.UninitVarStmnt uid name _ hirType -> do
    t <- convertType hirType
    varId <- mkVarId t $ un name
    let ctx' = ctx {vars = (uid, Variable {varId = varId, lirType = t, varType = VarVal}) : ctx.vars}
    visitStmnt ctx' ss dropVars
  H.AnAssignmentStmnt s -> do
    (v, _) <- visitExpr' ctx s.value
    (ptrLit, _) <- visitAccessorExpr' ctx s.lhs -- Produces a pointer

    -- Call drop fn after getting the value in case an exception is thrown
    forM_ s.lhsDestructor $ \id -> do
      fn <- vDefIdToFnLit id
      addInstr sr $ L.ICallVoid' $ L.ICallVoid fn [ptrLit] False

    addInstr sr $ L.IPtrWrite' $ L.IPtrWrite {ptr = ptrLit, value = v}
    visitStmnt ctx ss dropVars
  H.FnCallStmnt e -> do
    isNoReturn <- case fst e.fn of
      H.LoadConstantExpr (H.ConstFnPtr id, _) -> H.getVDef id <&> \d -> Attribute "NoReturn" `elem` (H.vDefCommon d).attributes
      H.LoadConstantExpr (H.ConstExtern id, _) -> H.getVDef id <&> \d -> Attribute "NoReturn" `elem` (H.vDefCommon d).attributes
      _ -> pure False

    (e', _) <- visitExpr' ctx e.fn
    args <- getFnArgs ctx e.args
    let argsLExprs = fst3 <$> args
    let argsDropFns = reverse $ mapMaybe thd3 args -- For r-values taken as references
    _ <- addInstr sr $ L.ICallVoid' $ L.ICallVoid e' argsLExprs isNoReturn
    forM_ argsDropFns $ addInstr sr

    case e.dropFnsIfMayThrow of
      Just ds -> do
        successBlk <- reserveBlockId
        (throwBlk, needGenOnThrow) <- getOnThrowBlockId (ctx.inNoThrowFn, ctx.catchBlock, ds)
        addInstr sr (L.ICheckForException' $ L.ICheckForException throwBlk successBlk)
        when needGenOnThrow $ mkOnThrowBlk ctx throwBlk ds sr
        addBlock' successBlk
      _ -> pure ()

    visitStmnt ctx ss dropVars
  H.ExprStmnt e destructor -> do
    (e', t) <- visitExpr' ctx e
    forM_ destructor $ \id -> do
      fn <- vDefIdToFnLit id
      varId <- mkVarId t ""
      addInstr sr $ L.ISetVar varId $ L.ILExpr e'
      addInstr sr $ L.ICallVoid' $ L.ICallVoid fn [L.LGetVarPtr varId] False
    visitStmnt ctx ss dropVars
  H.AnIfElseStmnt s -> do
    afterBlk <- reserveBlockId

    (cond, _) <- visitExpr ctx s.cond
    blk <- getActiveBlock

    thenBlk <- addBlock
    thenTerm <- visitStmnt ctx [s.thenStmnt] s.dropFnsForThen
    unless thenTerm $ addInstr (srcRangeLastChar $ snd s.thenStmnt) $ L.IGoTo afterBlk

    case s.elseStmntMaybe of
      Just x -> do
        elseBlk <- addBlock
        elseTerm <- visitStmnt ctx [x] s.dropFnsForElse
        unless elseTerm $ addInstr (srcRangeLastChar sr) $ L.IGoTo afterBlk
        setActiveBlock blk
        addInstr (srcRangeFirstChar $ snd s.thenStmnt) $ L.IGoToIfElse cond thenBlk elseBlk
      _ -> do
        setActiveBlock blk
        addInstr (srcRangeFirstChar $ snd s.thenStmnt) $ L.IGoToIfElse cond thenBlk afterBlk

    addBlock' afterBlk
    visitStmnt ctx ss dropVars
  H.LoopStmnt s -> do
    innerBlock <- reserveBlockId
    afterBlk <- reserveBlockId
    addInstr sr $ L.IGoTo innerBlock

    addBlock' innerBlock
    _ <- visitStmnt ctx {continueBlock = Just innerBlock, breakBlock = Just afterBlk} [s] []
    addInstr (srcRangeLastChar sr) $ L.IGoTo innerBlock

    addBlock' afterBlk
    visitStmnt ctx ss dropVars
  H.BreakStmnt dropVars' -> do
    runDropFns ctx sr dropVars'
    addInstr sr $ L.IGoTo $ must ctx.breakBlock
    pure True
  H.ContinueStmnt dropVars' -> do
    runDropFns ctx sr dropVars'
    addInstr sr $ L.IGoTo $ must ctx.continueBlock
    pure True
  H.CodeBlockStmnt inner dropVars' -> do
    term <- visitStmnt ctx inner dropVars'
    if term
      then
        pure True
      else
        visitStmnt ctx ss dropVars
  H.ReturnStmnt e dropVars' -> do
    i <- case e of
      Just x -> do
        (x', _) <- visitExpr' ctx x
        pure $ L.IReturn (L.ILExpr x')
      Nothing -> do
        pure L.IReturnVoid

    runDropFns ctx sr dropVars'
    addInstr sr i
    pure True
  H.AccessorReturnStmnt x dropVars' -> do
    (x', _) <- visitAccessorExpr' ctx x
    runDropFns ctx sr dropVars'
    addInstr sr $ L.IReturn (L.ILExpr x')
    visitStmnt ctx [] dropVars
  H.YieldStmnt x dropVars' -> do
    (x', _) <- visitExpr ctx x

    nextBlk <- reserveBlockId
    errBlk <- reserveBlockId

    addInstr sr $ L.IYield' $ L.IYield x' nextBlk errBlk

    addBlock' errBlk
    runDropFns ctx sr dropVars'
    addInstr sr L.IReturnVoid

    addBlock' nextBlk
    visitStmnt ctx ss dropVars
  H.AccessorYieldStmnt x dropVars' -> do
    (x', _) <- visitAccessorExpr ctx x

    nextBlk <- reserveBlockId
    errBlk <- reserveBlockId

    addInstr sr $ L.IYield' $ L.IYield x' nextBlk errBlk

    addBlock' errBlk
    runDropFns ctx sr dropVars'
    addInstr sr L.IReturnVoid

    addBlock' nextBlk
    visitStmnt ctx ss dropVars
  H.AForEachLoopStmnt x -> do
    let isAccessor = case x.varMode of Move -> False; _ -> True

    fnName <- getVDef x.iterFn <&> \case H.AFnDef f -> un $ fst f.c.name; _ -> undefined
    let coName = getFnCName x.iterFn fnName

    args <- case x.args of
      Left as ->
        getFnArgs ctx as
      Right (_, self, as) -> do
        -- Accessor iterator
        self' <- visitAccessorExpr' ctx self
        as' <- getFnArgs ctx as
        pure $ (fst self', snd self', Nothing) : as'
    let argsDropFns = thd3 <$> args

    -- Iterator variables and resume counter is stored in this local variable
    -- CoroutineState refers to a struct that will be generated by the C transpiler
    let coType = L.CoroutineState coName
    coVar <- mkVarId coType ""
    addInstr sr $ L.ISetVar coVar $ L.IInitCoroutine coName (fst3 <$> args)

    loopStartBlock <- reserveBlockId
    innerBlock <- reserveBlockId
    abortBlk <- reserveBlockId
    afterBlk <- reserveBlockId
    addInstr sr $ L.IGoTo loopStartBlock

    addBlock' loopStartBlock
    yieldType <- case x.yieldType of
      H.SliceType t -> convertType t <&> lirSliceTypeOf
      _ -> convertType x.yieldType <&> \t -> if isAccessor then L.PtrType (Just t) else t
    valueVar <- mkVarId yieldType "" -- Iterator yielded value stored here
    let step = L.IStepCoroutine coName (L.LGetVarPtr coVar) (L.LGetVarPtr valueVar)

    (gotValue, _) <- addValInstrLExpr sr L.BoolType $ L.IStepCoroutine' step

    case x.onIterThrowDropFns of
      Just ds -> do
        successBlk <- reserveBlockId
        (throwBlk, needGenOnThrow) <- getOnThrowBlockId (ctx.inNoThrowFn, ctx.catchBlock, ds)
        addInstr sr (L.ICheckForException' $ L.ICheckForException throwBlk successBlk)
        when needGenOnThrow $ mkOnThrowBlk ctx throwBlk ds sr
        addBlock' successBlk
      _ ->
        -- Iterator is @NoThrow
        pure ()

    addInstr sr $ L.IGoToIfElse (L.ILExpr gotValue) innerBlock afterBlk

    addBlock' innerBlock

    -- Destructure the yielded value
    ctx' <- do
      (v, _) <- addValInstrLExpr sr yieldType $ L.ILoadVar valueVar
      if isAccessor
        then
          visitRefDestructure ctx sr v yieldType x.var
        else
          visitDestructure ctx sr v yieldType x.var

    -- Loop body
    _ <-
      visitStmnt
        ctx'
          { continueBlock = Just loopStartBlock,
            breakBlock = Just abortBlk
          }
        [x.body]
        x.dropFns
    addInstr (srcRangeLastChar sr) $ L.IGoTo loopStartBlock

    addBlock' abortBlk
    addInstr (srcRangeLastChar sr) $ L.IAbortCoroutine (L.ILExpr $ L.LGetVarPtr coVar) coName
    addInstr (srcRangeLastChar sr) $ L.IGoTo afterBlk

    addBlock' afterBlk
    forM_ (reverse $ catMaybes argsDropFns) $ addInstr (srcRangeLastChar sr)
    visitStmnt ctx ss dropVars
  H.AForLoopStmnt x -> do
    ctx' <- foldM (\c (d, e) -> visitVarStmnt c sr d e) ctx x.vars

    checkBlock <- reserveBlockId
    innerBlock <- reserveBlockId
    afterBlk <- reserveBlockId
    continueBlk <- reserveBlockId
    addInstr sr $ L.IGoTo checkBlock

    addBlock' checkBlock
    (l, _) <- visitExpr ctx' x.cond
    addInstr (snd x.cond) $ L.IGoToIfElse l innerBlock afterBlk

    addBlock' innerBlock
    _ <- visitStmnt ctx' {continueBlock = Just continueBlk, breakBlock = Just afterBlk} [x.innerStmnt] []
    addInstr (srcRangeLastChar sr) $ L.IGoTo continueBlk

    addBlock' continueBlk
    _ <- visitStmnt ctx' x.assignments []
    let asSr =
          if null x.assignments
            then
              srcRangeFirstChar (snd x.innerStmnt)
            else
              srcRangeOf x.assignments x.assignments
    addInstr asSr $ L.IGoTo checkBlock

    addBlock' afterBlk
    runDropFns ctx' sr x.dropFns
    visitStmnt ctx ss dropVars
  H.MatchStmnt _ e branches -> do
    afterBlk <- reserveBlockId

    (e', matchExprType, tag) <- case e of
      Left e' -> do
        (e'', t) <- visitExpr' ctx e'
        pure (e'', t, L.LStructUnionElem e'' 0)
      Right e' -> do
        (e'', t) <- visitAccessorExpr' ctx e'
        (tag, _) <- addValInstrLExpr sr (L.NumPrimType i32t) $ L.IPtrRead $ L.IStructUnionElemPtr (L.ILExpr e'') 0
        pure (e'', t, tag)

    caseBlocks <- replicateM (length branches) reserveBlockId

    forM_ (zip (toList branches) caseBlocks) $ \(br, block) -> do
      addMatchPatternBranch sr tag block br.pattern
    addInstr sr $ L.IPanic "Match cases not exhaustive"

    forM_ (zip (toList branches) caseBlocks) $ \(br, block) -> do
      addBlock' block
      -- Destructure the pattern
      ctx' <- case e of
        Left _ -> addPatternVars ctx br.patternSr e' matchExprType br.pattern
        Right _ -> addPatternRefVars ctx br.patternSr (L.ILExpr e') matchExprType br.pattern
      -- Branch code
      _ <- visitStmnt ctx' [br.code] br.dropFns
      addInstr (srcRangeLastChar $ snd br.code) $ L.IGoTo afterBlk

    addBlock' afterBlk
    visitStmnt ctx ss dropVars
  H.ThrowStmnt e dropVars' -> do
    (e', _) <- visitExpr ctx e
    runDropFns ctx sr dropVars'
    addInstr sr $ L.IThrow e'
    pure True
  H.TryCatchStmnt tryStmnt varMaybe catchStmnt -> do
    catchBlk <- reserveBlockId
    afterBlk <- reserveBlockId
    _ <- visitStmnt ctx {catchBlock = Just catchBlk} [tryStmnt] []
    addInstr sr $ L.IGoTo afterBlk
    addBlock' catchBlk
    case varMaybe of
      Just (uid, name, hirType) -> do
        t <- convertType hirType
        varId <- mkVarId t $ un name
        addInstr sr $ L.ISetVar varId L.ITakeException
        let ctx' = ctx {vars = (uid, Variable {varId = varId, lirType = t, varType = VarVal}) : ctx.vars}
        void $ visitStmnt ctx' [catchStmnt] []
        addInstr sr $ L.IGoTo afterBlk
      _ -> do
        void $ visitStmnt ctx [catchStmnt] []
        addInstr sr $ L.IGoTo afterBlk
    addBlock' afterBlk
    visitStmnt ctx ss dropVars
  H.BubbleStmnt e dropFns -> do
    -- Get the IsError/MaybeError value
    (e', t) <- visitExpr' ctx e

    -- Extract types
    let (tagType, tagAndErrType) = case t of
          L.UnionType ts -> (ts !! 0, ts !! 2)
          _ -> undefined

    -- Get tag value
    (tag, _) <- addValInstrLExpr sr tagType (L.ILExpr $ L.LStructUnionElem e' 0)

    -- Check if tag is 0 (Ok) or 1 (Err)
    retBlk <- reserveBlockId
    contBlk <- reserveBlockId
    addInstr (srcRangeLastChar sr) $ L.IGoToIfElse (L.ILExpr $ L.LNEq tag (L.IntLit 0)) retBlk contBlk

    -- Err
    addBlock' retBlk
    runDropFns ctx sr dropFns

    retType <- convertType $ must ctx.returnType
    id <- newTmpId
    addInstr sr $ L.IAddUninitTmp id retType -- Holds the union for the returned enum value
    case tagAndErrType of
      L.StructType _ -> do
        -- MaybeError -> MaybeError or Result
        (errValue, _) <- addValInstrInstrV' sr tagAndErrType (L.ILExpr $ L.LStructUnionElem e' 2)
        addInstr sr $ L.ISetUnion (L.LTmp id) 2 errValue
      _ ->
        -- IsError -> IsError or Maybe
        addInstr sr $ L.ISetUnion (L.LTmp id) 0 (L.ILExpr $ L.IntLit 1)
    addInstr sr $ L.IReturn $ L.ILExpr $ L.LTmp id

    -- Ok
    addBlock' contBlk
    visitStmnt ctx ss dropVars
  H.BorrowStatement _ uid name e -> do
    (e', t) <- visitAccessorExpr ctx e
    varId <- mkVarId t $ un name
    addInstr sr $ L.ISetVar varId e'
    let ctx' = ctx {vars = (uid, Variable {varId = varId, lirType = t, varType = VarRefPtr}) : ctx.vars}
    visitStmnt ctx' ss dropVars
visitStmnt ctx [] dropVars = do
  runDropFns ctx def dropVars
  pure False

addPatternVars :: (MonadLo m) => Ctx -> SrcRange -> L.LExpr -> L.Type -> H.Pattern -> m Ctx
addPatternVars ctx sr expr exprType = \case
  H.PatternAny dropFn -> do
    forM_ dropFn $ \id -> do
      fn <- vDefIdToFnLit id
      varId <- mkVarId exprType ""
      addInstr sr $ L.ISetVar varId $ L.ILExpr expr
      addInstr sr $ L.ICallVoid' $ L.ICallVoid fn [L.LGetVarPtr varId] False
    pure ctx
  H.PatternName uid name _ -> do
    varId <- mkVarId exprType $ un $ fst name
    addInstr sr $ L.ISetVar varId (L.ILExpr expr)
    let newVar = Variable varId exprType VarVal
    pure ctx {vars = (uid, newVar) : ctx.vars}
  H.PatternDataCons0 _ -> pure ctx
  H.PatternDataCons1 i innerPattern -> do
    let getExpr = L.LStructUnionElem (L.LStructUnionElem expr (i + 1)) 1
    let t = case exprType of
          L.UnionType ts -> case ts !! (i + 1) of
            L.StructType ts' -> ts' !! 1
            _ -> undefined
          _ -> undefined
    addPatternVars ctx sr getExpr t innerPattern

addPatternRefVars :: (MonadLo m) => Ctx -> SrcRange -> L.InstrV' -> L.Type -> H.Pattern -> m Ctx
addPatternRefVars ctx sr expr exprPtrType = \case
  H.PatternAny _ -> pure ctx
  H.PatternName uid name _ -> do
    varId <- mkVarId exprPtrType $ un $ fst name
    addInstr sr $ L.ISetVar varId expr
    let newVar = Variable varId exprPtrType VarRefPtr
    pure ctx {vars = (uid, newVar) : ctx.vars}
  H.PatternDataCons0 _ -> pure ctx
  H.PatternDataCons1 i innerPattern -> do
    let getPtr = L.IStructUnionElemPtr (L.IStructUnionElemPtr expr (i + 1)) 1
    let t = case exprPtrType of
          L.PtrType (Just (L.UnionType ts)) -> case ts !! (i + 1) of
            L.StructType ts' -> ts' !! 1
            _ -> undefined
          _ -> undefined
    addPatternRefVars ctx sr getPtr (L.PtrType (Just t)) innerPattern

patternNonConditional :: H.Pattern -> Bool
patternNonConditional = \case
  H.PatternAny _ -> True
  H.PatternName {} -> True
  _ -> False

addMatchPatternBranch :: (MonadLo m) => SrcRange -> L.LExpr -> L.BlockId -> H.Pattern -> m ()
addMatchPatternBranch sr tag block = \case
  H.PatternAny _ -> addInstr sr $ L.IGoTo block
  H.PatternName {} -> addInstr sr $ L.IGoTo block
  H.PatternDataCons0 i -> do
    (isEq, _) <- addValInstrLExpr sr L.BoolType $ L.ILExpr $ L.LEq tag $ L.IntLit $ fromIntegral i
    nextBlock <- reserveBlockId
    addInstr sr $ L.IGoToIfElse (L.ILExpr isEq) block nextBlock
    addBlock' nextBlock
  H.PatternDataCons1 i p | patternNonConditional p -> do
    (isEq, _) <- addValInstrLExpr sr L.BoolType $ L.ILExpr $ L.LEq tag $ L.IntLit $ fromIntegral i
    nextBlock <- reserveBlockId
    addInstr sr $ L.IGoToIfElse (L.ILExpr isEq) block nextBlock
    addBlock' nextBlock
  H.PatternDataCons1 i p -> do
    (isEq, _) <- addValInstrLExpr sr L.BoolType $ L.ILExpr $ L.LEq tag $ L.IntLit $ fromIntegral i
    nextCheck <- reserveBlockId
    nextBlock <- reserveBlockId
    addInstr sr $ L.IGoToIfElse (L.ILExpr isEq) nextCheck nextBlock
    addBlock' nextCheck
    addMatchPatternBranch sr tag block p
    addInstr sr $ L.IGoTo nextBlock
    addBlock' nextBlock

lirSliceTypeOf :: L.Type -> L.Type
lirSliceTypeOf t = L.StructType $ List1 (L.PtrType (Just t)) [L.NumPrimType i64t]

convertFnParamType :: (MonadLo m) => (AccessMode, H.Type) -> Bool -> m ((L.Type, L.IsRestrict), VarType)
convertFnParamType (mode, t) isAccParam0 = case t of
  H.SliceType t' -> do
    assertM $ mode /= Move
    t'' <- convertType t'
    pure ((lirSliceTypeOf t'', True), VarRefPtr)
  _ -> do
    paramInnerCType <- convertType t
    let sz = L.typeSizeEstimate paramInnerCType
    pure $ case mode of
      Shared | sz <= 16 && not isAccParam0 -> ((paramInnerCType, False), VarSmallConstRefVal)
      Move -> ((paramInnerCType, False), VarVal)
      Shared -> ((L.PtrType (Just paramInnerCType), True), VarRefPtr)
      Exclusive -> ((L.PtrType (Just paramInnerCType), True), VarRefPtr)

-- Converts to slice or pointer
convertAccFnRetType :: (MonadLo m) => H.Type -> m L.Type
convertAccFnRetType = \case
  H.SliceType t ->
    convertType t <&> lirSliceTypeOf
  t ->
    convertType t <&> \r -> L.PtrType (Just r)

convertType :: (MonadLo m, HasCallStack) => H.Type -> m L.Type
convertType hirType =
  case hirType of
    H.BoolType -> pure L.BoolType
    H.NumPrimType x -> pure $ L.NumPrimType x
    H.ANamedType id -> do
      td <- H.getTDef2 id
      case td of
        H.AStructDef2 s -> do
          fields <- forM (Ins.elems s.fields) $ \(t, _) -> do
            convertType t
          pure $ L.StructType $ must $ listToList1 fields
        H.AnEnumDef2 e -> do
          dataConsTypes <- forM (Ins.elems e.dataCons) $ \t -> forM t convertType

          tagType <- convertType e.tagType
          let dataConsTypes' =
                dataConsTypes <&> \case
                  Nothing -> tagType
                  Just t -> L.StructType $ List1 tagType [t]

          pure $ L.UnionType $ List1 tagType dataConsTypes'
    H.TupleType xs -> do
      xs' <- forM xs convertType
      pure $ L.StructType $ list2ToList1 xs'
    H.AFnType f -> do
      ps <- forM f.params $ flip convertFnParamType False
      r <- forM f.ret convertType
      pure $ L.FnPtrType $ L.FnType (fst <$> ps) f.isVarArgs r
    H.AnAccessorType f -> do
      ps <- forM (zip [0 :: Int ..] (toList f.params)) $ \(i, p) -> convertFnParamType p (i == 0)
      r <- convertAccFnRetType f.ret
      pure $ L.FnPtrType $ L.FnType (fst <$> ps) f.isVarArgs (Just r)
    H.AnIteratorType _ -> undefined
    H.AnAccessorIteratorType _ -> undefined
    H.PtrType _ ->
      pure $ L.PtrType Nothing
    H.ConstPtrType _ ->
      pure $ L.PtrType Nothing
    H.ArrayType t n -> do
      t' <- convertType t
      pure $ L.ArrayType t' n
    H.SliceType _ -> undefined

--
-- State
--

data LowererState = LowererState
  { hir :: H.Ir,
    trState :: Either CTr.TrState (),
    fnCache :: HashTable H.VDefId FnCacheData,
    lowererConstsVisited :: HashTable H.VDefId L.CName,
    fnBodiesVisited :: HashTable H.VDefId (),
    lowererNextFnUid :: IORef Int,
    nextBlockId :: IORef Int,
    nextTmpId :: IORef Int,
    varsRev :: IORef [(L.VarId, L.Type)],
    activeBlockId :: IORef L.BlockId,
    blocks :: IORef (HashTable L.BlockId [L.Instr]),
    blocksOrder :: IORef [L.BlockId],
    constants :: UniqueTable L.ConstId L.Constant,
    lineNum :: IORef Int,
    onThrowBlockCache :: IORef (HashTable OnThrowBlockCacheKey L.BlockId)
  }
  deriving (Generic)

type OnThrowBlockCacheKey = (Bool, Maybe L.BlockId, H.DropFns)

type FnCacheData = ([(L.Type, VarType, Maybe VName)], L.FnName, L.FnType)

newLowererState :: H.Ir -> Bool -> IO LowererState
newLowererState hir addDbgLineNumbers = do
  h <- HT.new
  h' <- HT.new
  cState <- CTr.mkTrState addDbgLineNumbers
  LowererState hir (Left cState)
    <$> HT.new
    <*> HT.new
    <*> HT.new
    <*> newIORef 0
    <*> newIORef 0
    <*> newIORef 0
    <*> newIORef []
    <*> newIORef (idFromInt 0)
    <*> newIORef h
    <*> newIORef []
    <*> uTblEmpty
    <*> newIORef 0
    <*> newIORef h'

class (H.MonadHirRead m) => MonadLo m where
  -- Returns True if on-throw block needs to be generated (was not in cache)
  getOnThrowBlockId :: OnThrowBlockCacheKey -> m (L.BlockId, Bool)

  fnBodyVisited :: H.VDefId -> m Bool
  markFnBodyVisited :: H.VDefId -> m ()
  addFunction :: L.Function -> m ()
  addExternFunction :: L.FnName -> L.FnType -> m ()
  addConstant :: L.Constant -> m L.ConstId
  addExternConstant :: L.CName -> L.Type -> m ()

  -- Takes variable name, may be blank
  mkVarId :: L.Type -> Text -> m L.VarId

  resetPerFnState :: m L.BlockId
  addInstr :: SrcRange -> L.Instr' -> m ()
  newTmpId :: m L.TmpId
  addValInstr :: SrcRange -> L.Type -> L.InstrV' -> m (L.TmpId, L.Type)
  addValInstrLExpr :: SrcRange -> L.Type -> L.InstrV' -> m (L.LExpr, L.Type)
  addValInstrInstrV' :: SrcRange -> L.Type -> L.InstrV' -> m (L.InstrV', L.Type)

  -- Ses the active block
  addBlock :: m L.BlockId

  -- Does not change the active block
  reserveBlockId :: m L.BlockId

  -- Ses the active block
  addBlock' :: L.BlockId -> m ()

  getActiveBlock :: m L.BlockId
  setActiveBlock :: L.BlockId -> m ()
  constVisited :: H.VDefId -> m (Maybe L.CName)
  markConstVisited :: H.VDefId -> L.CName -> m ()
  getFnFromCache :: H.VDefId -> m (Maybe FnCacheData)
  addFnToCache :: H.VDefId -> FnCacheData -> m ()
  addOnThrowBlock :: OnThrowBlockCacheKey -> L.BlockId -> m ()
  getVarsRev :: m [(L.VarId, L.Type)]
  getBlocksOrderRev :: m [L.BlockId]
  getBlock :: L.BlockId -> m [L.Instr]

instance MonadLo LoM where
  getOnThrowBlockId key = do
    s <- ask
    ht <- liftIO $ readIORef s.onThrowBlockCache
    idMaybe <- liftIO $ HT.lookup ht key
    case idMaybe of
      Just id -> pure (id, False)
      _ -> reserveBlockId <&> (,True)
  fnBodyVisited id = ask >>= \s -> liftIO $ HT.lookup s.fnBodiesVisited id <&> isJust
  markFnBodyVisited id = ask >>= \s -> liftIO $ HT.insert s.fnBodiesVisited id ()
  addFunction f =
    ask >>= \s -> case s.trState of
      Left cTr -> liftIO $ flip runReaderT cTr $ CTr.transpileFn (f.cName, f)
      _ -> pure ()
  addExternFunction cName fnType =
    ask >>= \s -> case s.trState of
      Left cTr -> liftIO $ flip runReaderT cTr $ CTr.transpileExternFn (cName, fnType)
      _ -> pure ()
  addConstant c = do
    s <- ask
    (id, _, isNew) <- liftIO $ uTblInsert'' c s.constants
    when (isNew == NewValue)
      $ case s.trState of
        Left cTr -> do
          liftIO $ flip runReaderT cTr $ CTr.transpileConst (id, c)
        _ -> pure ()
    pure id
  addExternConstant cName c =
    ask >>= \s -> case s.trState of
      Left cTr -> liftIO $ flip runReaderT cTr $ CTr.transpileExternConst (cName, c)
      _ -> pure ()
  mkVarId t name = do
    s <- ask
    vs <- liftIO $ readIORef s.varsRev
    let name' = if T.null name then "" else "_" <> T.take 10 name
    let id = idFromText $ "v" <> tShow (length vs) <> name'
    liftIO $ modifyIORef' s.varsRev ((id, t) :)
    pure id
  resetPerFnState = do
    h <- liftIO HT.new
    h' <- liftIO HT.new
    ask >>= \s ->
      liftIO
        $ writeIORef s.varsRev []
        >> writeIORef s.nextTmpId 0
        >> writeIORef s.nextBlockId 0
        >> writeIORef s.activeBlockId (idFromInt 0)
        >> writeIORef s.blocks h
        >> writeIORef s.blocksOrder []
        >> writeIORef s.onThrowBlockCache h'
    addBlock
  addInstr sr i = do
    blk <- getActiveBlock
    ht <- ask >>= \s -> liftIO $ readIORef s.blocks
    liftIO $ HT.mutate ht blk $ \xs -> (Just ((i, sr) : must xs), ())
  newTmpId = do
    s <- ask
    id <- liftIO $ readIORef s.nextTmpId <&> idFromInt
    liftIO $ modifyIORef' s.nextTmpId (+ 1)
    pure id
  addValInstr sr t i = do
    id <- newTmpId
    addInstr sr (L.IInstrV (i, id, t))
    pure (id, t)
  addValInstrLExpr sr b c = first L.LTmp <$> addValInstr sr b c
  addValInstrInstrV' sr b c = first (L.ILExpr . L.LTmp) <$> addValInstr sr b c
  addBlock = do
    s <- ask
    id <- liftIO $ idFromInt <$> readIORef s.nextBlockId
    liftIO $ modifyIORef' s.nextBlockId (+ 1)
    ht <- liftIO $ readIORef s.blocks
    liftIO $ HT.insert ht id []
    liftIO $ modifyIORef' s.blocksOrder (id :)
    setActiveBlock id
    pure id
  reserveBlockId = do
    s <- ask
    id <- liftIO $ idFromInt <$> readIORef s.nextBlockId
    liftIO $ modifyIORef' s.nextBlockId (+ 1)
    ht <- liftIO $ readIORef s.blocks
    liftIO $ HT.insert ht id []
    pure id
  addBlock' id = do
    s <- ask
    liftIO $ modifyIORef' s.blocksOrder (id :)
    setActiveBlock id
  getActiveBlock = ask >>= \s -> liftIO $ readIORef s.activeBlockId
  setActiveBlock id = ask >>= \s -> liftIO $ writeIORef s.activeBlockId id
  constVisited k = ask >>= \s -> liftIO $ HT.lookup s.lowererConstsVisited k
  markConstVisited k v = ask >>= \s -> liftIO $ HT.insert s.lowererConstsVisited k v
  getFnFromCache k = ask >>= \s -> liftIO $ HT.lookup s.fnCache k
  addFnToCache k v = ask >>= \s -> liftIO $ HT.insert s.fnCache k v
  addOnThrowBlock key x = do
    s <- ask
    ht <- liftIO $ readIORef s.onThrowBlockCache
    liftIO $ HT.insert ht key x
  getVarsRev = ask >>= \s -> liftIO $ readIORef s.varsRev
  getBlocksOrderRev = ask >>= \s -> liftIO $ readIORef s.blocksOrder
  getBlock id = do
    s <- ask
    ht <- liftIO $ readIORef s.blocks
    liftIO $ HT.lookup ht id <&> reverse . must

instance H.MonadHirRead LoM where
  getVDef id = ask >>= \s -> liftIO $ tblGet id s.hir.vDefs
  getFnDefBodyMaybe id = ask >>= \s -> liftIO $ HT.lookup s.hir.fnBodies id
  getFnDeps id = ask >>= \s -> liftIO $ HT.lookup s.hir.fnDeps id <&> fromMaybe []
  getTDef id = ask >>= \s -> liftIO $ tblGet id s.hir.tDefs
  loopOverVDefs f = ask >>= \s -> liftIO $ tblForEach (\(k, _) -> runReaderT (f k) s) s.hir.vDefs
  loopOverTSDefs f = ask >>= \s -> liftIO $ tblForEach (\(k, _) -> runReaderT (f k) s) s.hir.tDefs
  getTDef2 id = ask >>= \s -> liftIO $ must <$> HT.lookup s.hir.tDefs2 id
