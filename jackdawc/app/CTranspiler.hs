-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module CTranspiler where

import Control.Monad (forM)
import Control.Monad.Reader (MonadIO (liftIO), MonadReader (ask), ReaderT, asks)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (find)
import Data.Maybe (fromMaybe)
import Data.Text qualified as T
import IdTypes
import Lir qualified as L
import Prelude2
import Primitives
import SrcLoc (getLineNum)
import Tables (UniqueTable (..), uTblEmpty, uTblGetByValue, uTblInsert)

newtype TypeId = TypeId IntId
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable, Default, IdType, IntIdType)
  deriving anyclass (Newtype)

type TrM = ReaderT TrState IO

transpileFn :: (MonadTr m) => (L.FnName, L.Function) -> m ()
transpileFn (name, fn) = do
  lineNums <- lineNumbersEnabled

  let name' = un $ un name
  let dbgName
        | T.null fn.dbgName = ""
        | lineNums = "/* " <> fn.dbgName <> " */\n"
        | otherwise = "/* " <> fn.dbgFile <> ": " <> fn.dbgName <> " */\n"

  let line = if lineNums then "#line " <> tShow (getLineNum fn.sr) <> " \"" <> fn.dbgFile <> "\"\n" else ""

  setIsCoroutine fn.isCoroutine
  clearResumePoints
  if fn.isCoroutine
    then do
      yieldValuePtr <- transpileType $ L.PtrType (Just $ must fn.fnType.ret)
      -- Args are in the Co_ struct
      addDeclSrc $ con ["bool ", name', "(Co_", name', " * restrict, ", yieldValuePtr, ");\n"]

      blocks <- forM fn.blocks $ transpileBlock (Just L.BoolType) fn.blocks
      resumePoints <- getResumePoints
      let switchCases =
            zip [1 :: Int ..] resumePoints <&> \(r, (b0, b1)) ->
              con
                [ line,
                  "\t\tcase ",
                  tShow r,
                  ": if(out!=NULL){goto b",
                  tShow $ idToInt $ foldGoTo fn.blocks b0,
                  ";}else{goto b",
                  tShow $ idToInt $ foldGoTo fn.blocks b1,
                  ";};\n"
                ]

      let switch = con [line, "\tswitch (state->resumePoint) {\n", con switchCases, "\t}\n"]
      let body = con [switch, sep "\n" blocks, "\n}\n\n"]
      addFnSrc $ con [dbgName, line, "bool ", name', "(Co_", name', " * restrict state, ", yieldValuePtr, " restrict out) {\n", body]

      -- Put all variables (including parameters) into a struct
      let structStart = "typedef struct {\n\tint32_t resumePoint;\n"
      varsTypes <- forM fn.vars $ \(id, t) -> transpileType t <&> (id,)
      let structVars = con $ varsTypes <&> \(id, t) -> con ["\t", t, " ", idToText id, ";\n"]
      addTypeSrc $ con [structStart, structVars, "} Co_", name', ";\n\n"]
    else do
      paramsTypes <- forM fn.fnType.params transpileTypeMaybeRestrict
      let paramsCount = length fn.fnType.params
      let paramsNames = take paramsCount fn.vars <&> idToText . fst
      let params =
            (zip paramsTypes paramsNames <&> \(t, n) -> con [t, " ", n])
              & (\x -> if fn.fnType.isVarArgs then x ++ ["..."] else x)
              & sep ", "
              & (\x -> if T.null x then "void" else x)
      returnTypeSrc <- forM fn.fnType.ret transpileType <&> fromMaybe "void"
      let fnStart = con [returnTypeSrc, " ", name', " (", params, ") {\n"]
      vars <- forM (drop paramsCount fn.vars) $ \(id, t) ->
        transpileType t <&> \t' -> con [t', " ", idToText id, ";"]
      let vars' = if null vars then "" else "\t" <> con vars <> "\n"
      body <- forM fn.blocks $ transpileBlock fn.fnType.ret fn.blocks
      addFnSrc $ con [dbgName, line, fnStart, vars', sep "\n" body, "}\n\n"]

      -- Signature
      let paramsTypes' =
            paramsTypes
              & (\x -> if fn.fnType.isVarArgs then x ++ ["..."] else x)
              & sep ", "
              & (\x -> if T.null x then "void" else x)
      addDeclSrc $ con [returnTypeSrc, " ", name', " (", paramsTypes', ");\n"]

transpileExternFn :: (MonadTr m) => (L.FnName, L.FnType) -> m ()
transpileExternFn (name, cType) = do
  returnTypeSrc <- forM cType.ret transpileType <&> fromMaybe "void"
  paramsTypes <- forM cType.params transpileTypeMaybeRestrict
  let paramsTypes' =
        paramsTypes
          & (\x -> if cType.isVarArgs then x ++ ["..."] else x)
          & sep ", "
          & (\x -> if T.null x then "void" else x)
  addExternDeclSrc $ con [returnTypeSrc, " ", un $ un name, " (", paramsTypes', ");\n"]

transpileConst :: (MonadTr m) => (L.ConstId, L.Constant) -> m ()
transpileConst (id, arg@(_, constType)) = do
  t <- transpileType constType
  src <- transpileConstLiteral arg
  addDeclSrc $ con ["const ", t, " c", tShow $ idToInt id, " = ", src, ";\n"]

type IsCoroutine = Bool

lExprToText :: IsCoroutine -> L.LExpr -> Text
lExprToText isCo = \case
  L.IntLit y -> if y > 2147483647 then tShow y <> "u" else tShow y
  L.BoolLit y -> if y then "true" else "false"
  L.FloatOrDoubleLit y -> y
  L.NullPtr -> "NULL"
  L.ConstName name -> un name
  L.ConstNameAddrOf name -> "(&" <> un name <> ")"
  L.LTmp x -> "x" <> idToText x
  L.ConstIdLit id -> "c" <> tShow (idToInt id)
  L.LGetVarPtr v -> "(&" <> getVar isCo v <> ")"
  L.LAddPtr x i -> con ["(", lExprToText isCo x, " + ", lExprToText isCo i, ")"]
  L.LSubPtr x i -> con ["(", lExprToText isCo x, " - ", lExprToText isCo i, ")"]
  L.LEq x y -> con ["(", lExprToText isCo x, " == ", lExprToText isCo y, ")"]
  L.LNEq x y -> con ["(", lExprToText isCo x, " != ", lExprToText isCo y, ")"]
  L.LStructUnionElem x i -> con [lExprToText isCo x, ".x", tShow i]
  L.LStructUnionElemPtr x@(L.LStructUnionElemPtr _ _) i ->
    con ["(", stripFstLst $ lExprToText isCo x, ".x", tShow i, ")"]
  L.LStructUnionElemPtr x i -> con ["(&", lExprToText isCo x, "->x", tShow i, ")"]

stripFstLst :: Text -> Text
stripFstLst x = T.drop 1 x & T.take (length x - 2)

tmpIdToText :: L.TmpId -> Text
tmpIdToText x = "x" <> idToText x

transpileConstLiteral :: (MonadTr m) => L.Constant -> m Text
transpileConstLiteral (constVal, t) = do
  t' <- transpileType t
  let t'' = con ["(", t', ")"]
  case constVal of
    L.ConstLit l ->
      pure $ t'' <> lExprToText False l
    L.ConstStruct xs -> do
      xs' <- forM xs transpileConstLiteral
      pure $ con ["{", sep ", " xs', "}"]
    L.ConstArray xs el -> do
      xs' <- forM (toList xs <&> (,el)) transpileConstLiteral
      pure $ con ["{{", sep ", " xs', "}}"]
    L.ConstSizeof szOf -> do
      szOf' <- transpileType szOf
      pure $ con [t'', "sizeof(", szOf', ")"]
    L.ConstCastLit l _ -> do
      pure $ con [t'', "(", lExprToText False l, ")"]

transpileExternConst :: (MonadTr m) => (L.CName, L.Type) -> m ()
transpileExternConst (name, cType) = do
  t <- transpileTypeGetId cType
  -- Txx form of type is used here because the C syntax for constant pointers (not pointers-to-const) is weird
  addExternDeclSrc $ con ["extern const T", idToText t, " ", un name, ";\n"]

transpileInstrV :: (MonadTr m) => L.InstrV' -> m Text
transpileInstrV i = transpileInstrV' i <&> \x -> "(" <> x <> ")"

getVar :: IsCoroutine -> L.VarId -> Text
getVar True v = "(state->" <> idToText v <> ")"
getVar False v = idToText v

transpileInstrV' :: (MonadTr m) => L.InstrV' -> m Text
transpileInstrV' instr =
  isCoroutine >>= \isCo -> case instr of
    L.ILExpr l -> pure $ lExprToText isCo l
    L.ICall fn args -> pure $ con [lExprToText isCo fn, "(", sep ", " $ args <&> lExprToText isCo, ")"]
    L.ILoadVar v -> pure $ getVar isCo v
    L.IPtrRead (L.ILExpr (L.LGetVarPtr v)) -> pure $ getVar isCo v
    L.IPtrRead (L.IStructUnionElemPtr x i) -> transpileInstrV x <&> \x' -> con [x', "->x", tShow i]
    L.IPtrRead (L.IArrayIndexPtr x i) -> transpileInstrV x <&> \x' -> con [x', "->x[", tShow i, "]"]
    L.IPtrRead (L.IArrayIndexPtr' x i) -> pure $ con [lExprToText isCo x, "->x[", lExprToText isCo i, "]"]
    L.IPtrRead x -> ("*" <>) <$> transpileInstrV x
    L.IIndexPtr x i -> pure $ con [lExprToText isCo x, "[", lExprToText isCo i, "]"]
    L.IStructUnionElemPtr x@(L.IStructUnionElemPtr _ _) i ->
      transpileInstrV' x <&> \x' -> con [x', ".x", tShow i]
    L.IStructUnionElemPtr x i -> transpileInstrV x <&> \x' -> con ["&", x', "->x", tShow i]
    L.IArrayIndex x i -> transpileInstrV x <&> \x' -> con [x', ".x[", tShow i, "]"]
    L.IArrayIndexPtr x i -> transpileInstrV x <&> \x' -> con ["&", x', "->x[", tShow i, "]"]
    L.IArrayIndex' x i -> pure $ con [lExprToText isCo x, ".x[", lExprToText isCo i, "]"]
    L.IArrayIndexPtr' x i -> pure $ con ["&", lExprToText isCo x, "->x[", lExprToText isCo i, "]"]
    L.IBitCast x t -> do t' <- transpileType t; x' <- transpileInstrV' x; pure $ con ["(", t', ") ", x']
    L.IInitStruct fields t -> do
      t' <- transpileType t
      pure $ con ["(", t', "){", sep "," $ toList fields <&> lExprToText isCo, "}"]
    L.IInitArray xs t -> do
      t' <- transpileType t
      pure $ con ["(", t', "){{", sep "," $ toList xs <&> lExprToText isCo, "}}"]
    L.ISizeOf szOf -> transpileType szOf <&> \szOf' -> con ["sizeof(", szOf', ")"]
    L.IInitCoroutine fnName args ->
      pure $ con ["(Co_", un $ un fnName, ") {0,", sep "," $ args <&> lExprToText isCo, "}"]
    L.IStepCoroutine' x ->
      pure $ con [un $ un x.co, "(", lExprToText isCo x.coPtr, ", ", lExprToText isCo x.outPtr, ")"]
    L.ITakeException -> pure "_takeException()"

foldGoTo :: [(L.BlockId, [L.Instr])] -> L.BlockId -> L.BlockId
foldGoTo allBlocks id = case blockIsFoldable $ snd $ must $ find (fst >>> (== id)) allBlocks of
  Nothing -> id
  Just id' -> foldGoTo allBlocks id'

blockIsFoldable :: [L.Instr] -> Maybe L.BlockId
blockIsFoldable b = case b of
  [(L.IGoTo id, _)] -> Just id
  _ -> Nothing

transpileBlock :: (MonadTr m) => Maybe L.Type -> [(L.BlockId, [L.Instr])] -> (L.BlockId, [L.Instr]) -> m Text
transpileBlock fnRetType allBlocks (blkId, b) = case blockIsFoldable b of
  Just _ -> pure ""
  Nothing -> do
    case b of
      [] -> pure () -- error "Empty block"
      xs -> case fst $ must $ last xs of
        L.IGoTo _ -> pure ()
        L.IGoToIfElse {} -> pure ()
        L.IPanic _ -> pure ()
        L.IThrow _ -> pure ()
        L.IReturn _ -> pure ()
        L.IReturnVoid -> pure ()
        L.IYield' _ -> pure ()
        L.ICallVoid' x | x.noReturn -> pure ()
        L.ICheckForException' _ -> pure ()
        L.IBubbleException -> pure ()
        _ -> error "Block does not end in terminator instruction"

    isCo <- isCoroutine
    srcLines' <- forM b $ \(instr, _) -> case instr of
      L.IInstrV (x', id, t) -> do
        t' <- transpileType t
        src <- transpileInstrV' x'
        pure [t', " ", tmpIdToText id, " = ", src, ";"]
      L.IAddUninitTmp id t -> do
        t' <- transpileType t
        pure [t', " ", tmpIdToText id, ";"]
      L.IGoTo blkId' -> do
        pure ["goto b", tShow $ idToInt $ foldGoTo allBlocks blkId', ";"]
      L.IGoToIfElse cond thenBlk elseBlk -> do
        cond' <- transpileInstrV' cond
        pure
          [ "if (",
            cond',
            ") { goto b",
            tShow $ idToInt $ foldGoTo allBlocks thenBlk,
            "; } else { goto b",
            tShow $ idToInt $ foldGoTo allBlocks elseBlk,
            "; }"
          ]
      L.ICallVoid' x -> pure [lExprToText isCo x.fn, "(", args, ");"]
        where
          args = sep ", " $ x.args <&> lExprToText isCo
      L.IPtrWrite' L.IPtrWrite {ptr = (L.LGetVarPtr v), value} ->
        pure [getVar isCo v, " = ", lExprToText isCo value, ";"]
      L.IPtrWrite' x -> pure ["*", lExprToText isCo x.ptr, " = ", lExprToText isCo x.value, ";"]
      L.ISetVar v x -> do
        x' <- transpileInstrV' x
        pure [getVar isCo v, " = ", x', ";"]
      L.IReturn x -> do
        assertM $ not isCo
        x' <- transpileInstrV' x
        pure ["return ", x', ";"]
      L.IReturnVoid ->
        pure $ if isCo then ["return false;"] else ["return;"]
      L.IYield' x -> do
        i <- addResumePoint (x.continuationBlock, x.onFreeBlock)
        val <- transpileInstrV' x.yieldValue
        pure ["state->resumePoint = ", tShow i, ";\n\t*out = ", val, ";\n\treturn true;"]
      L.IAbortCoroutine i fnName ->
        transpileInstrV' i <&> \i' -> [un $ un fnName, "(", i', ", NULL);"]
      L.ISetUnion union idx x ->
        transpileInstrV' x <&> \x' -> [lExprToText isCo union, ".x", tShow idx, " = ", x', ";"]
      L.ISetUnionPtr union idx x ->
        transpileInstrV' x <&> \x' -> [lExprToText isCo union, "->x", tShow idx, " = ", x', ";"]
      L.IPanic x -> pure ["__panic(\"", x, "\");"]
      L.IThrow x -> do
        x' <- transpileInstrV' x
        case fnRetType of
          Just t -> do
            t' <- transpileType t
            pure ["thrownException=", x', ";\n\t{", t', " uninitRetVal; return uninitRetVal;}"]
          _ ->
            pure ["thrownException=", x', ";\n\treturn;"]
      L.IBubbleException ->
        case fnRetType of
          Just t -> do
            t' <- transpileType t
            pure ["{", t', " uninitRetVal; return uninitRetVal;}"]
          _ ->
            pure ["return;"]
      L.ICheckForException' L.ICheckForException {..} ->
        pure
          [ "if (unlikely(thrownException)) { goto b",
            tShow $ idToInt $ foldGoTo allBlocks onThrowGoto,
            "; } else { goto b",
            tShow $ idToInt $ foldGoTo allBlocks noThrowGoto,
            "; }"
          ]

    lineNums <- lineNumbersEnabled

    -- Add #line to each line after the first (first is b##:)
    let srcLines =
          zip3 srcLines' b (True : repeat False) <&> \(x, sr, isFirst) ->
            let ln = getLineNum sr
                blkLbl = if isFirst then con ["b", tShow (idToInt blkId), ":; "] else ""
             in if ln >= 1 && lineNums
                  then
                    ["#line ", tShow $ getLineNum sr, "\n\t", blkLbl] ++ x ++ ["\n"]
                  else
                    ["\t", blkLbl, if isFirst then "\n\t" else ""] ++ x ++ ["\n"]

    pure $ if null srcLines then con ["\t// empty block b", tShow (idToInt blkId), "\n"] else con (concat srcLines)

numPrimToCType :: NumPrim -> Text
numPrimToCType = \case
  AnIntT i -> con [sign, "int", sz, "_t"]
    where
      sz = tShow (intSizeToInt i.size)
      sign = case i.signed of Signed -> ""; Unsigned -> "u"
  AFloatT F32T -> "float"
  AFloatT F64T -> "double"

con :: [Text] -> Text
con = T.concat

sep :: Text -> [Text] -> Text
sep = T.intercalate

transpileTypeGetId :: (MonadTr m) => L.Type -> m TypeId
transpileTypeGetId typ = do
  idMaybe <- getTypeIDMaybe typ
  case idMaybe of
    Just x -> pure x
    _ -> do
      id <- addType typ
      let idt = "T" <> idToText id
      src <- case typ of
        L.NumPrimType x ->
          pure $ con ["typedef ", numPrimToCType x, " ", idt, ";\n\n"]
        L.BoolType ->
          pure $ con ["typedef bool ", idt, ";\n\n"]
        L.FnPtrType x -> do
          p <- forM x.params transpileTypeMaybeRestrict
          let p' = if x.isVarArgs then p ++ ["..."] else p
          r <- forM x.ret transpileType
          pure $ con ["typedef ", fromMaybe "void" r, " (*", idt, ")(", sep "," p', ");\n\n"]
        L.PtrType (Just x) -> do
          t <- transpileType x
          pure $ con ["typedef ", t, "* ", idt, ";\n\n"]
        L.PtrType Nothing -> do
          pure $ con ["typedef void * ", idt, ";\n\n"]
        L.StructType xs -> do
          xs' <- forM (toList xs) transpileType
          let fieldsIndexType = zip [0 :: Int ..] xs'
          let fields = fieldsIndexType <&> \(i, t) -> con ["\t", t, " x", tShow i, ";\n"]
          let td = con ["typedef struct {\n", con fields, "} ", idt, ";\n"]
          pure td
        L.UnionType xs -> do
          xs' <- forM (toList xs) transpileType
          let fieldsIndexType = zip [0 :: Int ..] xs'
          let fields =
                fieldsIndexType <&> \(i, t) ->
                  con ["\t", t, " x", tShow i, ";\n"]
          pure $ con ["typedef union {\n", con fields, "} ", idt, ";\n\n"]
        L.ArrayType t l -> do
          t' <- transpileType t
          pure $ con ["typedef struct {\n\t", t', " x[", tShow l, "];\n} ", idt, ";\n\n"]
        L.CoroutineState _ -> pure ""

      addTypeSrc src
      pure id

transpileType :: (MonadTr m) => L.Type -> m Text
transpileType typ = do
  id <- transpileTypeGetId typ

  pure $ case typ of
    L.NumPrimType x -> numPrimToCType x
    L.BoolType -> "bool"
    L.PtrType Nothing -> "void*"
    L.PtrType (Just (L.NumPrimType x)) -> numPrimToCType x <> "*"
    L.PtrType (Just L.BoolType) -> "bool*"
    L.CoroutineState (L.FnName (L.CName n)) -> "Co_" <> n
    _ -> "T" <> idToText id

-- For function reference parameters
transpileTypeMaybeRestrict :: (MonadTr m) => (L.Type, L.IsRestrict) -> m Text
transpileTypeMaybeRestrict x@(typ, _) = case x of
  (L.PtrType (Just pointee), True) -> do
    t <- transpileType pointee
    pure $ t <> "* restrict"
  (L.PtrType Nothing, True) -> pure "void * restrict"
  _ -> transpileType typ

data TrState = TrState
  { enableLineNumbers :: Bool,
    lineNumber :: IORef Int,
    types :: UniqueTable TypeId L.Type,
    typesRev :: IORef [Text],
    declsRev :: IORef [Text],
    externDeclsRev :: IORef [Text],
    fns :: IORef [Text],
    -- Per fn state
    isCoroutine :: IORef Bool,
    resumePointsRev :: IORef [(L.BlockId, L.BlockId)]
  }

mkTrState :: Bool -> IO TrState
mkTrState enableLineNumbers =
  TrState enableLineNumbers
    <$> newIORef 0
    <*> uTblEmpty
    <*> newIORef []
    <*> newIORef []
    <*> newIORef []
    <*> newIORef []
    <*> newIORef False
    <*> newIORef []

class (Monad m) => MonadTr m where
  addTypeSrc :: Text -> m ()
  getTypeIDMaybe :: L.Type -> m (Maybe TypeId)
  addType :: L.Type -> m TypeId
  addFnSrc :: Text -> m ()
  addDeclSrc :: Text -> m ()
  addExternDeclSrc :: Text -> m ()
  setIsCoroutine :: Bool -> m ()
  isCoroutine :: m Bool
  addResumePoint :: (L.BlockId, L.BlockId) -> m Int
  getResumePoints :: m [(L.BlockId, L.BlockId)]
  clearResumePoints :: m ()
  extract :: m Text
  lineNumbersEnabled :: m Bool

instance MonadTr TrM where
  addTypeSrc src = ask >>= \s -> liftIO $ modifyIORef' s.typesRev (src :)
  getTypeIDMaybe t = ask >>= \s -> liftIO $ uTblGetByValue t s.types
  addType t = ask >>= \s -> liftIO $ uTblInsert t s.types
  addFnSrc src = ask >>= \s -> liftIO $ modifyIORef' s.fns (src :)
  addDeclSrc src = ask >>= \s -> liftIO $ modifyIORef' s.declsRev (src :)
  addExternDeclSrc src = ask >>= \s -> liftIO $ modifyIORef' s.externDeclsRev (src :)
  setIsCoroutine x = ask >>= \s -> liftIO $ writeIORef s.isCoroutine x
  isCoroutine = ask >>= \s -> liftIO $ readIORef s.isCoroutine
  addResumePoint x = do
    s <- ask
    liftIO $ modifyIORef' s.resumePointsRev (x :)
    -- ResumePoint 0 is the start
    liftIO $ readIORef s.resumePointsRev <&> length
  getResumePoints = ask >>= \s -> liftIO $ readIORef s.resumePointsRev <&> reverse
  clearResumePoints = ask >>= \s -> liftIO $ writeIORef s.resumePointsRev []
  extract = do
    state <- ask
    typesRev <- liftIO $ readIORef state.typesRev
    externDeclsRev <- liftIO $ readIORef state.externDeclsRev
    declsRev <- liftIO $ readIORef state.declsRev
    fns <- liftIO $ readIORef state.fns
    let ts :: [[Text]] = [reverse typesRev, reverse externDeclsRev, reverse declsRev, ["\n"], reverse fns]
    pure $ con $ concat ts
  lineNumbersEnabled = asks (.enableLineNumbers)
