-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use head" #-}
{-# HLINT ignore "Use uncurry" #-}
{-# HLINT ignore "Use maybe" #-}
-- TODO Split into 2 modules, 1 module provides runTc and handles the borrow checker function
module Tc.Tc where

import AccessMode
import Ast qualified as A
import Control.Exception (try)
import Control.Monad (forM, forM_, unless, void, when)
import Control.Monad.Reader (ReaderT (runReaderT))
import Data.ByteString qualified as BS
import Data.Either (isLeft)
import Data.HashMap.Strict qualified as HM
import Data.IORef (readIORef)
import Data.List (init, uncons)
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Hir qualified
import InsOrdMap qualified as Ins
import Names
import Prelude2
import Primitives
import SrcLoc (SrcRange)
import Tc.Builtins
import Tc.Casts
import Tc.Ctx
import Tc.Ctx qualified as C
import Tc.Error (Error (..), ErrorSeverity (..), MonadTcError)
import Tc.Error qualified as E
import Tc.Fmt
import Tc.Hir
import Tc.MkCtx
import Tc.Names
import Tc.State
import Tc.TcErr
import Tc.TcIr qualified as I

-- If the error list is non-empty then the HIR is incomplete and should only be used for writing to a file for debugging
runTc :: TcFns TcM -> HashMap Namespace A.Ast -> Bool -> Bool -> IO ([E.Error], Maybe Hir.Ir)
runTc f asts forceCheckStLib uncheckedArithmetic = do
  state <- newTcState f typeIsCopyable
  res <- try @E.TcException $ runReaderT (typeCheck asts forceCheckStLib uncheckedArithmetic) state
  allErrsAndWarnings <- readIORef state.errorsRev <&> reverse
  let hasErrs = notNull $ filter (\(Error sev _ _ _) -> sev == SevError) allErrsAndWarnings
  pure $ if isLeft res || hasErrs then (allErrsAndWarnings, Nothing) else (allErrsAndWarnings, Just state.hir)

-- Type checks and generates HIR for all non-generic definitions
typeCheck :: (MonadTc m) => HashMap Namespace A.Ast -> Bool -> Bool -> m ()
typeCheck allAsts forceCheckStLib uncheckedArithmetic = do
  allAsts'' <- forM (toList allAsts) $ \(ns, ast) -> getImports allAsts ns ast <&> \i -> (ns, (ast, i))
  let allAsts' = HM.fromList allAsts''
  let primitivesAst = must $ HM.lookup (Namespace "@stlib/primitives") allAsts'
  let stLibAst = must $ HM.lookup (Namespace "@stlib/stlib") allAsts'
  let hashAst = must $ HM.lookup (Namespace "@stlib/hash") allAsts'
  let toStringAst = must $ HM.lookup (Namespace "@stlib/to_string") allAsts'
  let dropFnAst = must $ HM.lookup (VName "drop") (fst stLibAst).astVDefs.defs
  let equalFn = must $ HM.lookup (VName "equal") (fst stLibAst).astVDefs.defs
  let notEqualFn = must $ HM.lookup (VName "notEqual") (fst stLibAst).astVDefs.defs
  let cloneFn = must $ HM.lookup (VName "clone") (fst stLibAst).astVDefs.defs
  let hashFn = must $ HM.lookup (VName "hash") (fst hashAst).astVDefs.defs
  let addToHashFn = must $ HM.lookup (VName "addToHash") (fst hashAst).astVDefs.defs
  let toStringFn = must $ HM.lookup (VName "toString") (fst toStringAst).astVDefs.defs
  let addToStringFn = must $ HM.lookup (VName "addToString") (fst toStringAst).astVDefs.defs
  let tcIn = TcInputs allAsts' primitivesAst stLibAst hashAst toStringAst dropFnAst equalFn notEqualFn cloneFn hashFn addToHashFn toStringFn addToStringFn uncheckedArithmetic

  -- Functions reachable from _kStart
  do
    setStartedFromStart True
    let ast = stLibAst
    let namespace = Namespace "@stlib/stlib"
    let rootCtx = mkFileCtx namespace ast tcIn
    let d = must $ HM.lookup (VName "_kStart") (fst ast).astVDefs.defs
    _ <- visitVDef rootCtx rootCtx [] def (mkVFqn namespace (VName "start"), d) True
    setStartedFromStart False

  -- All other functions
  forM_ (toList allAsts') $ \(namespace, (rootAst, imports)) ->
    -- Skip stlib files unless forceCheckStLib == True.
    when (forceCheckStLib || not ("@stlib/" `T.isPrefixOf` un namespace)) $ do
      let rootCtx = mkFileCtx namespace (rootAst, imports) tcIn

      forM_ (reverse rootAst.requireStmntsRev) $ checkRequireStmnt rootCtx

      forM_ (toList rootAst.astVDefs.defs) $ \(name, d) ->
        when (null (A.vDefCommon d).genericParams)
          $ void
          $ visitVDef rootCtx rootCtx def (snd (A.vDefCommon d).name) (mkVFqn namespace name, d) True

      forM_ (toList rootAst.tsDefs) $ \(name, astDef) -> do
        let isAlias = case astDef of A.ATypeAlias _ -> True; _ -> False
        let (astGp, sr) = let c = A.tsDefCommon astDef in (c.genericParams, snd c.name)

        when (null astGp) $ do
          let tFqn = mkTFqn namespace name
          lhsType <- getTSDefType rootCtx rootCtx def sr (tFqn, astDef)

          -- Don't check member functions for aliases to generic functions as some member functions
          -- might not be intended to be used for that given instantiation of the generic type and hence
          -- might not type check
          unless isAlias $ do
            x <- getVDefsInType tcIn lhsType
            forM_ x $ \(memberFns, lhsTFqn) -> do
              typeCtx <- getTypeCtx rootCtx def lhsType <&> must -- Type has value defs and therefore has a context
              forM_ (HM.toList memberFns.defs) $ \(name', def') -> do
                let c = A.vDefCommon def'
                when (null c.genericParams)
                  $ void
                  $ visitVDef
                    rootCtx
                    typeCtx
                    []
                    (snd c.name)
                    (VFqn $ un lhsTFqn <> "." <> un name', def')
                    True

  -- Type definitions that haven't been fully checked
  getQueuedTsDef2s >>= mapM_ checkTDef2

typeIsCopyable :: (MonadTc m) => I.Type -> m Bool
typeIsCopyable = \case
  I.BoolType -> pure True
  I.NumPrimType _ -> pure True
  I.ANamedType id -> do
    tsDef <- checkTDef2 id
    pure $ not $ case tsDef of I.AStructDef2 x -> x.nonCopyable; I.AnEnumDef2 x -> x.nonCopyable; I.AUnionDef2 _ -> False
  I.TupleType xs -> allM typeIsCopyable $ toList xs
  I.AFnType _ -> pure True
  I.AnAccessorType _ -> pure True
  I.AnIteratorType _ -> undefined
  I.AnAccessorIteratorType _ -> undefined
  I.PtrType _ -> pure True
  I.ConstPtrType _ -> pure True
  I.ArrayType elType _ -> typeIsCopyable elType
  I.SliceType _ -> pure False

checkRequireStmnt :: (MonadTc m) => Ctx -> A.RequireStmnt -> m ()
checkRequireStmnt ctx (A.RequireStmnt e) = do
  (c, act) <- getConstLitExprFn >>= \f -> f ctx (TypeHint bool) e
  unless (act == bool) $ throw ctx.et e "Expected boolean"
  unless (c == I.ConstBool True) $ throw ctx.et e "Assertion failed"

getBuiltinType :: (MonadTc m) => Ctx -> Namespace -> TName -> m I.Type
getBuiltinType ctx ns name = getGenericBuiltinType ctx ns name def

getGenericBuiltinType :: (MonadTc m) => Ctx -> Namespace -> TName -> [I.GenericArg'] -> m I.Type
getGenericBuiltinType ctx ns name gArgs = do
  let (ast, imports) = must $ HM.lookup ns ctx.tcIn.allAsts
  let ctx' = mkFileCtx ns (ast, imports) ctx.tcIn
  case HM.lookup name ast.tsDefs of
    (Just astTd) -> do
      getTSDefType ctx ctx' gArgs (snd (A.tsDefCommon astTd).name) (TFqn $ un ns <> ":" <> un name, astTd)
    _ -> error "Missing builtin type"

-- Gets the type of a function/constant without checking the function body
-- This is only used by visitVDef
getVDefType ::
  (MonadTc m) => Ctx -> Ctx -> Ctx -> [I.GenericArg'] -> SrcRange -> (VFqn, A.AnyVDef) -> m (I.VDefId, I.Type, I.AnyVDef)
getVDefType userCtx outerCtx ctx gArgs userSr (fqn, astDef) = do
  vDefMaybe <- getCachedVDef fqn ctx.genericParams
  case vDefMaybe of
    Just (id, d) ->
      pure (id, (I.vDefCommon d).typ, d)
    _ -> do
      let (VName name, sr') = (A.vDefCommon astDef).name
      let dbgName = ctx.et.location

      vDefVisited fqn ctx.genericParams >>= flip when (throw ctx.et sr' $ "Infinite loop getting type of " <> name)
      markVDefVisited fqn ctx.genericParams

      case astDef of
        A.AConstDef constDef -> do
          unless (length ctx.genericParams == length constDef.c.genericParams + length outerCtx.genericParams)
            $ throw userCtx.et userSr "Wrong number of generic arguments to constant definition"

          checkTemplateArgs userCtx constDef.c.genericParams gArgs

          t <- getType ctx constDef.typeExpr
          checkTypeHasRuntimeRepr ctx.et (snd constDef.typeExpr) t

          let typeGArg i = case ctx.genericParams !! i of I.TypeGenericArg t' -> t'; _ -> undefined
          let valGArg i = case ctx.genericParams !! i of I.ValueGenericArg x -> x; _ -> undefined

          e <- case constDef.expr of
            Just e -> do
              x <- getConstLitExprFn >>= \f -> f ctx (TypeHint t) e
              Just <$> iCastConstant t x
            -- Builtins
            _ -> case un fqn of
              "@stlib/stlib:uncheckedArithmetic" ->
                pure $ Just (Hir.ConstBool ctx.tcIn.uncheckedArithmetic, bool)
              "@stlib/stlib:sizeOf" -> do
                let arg = typeGArg 0
                pure $ Just (Hir.ConstSizeof arg, i32)
              "@stlib/stlib:typeName" -> do
                typeName <- formatType False (typeGArg 0)
                makeConstStringLit ctx NoHint typeName <&> Just
              "@stlib/stlib:hasMember" -> do
                fnName <- case valGArg 1 of
                  (I.ConstStructOrTuple cs1, t'') -> do
                    stringType <- getBuiltinType ctx (Namespace "@stlib/string") $ TName "String"
                    unless (t'' == stringType) $ throw userCtx.et userSr "Expected string"

                    -- Extract List from String
                    case cs1 !! 0 of
                      (I.ConstStructOrTuple cs2, _) -> do
                        -- Extract string data from constant List[U8]
                        let array = case cs2 !! 0 of (I.ConstAddrOfArray0 (x, _), _) -> x; _ -> undefined
                        let array' = case array of I.ConstArray _ x -> x; _ -> undefined
                        let u8s = toList array' <&> \case I.ConstInt i -> fromIntegral i; _ -> undefined
                        pure $ decodeUtf8 $ BS.pack (init u8s)
                      _ -> undefined
                  _ -> throw userCtx.et userSr "Expected string"

                exists <-
                  getAstTDefCommonFromType ctx.tcIn (typeGArg 0) <&> \case
                    Just c -> HM.member (VName fnName) c.vDefs.defs
                    _ -> False

                pure $ Just (Hir.ConstBool exists, bool)
              "@stlib/stlib:getFields" -> do
                fields <- case typeGArg 0 of
                  I.ANamedType id -> do
                    tDef <- checkTDef2 id
                    case tDef of
                      I.AStructDef2 s -> do
                        let fs = un <$> Ins.keys s.fields
                        forM fs $ makeConstStringLit ctx NoHint >>> fmap fst
                      _ -> pure def
                  I.TupleType xs ->
                    forM [0 .. (length xs - 1)] $ tShow >>> makeConstStringLit ctx NoHint >>> fmap fst
                  _ -> pure []
                --
                stringType <- getBuiltinType ctx (Namespace "@stlib/string") (TName "String")
                Just <$> makeConstListLit ctx stringType fields
              "@stlib/stlib:fieldsCount" -> do
                let t' = typeGArg 0

                i <- case t' of
                  I.ANamedType id -> do
                    checkTDef2 id <&> \case
                      I.AStructDef2 s -> fromIntegral $ length s.fields
                      _ -> 0
                  I.TupleType xs -> pure $ fromIntegral $ length xs
                  _ -> pure 0

                pure $ Just (I.ConstInt i, i32)
              "@stlib/stlib:typeIsCopyable" -> do
                typeIsCopyable (typeGArg 0) <&> \b -> Just (I.ConstBool b, bool)
              "@stlib/stlib:parameterCount" -> do
                n <- case ctx.genericParams !! 0 of
                  I.ValueGenericArg (_, I.AFnType ft) -> pure $ length ft.params
                  _ -> throw userCtx.et userSr "Expected function"
                pure $ Just (I.ConstInt $ fromIntegral n, i32)
              "@stlib/stlib:enumDataConsCount" -> do
                i <- case typeGArg 0 of
                  I.ANamedType id -> do
                    getTDef id <&> \case
                      I.AnEnumDef e -> fromIntegral e.dataConsCount
                      _ -> 0
                  _ -> pure 0

                pure $ Just (I.ConstInt i, i32)
              "@stlib/stlib:getDataCons" -> do
                fields <- case typeGArg 0 of
                  I.ANamedType id -> do
                    tDef <- checkTDef2 id
                    case tDef of
                      I.AnEnumDef2 ed -> do
                        let dcs = un <$> Ins.keys ed.dataCons
                        forM dcs $ makeConstStringLit ctx NoHint >>> fmap fst
                      _ -> pure def
                  _ -> pure []
                --
                stringType <- getBuiltinType ctx (Namespace "@stlib/string") (TName "String")
                Just <$> makeConstListLit ctx stringType fields
              "@stlib/stlib:dataConsTakesType" -> do
                let t' = typeGArg 0
                i <- case ctx.genericParams !! 1 of
                  I.ValueGenericArg (I.ConstInt i, _) -> pure i
                  _ -> throw userCtx.et userSr "Expected index integer"

                astDef' <- getAstTDefFromType ctx.tcIn t'
                case astDef' of
                  Just (A.AnEnumDef e) -> do
                    unless (i >= 0 && i < fromIntegral (length e.dataCons))
                      $ throw userCtx.et (gArgs !! 1) "Index out of range"
                    pure $ Just (I.ConstBool $ isJust $ snd3 $ e.dataCons !! fromIntegral i, bool)
                  _ -> throw userCtx.et (gArgs !! 0) "Not an enum"
              "@stlib/stlib:isArrayType" -> do
                let isArray = case typeGArg 0 of
                      I.ArrayType _ _ -> True
                      _ -> False
                pure $ Just (I.ConstBool isArray, bool)
              "@stlib/stlib:arrayLength" ->
                case typeGArg 0 of
                  I.ArrayType _ l -> pure $ Just (I.ConstInt $ fromIntegral l, i32)
                  _ -> throw userCtx.et (gArgs !! 0) "Not an array"
              "@stlib/stlib:typesEq" -> do
                pure $ Just (I.ConstBool $ typeGArg 0 == typeGArg 1, bool)
              "@stlib/stlib:typeInfo" -> do
                let t' = typeGArg 0
                typeMetaType <- getBuiltinType userCtx (Namespace "@stlib/stlib") (TName "TypeMeta")
                -- enum TypeMeta {
                --     0:struct_,
                --     1:enum_,
                --     2:union_,
                --     3:tuple,
                --     4:fn_,
                --     5:ptr,
                --     6:constPtr,
                --     7:array,
                --     8:number,
                --     9:boolType,
                --     10:slice
                -- }
                idx <- case t' of
                  I.ANamedType id -> do
                    getTDef id <&> \case
                      I.AStructDef _ -> 0
                      I.AnEnumDef _ -> 1
                      I.AUnionDef _ -> 2
                  I.TupleType _ -> pure 3
                  I.AFnType _ -> pure 4
                  I.AnAccessorType _ -> pure 4
                  I.AnIteratorType _ -> pure 4
                  I.AnAccessorIteratorType _ -> pure 4
                  I.PtrType _ -> pure 5
                  I.ConstPtrType _ -> pure 6
                  I.ArrayType _ _ -> pure 7
                  I.NumPrimType _ -> pure 8
                  I.BoolType -> pure 9
                  I.SliceType _ -> pure 10
                pure $ Just (I.ConstEnum idx, typeMetaType)
              _ -> do
                unless (null ctx.genericParams) $ throw userCtx.et userSr "Unknown generic builtin"
                pure Nothing
          --

          case e of
            Just (_, act) ->
              unless (t == act) $ addError SevError ctx.et constDef.typeExpr "Explicit type does not match actual type"
            _ -> pure ()

          reachableFromStart <- getStartedFromStart
          let c =
                I.AConstDef
                  $ I.ConstDef
                    { c =
                        I.VDefCommon
                          { name = constDef.c.name,
                            dbgName = dbgName,
                            fqn = fqn,
                            typ = t,
                            genericArgs = ctx.genericParams,
                            reachableFromStart = reachableFromStart,
                            attributes = constDef.c.attributes
                          },
                      value = e <&> fst
                    }
          id <- addVDef c
          pure (id, t, c)
        A.AFnDef fnDef -> do
          when (isJust fnDef.retType && Attribute "NoReturn" `elem` fnDef.c.attributes)
            $ addError SevError ctx.et fnDef.c.name "Functions which return a value cannot be @NoReturn"

          unless (length ctx.genericParams == length fnDef.c.genericParams + length outerCtx.genericParams)
            $ throw userCtx.et userSr
            $ "Wrong number of generic arguments to "
            <> un (fst fnDef.c.name)

          checkTemplateArgs ctx fnDef.c.genericParams gArgs

          when (fnDef.isVarArgs && Attribute "Unsafe" `notElem` fnDef.c.attributes)
            $ addError SevError ctx.et fnDef.c.name "Var-args requires @Unsafe"

          when (fnDef.isVarArgs && isJust fnDef.code)
            $ addError SevError ctx.et fnDef.c.name "Var-args is for extern functions only"

          when (fnDef.isVarArgs && null fnDef.parameters)
            $ addError SevError ctx.et fnDef.c.name "Must have at least once parameter before var-args"

          when (fnDef.isIterator && isNothing fnDef.code)
            $ addError SevError ctx.et fnDef.c.name "Iterators cannot be extern"

          -- Get fn type
          p <- forM fnDef.parameters $ \(n, mode, typeExpr) -> do
            t <- getType ctx typeExpr
            when (mode == Move) $ checkTypeHasRuntimeRepr ctx.et (snd typeExpr) t
            pure (mode, fmap fst n, t)
          let p' = p <&> outerOf3
          let pNames = fnDef.parameters <&> fst3
          let parameters = zip p' pNames <&> \((m, t), n) -> (m, t, fst <$> n)

          r <- forM fnDef.retType $ \t -> do
            t' <- getType ctx t
            unless fnDef.isAccessor $ checkTypeHasRuntimeRepr ctx.et (snd t) t'
            pure t'

          fnType <-
            if fnDef.isAccessor
              then do
                r' <- case r of Just x -> pure x; _ -> throw ctx.et fnDef.c.name "Accessors cannot return void"
                p'' <- case uncons $ parameters <&> fst2Of3 of
                  Just (x, xs) -> pure $ List1 x xs
                  _ -> throw ctx.et fnDef.c.name "Accessors must take at least one parameter"

                let accType = I.AccessorType p'' fnDef.isVarArgs r'
                pure $ if fnDef.isIterator then I.AnAccessorIteratorType accType else I.AnAccessorType accType
              else
                if fnDef.isIterator
                  then do
                    r' <- case r of Just x -> pure x; _ -> throw ctx.et fnDef.c.name "Iterators cannot return void"
                    pure
                      $ I.AnIteratorType
                      $ I.IteratorType {params = parameters <&> fst2Of3, ret = r'}
                  else
                    pure
                      $ I.AFnType
                      $ I.FnType (parameters <&> fst2Of3) fnDef.isVarArgs r False

          reachableFromStart <- getStartedFromStart
          let f =
                I.AFnDef
                  $ I.FnDef
                    { c =
                        I.VDefCommon
                          { name = fnDef.c.name,
                            dbgName = dbgName,
                            fqn = fqn,
                            typ = fnType,
                            genericArgs = ctx.genericParams,
                            reachableFromStart = reachableFromStart,
                            attributes = fnDef.c.attributes
                          },
                      isAccessor = fnDef.isAccessor,
                      isIterator = fnDef.isIterator,
                      parameters = parameters,
                      isVarArgs = fnDef.isVarArgs,
                      returnType = r
                    }
          id <- addVDef f
          pure (id, fnType, f)

-- Gets the type of a constant/function
-- If this is a function then the body is checked
visitVDef ::
  (MonadTc m) => Ctx -> Ctx -> [I.GenericArg'] -> SrcRange -> (VFqn, A.AnyVDef) -> Bool -> m (I.VDefId, I.Type, I.AnyVDef)
visitVDef userCtx outerCtx gArgs userSr (fqn, astDef) allowUnsafe = do
  let (astGp, isIterator, isAccessor, defSr, defName, isUnsafe) =
        case astDef of
          A.AConstDef x -> (x.c.genericParams, False, False, snd x.c.name, fst x.c.name, Attribute "Unsafe" `elem` x.c.attributes)
          A.AFnDef x -> (x.c.genericParams, x.isIterator, x.isAccessor, snd x.c.name, fst x.c.name, Attribute "Unsafe" `elem` x.c.attributes)
  ctx <- makeVDefCtx userCtx outerCtx (fst <$> gArgs) astGp isIterator isAccessor defName isUnsafe userSr
  (vDefId, t, hirDef) <- getVDefType userCtx outerCtx ctx gArgs userSr (fqn, astDef)

  unless allowUnsafe
    $ when (Attribute "Unsafe" `elem` (Hir.vDefCommon hirDef).attributes)
    $ addError SevError userCtx.et userSr "Cannot use unsafe definition in safe context"

  visited <- fnDefBodyVisited vDefId
  if visited
    then pure (vDefId, t, hirDef)
    else case astDef of
      A.AConstDef _ ->
        pure (vDefId, t, hirDef)
      A.AFnDef fnDef -> do
        markFnDefBodyVisited vDefId

        let typeGArg i = case ctx.genericParams !! i of I.TypeGenericArg t' -> t'; _ -> undefined

        case fnDef.code of
          Just s -> do
            -- Extract information
            let (p', retType) = case hirDef of
                  I.AFnDef f -> (f.parameters <&> fst2Of3, f.returnType)
                  _ -> error "Not a fn type"

            -- Vars
            let newVars = zip (fst3 <$> fnDef.parameters) $ I.LocalVarUid <$> [0 ..]
            let newNamedTypedVars =
                  zip newVars p' <&> \((nameMaybe, uid), (_, t')) ->
                    case nameMaybe of
                      Nothing -> Nothing
                      Just x -> Just $ Variable {name = x, uidOrVal = Left uid, typ = t'}
            let ctx' =
                  ctx
                    { variables = reverse $ catMaybes newNamedTypedVars,
                      returnType = retType,
                      inUnsafeCode = Attribute "Unsafe" `elem` fnDef.c.attributes
                    }

            -- Store current function's state
            prevNextVarId <- peekNextLocalVarUid
            prevUsedItersList <- getUsedIters
            prevUsesThrowingFns <- getUsesThrowingFns

            -- Type check function
            resetLocalVarUid $ length newVars
            resetUsedItersList []
            setUsesThrowingFns False
            s' <- getCodeBlockStmntFn >>= \f -> f ctx' [s] []

            deps <- getUsedIters
            checkForDepLoops ctx' (snd fnDef.c.name) vDefId deps
            setFnDeps vDefId deps
            usesThrowingFns <- getUsesThrowingFns

            -- Restore current function's state
            resetUsedItersList prevUsedItersList
            resetLocalVarUid prevNextVarId
            setUsesThrowingFns prevUsesThrowingFns

            -- Borrow checking

            dropFns <- forM p' $ \(mode, varType) -> do
              if mode == Move
                then
                  getDropFn ctx.tcIn varType userSr
                else
                  pure Nothing

            bwCheckFn <- getBwCheckFn -- Breaks Haskell module dependency cycle
            (s'', terminates) <- bwCheckFn ctx.et s' (zip3 p' newVars dropFns) (snd fnDef.c.name) fnDef.isAccessor
            unless (isNothing retType || fnDef.isIterator || terminates)
              $ throw ctx'.et fnDef.c.name "Control reaches end of non-void function"

            addFnDefBody vDefId s'' (not usesThrowingFns)
          -- Builtins
          _ -> case un fqn of
            "@stlib/stlib:getField" -> do
              i <- case ctx.genericParams !! 1 of
                I.ValueGenericArg (I.ConstInt x, _) -> pure x
                _ -> throw userCtx.et (gArgs !! 0) "Expected integer"

              _ <- getFieldTypeAtIdx userCtx gArgs (typeGArg 0) i

              -- Create a function that returns a reference to the field
              let a' = Hir.ALocalVarAccessorExpr $ Hir.LocalVarAccessorExpr (I.LocalVarUid 0) (VName "x")
              let a = Hir.AFieldAccessorExpr $ Hir.FieldAccessorExpr (a', defSr) (fromIntegral i)
              addFnDefBody vDefId (Hir.AccessorReturnStmnt (a, defSr) [], defSr) True
            "@stlib/stlib:getFieldPtr" -> do
              i <- case ctx.genericParams !! 1 of
                I.ValueGenericArg (I.ConstInt x, _) -> pure x
                _ -> throw userCtx.et (gArgs !! 0) "Expected integer"

              fieldType <- getFieldTypeAtIdx userCtx gArgs (typeGArg 0) i

              let a = Hir.ALocalVarAccessorExpr $ Hir.LocalVarAccessorExpr (I.LocalVarUid 0) (VName "x")
              let a' = Hir.PtrDerefExpr (Hir.DerefAccessorExpr (a, defSr), defSr) fieldType
              let a'' = Hir.AFieldAccessorExpr $ Hir.FieldAccessorExpr (a', defSr) (fromIntegral i)
              addFnDefBody vDefId (Hir.ReturnStmnt (Just (Hir.AddressOfExpr (a'', defSr), defSr)) [], defSr) True
            "@stlib/stlib:getEnumActiveIndex" -> do
              case typeGArg 0 of
                I.ANamedType id -> do
                  getTDef id >>= \case
                    I.AnEnumDef _ -> pure ()
                    _ -> throw userCtx.et (gArgs !! 0) "Not an enum"
                _ -> throw userCtx.et (gArgs !! 0) "Not an enum"

              let getArg = Hir.ALocalVarAccessorExpr $ Hir.LocalVarAccessorExpr (Hir.LocalVarUid 0) (VName "x")
              addFnDefBody vDefId (Hir.ReturnStmnt (Just (Hir.ActiveDataConsExpr $ Right (getArg, defSr), defSr)) [], defSr) True
            "@stlib/stlib:getEnumIndexUnsafe" -> do
              i <- case ctx.genericParams !! 1 of
                I.ValueGenericArg (I.ConstInt x, _) -> pure x
                _ -> throw userCtx.et (gArgs !! 0) "Expected integer"

              case typeGArg 0 of
                I.ANamedType id -> do
                  checkTDef2 id >>= \case
                    I.AnEnumDef2 e -> do
                      unless (i >= 0 && i < fromIntegral (length e.dataCons))
                        $ throw userCtx.et (gArgs !! 1) "Index out of range"
                    _ -> throw userCtx.et (gArgs !! 0) "Not an enum"
                _ -> throw userCtx.et (gArgs !! 0) "Not an enum"

              let a = Hir.ALocalVarAccessorExpr $ Hir.LocalVarAccessorExpr (I.LocalVarUid 0) (VName "x")
              let a' = Hir.DataConsUnsafeAccessorExpr (a, defSr) (fromIntegral i)
              addFnDefBody vDefId (Hir.AccessorReturnStmnt (a', defSr) [], defSr) True
            "@stlib/stlib:getEnumIndexPtrUnsafe" -> do
              i <- case ctx.genericParams !! 1 of
                I.ValueGenericArg (I.ConstInt x, _) -> pure x
                _ -> throw userCtx.et (gArgs !! 0) "Expected integer"

              case typeGArg 0 of
                I.ANamedType id -> do
                  checkTDef2 id >>= \case
                    I.AnEnumDef2 e -> do
                      unless (i >= 0 && i < fromIntegral (length e.dataCons))
                        $ throw userCtx.et (gArgs !! 1) "Index out of range"
                    _ -> throw userCtx.et (gArgs !! 0) "Not an enum"
                _ -> throw userCtx.et (gArgs !! 0) "Not an enum"

              let a = Hir.ALocalVarAccessorExpr $ Hir.LocalVarAccessorExpr (I.LocalVarUid 0) (VName "x")
              let e = Hir.DataConsUnsafeAddrOfExpr (Hir.DerefAccessorExpr (a, defSr), defSr) (fromIntegral i)
              addFnDefBody vDefId (Hir.ReturnStmnt (Just (e, defSr)) [], defSr) True
            "@stlib/stlib:leak" -> do
              addFnDefBody vDefId (Hir.ReturnStmnt Nothing [], defSr) True
            "@stlib/primitives:Slice.asRawSlice" -> do
              let a = Hir.ALocalVarAccessorExpr $ Hir.LocalVarAccessorExpr (I.LocalVarUid 0) (VName "self")
              addFnDefBody vDefId (Hir.ReturnStmnt (Just (Hir.SliceAsRawExpr (a, defSr), defSr)) [], defSr) True
            _ -> pure ()
        pure (vDefId, t, hirDef)

getFieldTypeAtIdx :: (MonadTc m) => Ctx -> [I.GenericArg'] -> I.Type -> Integer -> m I.Type
getFieldTypeAtIdx userCtx gArgs t' i = case t' of
  I.ANamedType id -> do
    tDef <- checkTDef2 id
    case tDef of
      I.AStructDef2 s -> do
        unless (i >= 0 && i < fromIntegral (length s.fields))
          $ throw userCtx.et (gArgs !! 1) "Field index out of range"
        pure $ fst $ s.fields !! fromIntegral i
      _ -> do
        t'' <- formatType False t'
        throw userCtx.et (gArgs !! 0) $ t'' <> " does not have fields"
  I.TupleType xs -> do
    unless (i >= 0 && i < fromIntegral (length xs)) $ throw userCtx.et (gArgs !! 1) "Field index out of range"
    pure $ xs !! fromIntegral i
  _ -> do
    t'' <- formatType False t'
    throw userCtx.et (gArgs !! 0) $ t'' <> " does not have fields"

-- Checks that generic arguments match the naming convention
-- E.g. only types can be passed to 'T', only constant values to 'x'
checkTemplateArgs :: (MonadTc m) => Ctx -> [A.GenericParameter] -> [I.GenericArg'] -> m ()
checkTemplateArgs ctx astGp gArgs = do
  forM_ (zip astGp gArgs) $ \case
    (A.TypeGenericParameter _, (I.TypeGenericArg _, _)) -> pure ()
    (A.TypeGenericParameter _, (_, sr)) -> throw ctx.et sr "Expected a type"
    (A.ValueGenericParameter _, (I.ValueGenericArg _, _)) -> pure ()
    (A.ValueGenericParameter _, (_, sr)) -> throw ctx.et sr "Expected a constant value"

-- Gets the field / data constructor types, adds the StructDef2/EnumDef2 types to the HIR
checkTDef2 :: (MonadTc m) => I.TDefId -> m I.AnyTDef2
checkTDef2 id = do
  visited <- typeDefVisited id
  case visited of
    Td2Visited x -> pure x
    Td2Visiting (userCtx, sr) -> throw userCtx.et sr "Infinite loop in type definition"
    Td2Queued (ctx, _, _, astDef) -> do
      markTypeDefVisiting id
      let c = case astDef of
            A.ATypeAlias _ -> undefined
            A.ATypeDef d -> A.tDefCommon d
            A.AStructDef d -> A.tDefCommon d
            A.AnEnumDef d -> A.tDefCommon d
            A.AUnionDef d -> A.tDefCommon d

      let hasOnDrop = HM.member (VName "onDrop") c.vDefs.defs
      case astDef of
        A.ATypeAlias _ -> undefined
        A.ATypeDef _ -> undefined -- No fields so not queued by getTSDefType
        A.AStructDef structDef -> do
          let typeIsUnsafe' = Attribute "Unsafe" `elem` (A.tsDefCommon astDef).attributes

          fields <- forM structDef.fields $ \(sr', typeExpr, attribs) -> do
            t <- getType ctx {inUnsafeCode = typeIsUnsafe' || Attribute "Unsafe" `elem` attribs} typeExpr
            checkTypeHasRuntimeRepr ctx.et sr' t
            pure (t, attribs)

          nonCopyable <-
            if hasOnDrop
              then pure True
              else do
                fieldsCopy <- forM (Ins.elems fields <&> fst) typeIsCopyable
                pure $ not $ and fieldsCopy

          tDef <- getTDef id
          markTypeDefVisited id $ I.AStructDef2 $ I.StructDef2 (I.tDefCommon tDef) nonCopyable fields
        A.AnEnumDef enumDef -> do
          dataCons <- forM enumDef.dataCons $ \(sr', typeExprMaybe, attribs) -> do
            when (Attribute "Unsafe" `elem` attribs) $ error "TODO: unsafe enum data constructors"
            forM typeExprMaybe $ \typeExpr -> do
              t <- getType ctx typeExpr
              checkTypeHasRuntimeRepr ctx.et sr' t
              pure t

          nonCopyable <-
            if hasOnDrop
              then pure True
              else do
                fieldsCopy <- forM (Ins.elems dataCons) $ \t ->
                  forM t typeIsCopyable <&> fromMaybe True
                pure $ not $ and fieldsCopy

          let tagType
                | length dataCons <= 256 = u8
                | length dataCons <= 65536 = u16
                | otherwise = i32

          tDef <- getTDef id <&> \case I.AnEnumDef x -> x; _ -> undefined
          markTypeDefVisited id $ I.AnEnumDef2 $ I.EnumDef2 tDef tagType nonCopyable dataCons
        A.AUnionDef unionDef -> do
          dataCons <- forM unionDef.dataCons $ \(sr', typeExpr, _attribs) -> do
            t <- getType ctx typeExpr
            checkTypeHasRuntimeRepr ctx.et sr' t
            pure t

          tDef <- getTDef id <&> \case I.AUnionDef x -> x; _ -> undefined
          markTypeDefVisited id $ I.AUnionDef2 $ I.UnionDef2 tDef dataCons

getTSDefType ::
  (MonadTc m) =>
  Ctx ->
  Ctx ->
  [I.GenericArg'] ->
  SrcRange ->
  (TFqn, A.AnyTSDef) ->
  m I.Type
getTSDefType userCtx outerCtx gArgs sr (fqn, astDef) = do
  let isUnion = case astDef of A.AUnionDef _ -> True; _ -> False
  let c' = A.tsDefCommon astDef
  let typeIsUnsafe' = isUnion || Attribute "Unsafe" `elem` c'.attributes

  unless userCtx.inUnsafeCode
    $ when typeIsUnsafe'
    $ addError SevError userCtx.et sr "Cannot use unsafe type in safe context"

  let gArgs' = fst <$> gArgs
  tsDefMaybe <- getCachedTSDef fqn gArgs'
  case tsDefMaybe of
    Just (TsDefVisited x) -> do
      pure x
    Just TsDefVisiting ->
      throw userCtx.et sr $ "Infinite loop in " <> un (fst c'.name)
    Nothing -> do
      unless (length c'.genericParams == length gArgs)
        $ throw userCtx.et sr "Wrong number of generic arguments to type"

      checkTemplateArgs userCtx c'.genericParams gArgs

      let typeGArg i = case gArgs' !! i of I.TypeGenericArg t' -> t'; _ -> undefined

      case astDef of
        A.ATypeAlias alias -> do
          markTsDefVisiting fqn gArgs'
          t <- case alias.typ of
            Just t -> do
              ctx <-
                makeTSDefCtx
                  userCtx
                  outerCtx
                  fqn
                  alias.c.genericParams
                  gArgs'
                  Nothing
                  (fst alias.c.name)
                  typeIsUnsafe'
                  sr
              getType ctx t
            -- Builtins
            _ -> case un fqn of
              "@stlib/stlib:FieldType" -> do
                -- TODO Take field name strings as well
                let t' = typeGArg 0

                i <- case gArgs' !! 1 of
                  I.ValueGenericArg (I.ConstInt x, _) -> pure x
                  _ -> throw userCtx.et sr "Expected integer"

                getFieldTypeAtIdx userCtx gArgs t' i
              "@stlib/stlib:DataConsType" -> do
                -- TODO Take field name strings as well
                let t' = typeGArg 0

                i <- case gArgs' !! 1 of
                  I.ValueGenericArg (I.ConstInt x, _) -> pure x
                  _ -> throw userCtx.et sr "Expected integer"

                case t' of
                  I.ANamedType id ->
                    checkTDef2 id >>= \case
                      I.AnEnumDef2 e -> do
                        unless (i >= 0 && i < fromIntegral (length e.dataCons))
                          $ throw userCtx.et (gArgs !! 1) "Index out of range"
                        case e.dataCons !! fromIntegral i of
                          Just x -> pure x
                          _ -> throw userCtx.et (gArgs !! 0) "Data constructor does not have a type"
                      _ -> throw userCtx.et (gArgs !! 0) "Not an enum"
                  _ -> throw userCtx.et (gArgs !! 0) "Not an enum"
              "@stlib/stlib:ArrayElemType" ->
                case typeGArg 0 of
                  I.ArrayType el _ -> pure el
                  _ -> throw userCtx.et (gArgs !! 0) "Not an array"
              _ ->
                throw userCtx.et alias.c.name $ "Unknown builtin type alias: " <> un (fst alias.c.name)
          addTSDef' fqn gArgs' t
        _ -> do
          let c = case astDef of
                A.ATypeDef d -> A.tDefCommon d
                A.AStructDef d -> A.tDefCommon d
                A.AnEnumDef d -> A.tDefCommon d
                A.AUnionDef d -> A.tDefCommon d
          let name = fst c.c.name

          let tDefCommon =
                I.TDefCommon
                  { name = name,
                    fqn = fqn,
                    namespace = outerCtx.namespace,
                    genericArgs = gArgs',
                    attributes = (A.tsDefCommon astDef).attributes
                  }

          case astDef of
            A.ATypeDef td -> do
              unless (outerCtx.namespace == Namespace "@stlib/primitives")
                $ throw userCtx.et td.c.c.name "Builtin types are not valid here"
              x <- case un name of
                "Bool" -> addTSDef' fqn gArgs' I.BoolType
                "I8" -> addTSDef' fqn gArgs' i8
                "I16" -> addTSDef' fqn gArgs' i16
                "I32" -> addTSDef' fqn gArgs' i32
                "I64" -> addTSDef' fqn gArgs' i64
                "U8" -> addTSDef' fqn gArgs' u8
                "U16" -> addTSDef' fqn gArgs' u16
                "U32" -> addTSDef' fqn gArgs' u32
                "U64" -> addTSDef' fqn gArgs' u64
                "F32" -> addTSDef' fqn gArgs' f32
                "F64" -> addTSDef' fqn gArgs' f64
                "Array" -> do
                  let n = case gArgs' !! 1 of I.ValueGenericArg (n', _) -> n'; _ -> undefined
                  n'' <- case n of
                    I.ConstInt i -> if i > 0 && i <= 2147483647 then pure i else throw userCtx.et sr "Invalid array length"
                    _ -> throw userCtx.et sr "Expected integer"
                  let arrayType = I.ArrayType (typeGArg 0) $ fromIntegral n''
                  addTSDef' fqn gArgs' arrayType
                "Slice" ->
                  addTSDef' fqn gArgs' $ I.SliceType $ typeGArg 0
                _ -> throw userCtx.et td.c.c.name "Unrecognised builtin type"

              ctx <- makeTSDefCtx userCtx outerCtx fqn c.c.genericParams gArgs' (Just x) name typeIsUnsafe' sr
              addTypeCtx x ctx
              pure x
            --
            A.AStructDef structDef -> do
              forM_ (toList structDef.c.vDefs.defs) $ \(n, d) ->
                when (n `elem` Ins.keys structDef.fields)
                  $ addError SevError userCtx.et (A.vDefCommon d).name ("Member function " <> un n <> " has same name as field")

              ctx <- makeTSDefCtx userCtx outerCtx fqn structDef.c.c.genericParams gArgs' Nothing name typeIsUnsafe' sr

              (t, id) <- addTSDef fqn gArgs' $ I.AStructDef tDefCommon
              let ctx' = ctx {C.selfType = Just (fqn, t)}
              addTypeCtx t ctx'
              forM_ c.requireStmnts $ checkRequireStmnt ctx'
              queueTDefVisit id (ctx', userCtx, sr, astDef)
              -- Type checking continues in checkTDef2
              pure t
            --
            A.AnEnumDef enumDef -> do
              forM_ (toList enumDef.c.vDefs.defs) $ \(n, d) ->
                when (n `elem` Ins.keys enumDef.dataCons)
                  $ addError SevError userCtx.et (A.vDefCommon d).name ("Member function " <> un n <> " has same name as data constructor")

              ctx <- makeTSDefCtx userCtx outerCtx fqn enumDef.c.c.genericParams gArgs' Nothing name typeIsUnsafe' sr

              let canBeCastedToInt = all (isNothing . snd3) $ Ins.elems enumDef.dataCons

              (t, id) <-
                addTSDef fqn gArgs'
                  $ I.AnEnumDef
                  $ I.EnumDef tDefCommon canBeCastedToInt (length enumDef.dataCons)

              let ctx' = ctx {C.selfType = Just (fqn, t)}
              addTypeCtx t ctx'
              forM_ c.requireStmnts $ checkRequireStmnt ctx'
              queueTDefVisit id (ctx', userCtx, sr, astDef)
              -- Type checking continues in checkTDef2
              pure t
            --
            A.AUnionDef unionDef -> do
              forM_ (toList unionDef.c.vDefs.defs) $ \(n, d) ->
                when (n `elem` Ins.keys unionDef.dataCons)
                  $ addError SevError userCtx.et (A.vDefCommon d).name ("Member function " <> un n <> " has same name as data constructor")

              ctx <- makeTSDefCtx userCtx outerCtx fqn unionDef.c.c.genericParams gArgs' Nothing name typeIsUnsafe' sr

              (t, id) <-
                addTSDef fqn gArgs'
                  $ I.AUnionDef
                  $ I.UnionDef tDefCommon (length unionDef.dataCons)

              let ctx' = ctx {C.selfType = Just (fqn, t)}
              addTypeCtx t ctx'
              forM_ c.requireStmnts $ checkRequireStmnt ctx'
              queueTDefVisit id (ctx', userCtx, sr, astDef)
              -- Type checking continues in checkTDef2
              pure t

getGenArg :: (MonadTc m) => Ctx -> A.GenericArg -> m I.GenericArg'
getGenArg ctx (A.TypeGenericArg e@(_, sr)) = getType ctx e <&> \x -> (I.TypeGenericArg x, sr)
getGenArg ctx (A.ValueGenericArg e@(_, sr)) = getConstLitExprFn >>= \f -> f ctx NoHint e <&> \x -> (I.ValueGenericArg x, sr)

getNamespaceOrType :: (MonadTc m) => Ctx -> A.TypeExpr -> m (Either (Namespace, A.Ast, ImportsList) I.Type)
getNamespaceOrType ctx typeExpr@(astTypeExpr, sr) = case astTypeExpr of
  A.NamedType Nothing name Nothing ->
    lookupTypeName ctx name
      >>= \case
        NlNamespace x -> pure $ Left x
        NlTypeDef (outerCtx, fqn, astTypeDef) -> getTSDefType ctx outerCtx [] sr (fqn, astTypeDef) <&> Right
        NlType t -> pure $ Right t
  _ -> getType ctx typeExpr <&> Right

getNamespace :: (MonadTc m) => Ctx -> A.TypeExpr -> m (Namespace, A.Ast, ImportsList)
getNamespace ctx (astTypeExpr, sr) = case astTypeExpr of
  A.NamedType Nothing name gArgsMaybe -> do
    unless (null gArgsMaybe) $ throw ctx.et sr "Namespaces cannot be generic"
    lookupTypeName ctx name
      >>= \case
        NlNamespace x -> pure x
        _ -> throw ctx.et sr "Expected namespace, got type"
  _ -> throw ctx.et sr "Expected namespace"

getType :: (MonadTc m) => Ctx -> A.TypeExpr -> m I.Type
getType ctx (astTypeExpr, sr) = case astTypeExpr of
  A.NamedType (Just nsExpr) (name, _) gArgsMaybe -> do
    (ns, ast, astImports) <- getNamespace ctx nsExpr
    case HM.lookup name ast.tsDefs of
      Nothing -> throw ctx.et sr $ "No such definition: " <> un name
      Just astTypeDef -> do
        let outerCtx = mkFileCtx ns (ast, astImports) ctx.tcIn
        let fqn = mkTFqn ns name
        args <- forM (fromMaybe [] gArgsMaybe) $ getGenArg ctx
        getTSDefType ctx outerCtx args sr (fqn, astTypeDef)
  A.NamedType Nothing name gArgsMaybe -> do
    x <- lookupTypeName ctx name
    case x of
      NlTypeDef (outerCtx, fqn, astTypeDef) -> do
        args <- forM (fromMaybe [] gArgsMaybe) $ getGenArg ctx
        getTSDefType ctx outerCtx args sr (fqn, astTypeDef)
      NlType t ->
        pure t
      NlNamespace _ ->
        throw ctx.et sr "Expected type, got namespace"
  A.TupleType xs -> do
    xs' <- forM xs $ getType ctx
    pure $ I.TupleType xs'
  A.AFnType fnType -> do
    p <- forM fnType.params $ \(mode, e) -> do e' <- getType ctx e; pure (mode, e')
    r <- forM fnType.ret $ getType ctx
    pure $ I.AFnType $ I.FnType p fnType.isVarArgs r fnType.isNullable
  A.AnAccessorType fnType -> do
    p <- forM fnType.params $ \(mode, e) -> do e' <- getType ctx e; pure (mode, e')
    r <- getType ctx fnType.ret
    pure $ I.AnAccessorType $ I.AccessorType p fnType.isVarArgs r
  A.SelfType -> case ctx.selfType of
    Just (_, t) -> pure t
    _ -> throw ctx.et sr "Self type is not valid here"
  A.PtrType typeMaybe -> do
    unless ctx.inUnsafeCode $ addError SevError ctx.et sr "Cannot use pointers in safe code"
    t <- forM typeMaybe $ getType ctx
    pure $ I.PtrType t
  A.ConstPtrType typeExpr -> do
    t <- getType ctx typeExpr
    pure $ I.ConstPtrType t
  A.TypeOf e ->
    getExprFn >>= \f -> snd3 <$> f ctx NoHint e

-- Returns Nothing if the drop function is empty
getDropFn :: (MonadTc m) => TcInputs -> I.Type -> SrcRange -> m (Maybe I.DropFn)
getDropFn tcIn t sr = do
  noNeedToCheck <- typeIsCopyable t

  if noNeedToCheck
    then pure Nothing
    else do
      let astDef = tcIn.dropFn
      let ctx' = mkFileCtx (Namespace "@stlib/stlib") tcIn.stLibAst tcIn
      (id, _, _) <- visitVDef ctx' ctx' [(I.TypeGenericArg t, sr)] sr (VFqn "@stlib/stlib:drop", astDef) True
      body <- getFnDefBodyMaybe id
      case body of
        Nothing -> pure Nothing
        Just ((Hir.CodeBlockStmnt ss _, _), _) | null ss -> pure Nothing
        Just ((Hir.CodeBlockStmnt ss _, _), _) | length ss == 1 -> case ss !! 0 of
          (Hir.ReturnStmnt _ _, _) -> pure Nothing
          _ -> pure $ Just id
        _ -> pure $ Just id

getStructFields :: (MonadTc m) => Ctx -> SrcRange -> I.Type -> m (Ins.InsOrdMap VName (I.Type, [Attribute]))
getStructFields ctx sr = \case
  I.ANamedType id -> do
    td <- checkTDef2 id
    case td of
      I.AStructDef2 s -> pure s.fields
      _ -> throw ctx.et sr "Expected a struct type"
  _ -> throw ctx.et sr "Expected a struct type"

checkForDepLoops :: (MonadTc m) => Ctx -> SrcRange -> I.VDefId -> [I.VDefId] -> m ()
checkForDepLoops ctx sr id deps = do
  when (id `elem` deps) $ throw ctx.et sr "Dependency loop"
  forM_ deps $ \d -> do
    deps' <- getFnDeps d
    checkForDepLoops ctx sr id deps'

getVDefsInType ::
  (MonadTc m) =>
  TcInputs ->
  I.Type ->
  m (Maybe (A.VDefs, TFqn))
getVDefsInType tcIn lhsType = do
  getAstTDefCommonFromType tcIn lhsType >>= \case
    Just c -> case lhsType of
      I.ANamedType tdId -> do
        lhsTypeDef <- getTDef tdId
        let lhsTDCommon = I.tDefCommon lhsTypeDef
        pure $ Just (c.vDefs, lhsTDCommon.fqn)
      I.ArrayType _ _ ->
        pure $ Just (c.vDefs, TFqn "@stlib/primitives:Array")
      I.SliceType _ ->
        pure $ Just (c.vDefs, TFqn "@stlib/primitives:Slice")
      I.BoolType -> do
        pure $ Just (c.vDefs, TFqn "@stlib/primitives:Bool")
      I.NumPrimType numTyp -> do
        let name = numPrimTypeToText numTyp
        pure $ Just (c.vDefs, TFqn $ "@stlib/primitives:" <> name)
      _ -> pure Nothing
    _ -> pure Nothing

-- This prevents the Slice type from being stored in a variable or field
checkTypeHasRuntimeRepr :: (MonadTcError m) => ErrorTrace -> SrcRange -> I.Type -> m ()
checkTypeHasRuntimeRepr st sr t =
  unless (I.typeHasRuntimeRepr t)
    $ throw st sr "Type does not have a runtime representation"

makeConstListLit :: (MonadTc m) => Ctx -> I.Type -> [I.Constant'] -> m I.Constant
makeConstListLit ctx t cs = do
  listType <-
    getGenericBuiltinType
      ctx
      (Namespace "@stlib/list")
      (TName "List")
      [(I.TypeGenericArg t, undefined)]

  -- Build a constant List[String]

  let l = length cs
  let ptr =
        if l == 0
          then
            I.ConstNullPtr
          else
            I.ConstAddrOfArray0
              ( I.ConstArray t $ must $ listToList1 cs,
                I.ArrayType t $ fromIntegral l
              )

  pure
    ( I.ConstStructOrTuple
        [ (ptr, I.PtrType $ Just t),
          (I.ConstInt $ fromIntegral l, i64),
          (I.ConstInt 0, i64)
        ],
      listType
    )

makeConstStringLit :: (MonadTc m) => Ctx -> TypeHint -> Text -> m I.Constant
makeConstStringLit ctx hint str = do
  -- Use type hint to choose between string types
  strTypeMaybe <- case hint of
    TypeHint t@(I.ANamedType id) -> do
      getTDef id <&> \case
        I.AStructDef c -> case un c.fqn of
          "@stlib/os_string:OsString" -> Just t
          "@stlib/ascii_string:AsciiString" -> Just t
          _ -> Nothing
        _ -> Nothing
    _ -> pure Nothing

  -- Default to String
  stringType <- case strTypeMaybe of
    Just x -> pure x
    _ -> getBuiltinType ctx (Namespace "@stlib/string") (TName "String")

  -- String is represented as a list of byte constants
  let bytes = (BS.unpack (encodeUtf8 str) ++ [0]) <&> (I.ConstInt . fromIntegral)
  let l :: Integer = fromIntegral $ length bytes
  let array = (I.ConstArray u8 $ must $ listToList1 bytes, I.ArrayType u8 $ fromIntegral l)
  listU8Type <- getGenericBuiltinType ctx (Namespace "@stlib/list") (TName "List") [(I.TypeGenericArg u8, undefined)]
  -- Build a constant String(List[U8])
  let list =
        ( I.ConstStructOrTuple
            [ (I.ConstAddrOfArray0 array, I.PtrType $ Just u8),
              (I.ConstInt l, i64),
              (I.ConstInt 0, i64)
            ],
          listU8Type
        )
  pure (I.ConstStructOrTuple [list], stringType)
