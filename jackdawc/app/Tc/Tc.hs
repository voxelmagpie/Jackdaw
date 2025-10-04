-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use head" #-}
{-# HLINT ignore "Use uncurry" #-}
{-# HLINT ignore "Use maybe" #-}
-- TODO Split into 2 modules, 1 module provides runTc and handles the borrow checker function
module Tc.Tc (runTc, typeIsCopyable) where

import AccessMode
import Ast qualified as A
import Control.Exception (try)
import Control.Monad (foldM, forM, forM_, unless, void, when)
import Control.Monad.Reader (ReaderT (runReaderT))
import Data.Bits (Bits (complement, xor), (.&.), (.|.))
import Data.ByteString qualified as BS
import Data.Char (ord)
import Data.Either (isRight)
import Data.HashMap.Strict qualified as HM
import Data.List (elemIndex, find, init, uncons)
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, mapMaybe, maybeToList)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import HashMultiMap qualified as HMM
import Hir qualified
import InsOrdMap qualified as Ins
import Names
import Prelude2
import Primitives
import SrcLoc (SrcLoc', SrcRange, srcRangeOf, srcRangeToSrcLoc')
import Tc.Builtins
import Tc.Casts
import Tc.Ctx
import Tc.Ctx qualified as C
import Tc.Error (MonadTcError)
import Tc.Error qualified as E
import Tc.Fmt
import Tc.Names
import Tc.State
import Tc.TcErr
import Tc.TcIr qualified as I
import Tc.TypeAttribs (typeIsUnsafe)

data TypeHint = NoHint | TypeHint I.Type | FnReturningHint TypeHint
  deriving (Show, Eq)

-- If the error list is non-empty then the HIR is incomplete and should only be used for writing to a file for debugging
runTc :: BwCheckFnType TcM -> HashMap Namespace A.Ast -> Bool -> Bool -> IO (Either [E.Err] Hir.Ir)
runTc f asts forceCheckStLib uncheckedArithmetic = do
  state <- newTcState f typeIsCopyable
  res <- try @E.TcException $ runReaderT (typeCheck asts forceCheckStLib uncheckedArithmetic >> E.checkErrs) state
  pure $ case res of
    Left e -> Left $ un e
    _ -> Right state.hir

-- Type checks and generates HIR for all non-generic definitions
typeCheck :: (MonadTc m) => HashMap Namespace A.Ast -> Bool -> Bool -> m ()
typeCheck allAsts forceCheckStLib uncheckedArithmetic = do
  allAsts'' <- forM (toList allAsts) $ \(ns, ast) -> getImports allAsts ns ast <&> \i -> (ns, (ast, i))
  let allAsts' = HM.fromList allAsts''
  let primitivesAst = must $ HM.lookup (Namespace "@stlib/primitives") allAsts'
  let stLibAst = must $ HM.lookup (Namespace "@stlib/stlib") allAsts'
  let hashAst = must $ HM.lookup (Namespace "@stlib/hash") allAsts'
  let toStringAst = must $ HM.lookup (Namespace "@stlib/to_string") allAsts'
  let dropFnAst = must $ HM.lookup (VName "drop") (fst stLibAst).vDefs
  let equalFn = must $ HM.lookup (VName "equal") (fst stLibAst).vDefs
  let notEqualFn = must $ HM.lookup (VName "notEqual") (fst stLibAst).vDefs
  let cloneFn = must $ HM.lookup (VName "clone") (fst stLibAst).vDefs
  let hashFn = must $ HM.lookup (VName "hash") (fst hashAst).vDefs
  let addToHashFn = must $ HM.lookup (VName "addToHash") (fst hashAst).vDefs
  let toStringFn = must $ HM.lookup (VName "toString") (fst toStringAst).vDefs
  let tcIn = TcInputs allAsts' primitivesAst stLibAst hashAst toStringAst dropFnAst equalFn notEqualFn cloneFn hashFn addToHashFn toStringFn uncheckedArithmetic

  -- Functions reachable from _kStart
  do
    setStartedFromStart True
    let ast = stLibAst
    let namespace = Namespace "@stlib/stlib"
    let rootCtx = mkFileCtx namespace ast tcIn
    let d = must $ HM.lookup (VName "_kStart") (fst ast).vDefs
    _ <- visitVDef rootCtx rootCtx [] def (mkVFqn namespace (VName "start"), d) True
    setStartedFromStart False

  -- All other functions
  forM_ (toList allAsts') $ \(namespace, (rootAst, imports)) ->
    -- Skip stlib files unless forceCheckStLib == True.
    when (forceCheckStLib || not ("@stlib/" `T.isPrefixOf` un namespace)) $ do
      let rootCtx = mkFileCtx namespace (rootAst, imports) tcIn

      forM_ (reverse rootAst.requireStmntsRev) $ checkRequireStmnt rootCtx

      forM_ (toList rootAst.vDefs) $ \(name, d) ->
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
            x <- getMemberFnsForType tcIn lhsType
            forM_ x $ \(memberFns, lhsTFqn) -> do
              typeCtx <- getTypeCtx rootCtx lhsType <&> must -- Type has member functions and therefore has a context
              forM_ (HM.toList $ fst memberFns) $ \(fnName, fnDef) -> do
                when (null fnDef.c.genericParams)
                  $ void
                  $ visitVDef
                    rootCtx
                    typeCtx
                    []
                    (snd fnDef.c.name)
                    (VFqn $ un lhsTFqn <> "." <> un fnName, A.AFnDef fnDef)
                    True

  -- Type definitions that haven't been fully checked
  getQueuedTsDef2s >>= mapM_ checkTDef2

typeIsCopyable :: (MonadTc m) => I.Type -> m Bool
typeIsCopyable = \case
  I.BoolType -> pure True
  I.NumPrimType _ -> pure True
  I.ANamedType id -> do
    tsDef <- checkTDef2 id
    pure $ not $ case tsDef of I.AStructDef2 x -> x.nonCopyable; I.AnEnumDef2 x -> x.nonCopyable
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
  (c, act) <- getConstLitExpr ctx (TypeHint bool) e
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

-- If this is a member function then the context includes generic parameters from containing type as well as the function
-- 'userCtx' is the context of the code that is accessing this definition
-- 'outerCtx' is the context of the source file or type that the definition is within
makeVDefCtx :: (MonadHirRead' m) => Ctx -> Ctx -> [I.GenericArg] -> [A.GenericParameter] -> Bool -> Bool -> VName' -> Bool -> SrcLoc' -> m Ctx
makeVDefCtx _userCtx outerCtx genericArgs astGp isIterator isAccessor name isUnsafe srcLoc = do
  let gp = zip astGp genericArgs
  let newTypeParams =
        mapMaybe (\case (A.TypeGenericParameter n, I.TypeGenericArg t) -> Just (fst n, t); _ -> Nothing) gp
  let newValParams =
        mapMaybe (\case (A.ValueGenericParameter n, I.ValueGenericArg v) -> Just (fst n, v); _ -> Nothing) gp
  gArgsText <- forM genericArgs $ formatGenArg False
  let dbgName = if null genericArgs then un (fst name) else un (fst name) <> "[" <> T.intercalate "," gArgsText <> "]"
  pure
    $ outerCtx
      { genericParams = outerCtx.genericParams <> genericArgs,
        tNameToGp = HM.fromList $ HM.toList outerCtx.tNameToGp <> newTypeParams,
        vNameToGp = HM.fromList $ HM.toList outerCtx.vNameToGp <> newValParams,
        inIterator = isIterator,
        inAccessor = isAccessor,
        inUnsafeCode = isUnsafe,
        et = if null genericArgs then outerCtx.et else (dbgName, srcLoc) : outerCtx.et
      }

makeTSDefCtx :: (MonadHirRead' m) => Ctx -> Ctx -> TFqn -> [A.GenericParameter] -> [I.GenericArg] -> Maybe I.Type -> TName -> Bool -> SrcLoc' -> m Ctx
makeTSDefCtx _userCtx outerCtx fqn astGp genericArgs typ name isUnsafe srcLoc = do
  let gp = zip astGp genericArgs
  let newTypeParams =
        mapMaybe (\case (A.TypeGenericParameter n, I.TypeGenericArg t) -> Just (fst n, t); _ -> Nothing) gp
  let newValParams =
        mapMaybe (\case (A.ValueGenericParameter n, I.ValueGenericArg v) -> Just (fst n, v); _ -> Nothing) gp
  gArgsText <- forM genericArgs $ formatGenArg False
  let dbgName = if null genericArgs then un name else un name <> "[" <> T.intercalate ", " gArgsText <> "]"
  pure
    $ Ctx
      { namespace = outerCtx.namespace,
        thisAst = outerCtx.thisAst,
        thisAstImports = outerCtx.thisAstImports,
        tcIn = outerCtx.tcIn,
        selfType = typ <&> (fqn,),
        tNameToGp = HM.fromList newTypeParams,
        vNameToGp = HM.fromList newValParams,
        genericParams = genericArgs,
        variables = [],
        returnType = Nothing,
        inIterator = False,
        inAccessor = False,
        inLoop = False,
        inUnsafeCode = isUnsafe,
        et = [(dbgName, srcLoc) | notNull genericArgs]
      }

-- If this type has a type definition in code (Xyz, Array, Slice, etc.) then this function gets the relevant context
getTypeCtx :: (MonadTc m) => Ctx -> I.Type -> m (Maybe Ctx)
getTypeCtx ctx t = do
  getCachedTypeCtx t >>= \case
    Just x -> pure $ Just x
    _ -> do
      let outerCtx = mkFileCtx (Namespace "@stlib/primitives") ctx.tcIn.primitivesAst ctx.tcIn
      ctx' <- case t of
        I.ArrayType el n ->
          let c = (fst ctx.tcIn.primitivesAst).tsDefs & HM.lookup (TName "Array") & must & A.getTDefCommonMaybe & must
              astGp = c.c.genericParams
              gArgs = [I.TypeGenericArg el, I.ValueGenericArg (I.ConstInt $ fromIntegral n, i32)]
           in Just <$> makeTSDefCtx ctx outerCtx (TFqn "@stlib/primitives:Array") astGp gArgs (Just t) (TName "Array") False (srcRangeToSrcLoc' (snd c.c.name))
        I.SliceType el ->
          let c = (fst ctx.tcIn.primitivesAst).tsDefs & HM.lookup (TName "Slice") & must & A.getTDefCommonMaybe & must
              astGp = c.c.genericParams
              gArgs = [I.TypeGenericArg el]
           in Just <$> makeTSDefCtx ctx outerCtx (TFqn "@stlib/primitives:Slice") astGp gArgs (Just t) (TName "Slice") False (srcRangeToSrcLoc' (snd c.c.name))
        I.NumPrimType p ->
          let name = numPrimTypeToText p
              c = (fst ctx.tcIn.primitivesAst).tsDefs & HM.lookup (TName name) & must & A.getTDefCommonMaybe & must
           in Just <$> makeTSDefCtx ctx outerCtx (TFqn $ "@stlib/primitives:" <> numPrimTypeToText p) [] [] (Just t) (TName $ numPrimTypeToText p) False (srcRangeToSrcLoc' (snd c.c.name))
        I.BoolType ->
          let c = (fst ctx.tcIn.primitivesAst).tsDefs & HM.lookup (TName "Bool") & must & A.getTDefCommonMaybe & must
           in Just <$> makeTSDefCtx ctx outerCtx (TFqn "@stlib/primitives:Bool") [] [] (Just t) (TName "Bool") False (srcRangeToSrcLoc' (snd c.c.name))
        I.ANamedType _ ->
          -- Named type context was made when the type definition (1) was visited
          undefined
        _ -> pure Nothing
      forM_ ctx' $ addTypeCtx t
      pure ctx'

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
              x <- getConstLitExpr ctx (TypeHint t) e
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
              "@stlib/stlib:hasMemberFn" -> do
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
                    Just c -> HM.member (VName fnName) $ fst c.memberFns
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
                listStringType <-
                  getGenericBuiltinType
                    ctx
                    (Namespace "@stlib/list")
                    (TName "List")
                    [(I.TypeGenericArg stringType, undefined)]

                -- Build a constant List[String]

                let l = length fields
                let ptr =
                      if l == 0
                        then
                          I.ConstNullPtr
                        else
                          I.ConstAddrOfArray0
                            ( I.ConstArray stringType $ must $ listToList1 fields,
                              I.ArrayType stringType $ fromIntegral l
                            )

                pure
                  $ Just
                    ( I.ConstStructOrTuple
                        [ (ptr, I.PtrType $ Just stringType),
                          (I.ConstInt $ fromIntegral l, i64),
                          (I.ConstInt 0, i64)
                        ],
                      listStringType
                    )
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
                    pure $ Just (I.ConstBool $ isJust $ snd $ e.dataCons !! fromIntegral i, bool)
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
              _ -> do
                unless (null ctx.genericParams) $ throw userCtx.et userSr "Unknown generic builtin"
                pure Nothing
          --

          case e of
            Just (_, act) ->
              unless (t == act) $ addError ctx.et constDef.typeExpr "Explicit type does not match actual type"
            _ -> pure ()

          reachableFromStart <- getStartedFromStart
          let c =
                I.AConstDef
                  $ I.ConstDef
                    { c =
                        I.VDefCommon
                          { name = constDef.c.name,
                            fqn = fqn,
                            typ = t,
                            genericArgs = ctx.genericParams,
                            reachableFromStart = reachableFromStart,
                            attributes = constDef.attributes
                          },
                      value = e <&> fst
                    }
          id <- addVDef c
          pure (id, t, c)
        A.AFnDef fnDef -> do
          when (isJust fnDef.retType && Attribute "NoReturn" `elem` fnDef.attributes)
            $ addError ctx.et fnDef.c.name "Functions which return a value cannot be @NoReturn"

          unless (length ctx.genericParams == length fnDef.c.genericParams + length outerCtx.genericParams)
            $ throw userCtx.et userSr
            $ "Wrong number of generic arguments to "
            <> un (fst fnDef.c.name)

          checkTemplateArgs ctx fnDef.c.genericParams gArgs

          when (fnDef.isVarArgs && Attribute "Unsafe" `notElem` fnDef.attributes)
            $ addError ctx.et fnDef.c.name "Var-args requires @Unsafe"

          when (fnDef.isVarArgs && isJust fnDef.code)
            $ addError ctx.et fnDef.c.name "Var-args is for extern functions only"

          when (fnDef.isVarArgs && null fnDef.parameters)
            $ addError ctx.et fnDef.c.name "Must have at least once parameter before var-args"

          when (fnDef.isIterator && isNothing fnDef.code)
            $ addError ctx.et fnDef.c.name "Iterators cannot be extern"

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
                            fqn = fqn,
                            typ = fnType,
                            genericArgs = ctx.genericParams,
                            reachableFromStart = reachableFromStart,
                            attributes = fnDef.attributes
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
          A.AConstDef x -> (x.c.genericParams, False, False, snd x.c.name, fst x.c.name, Attribute "Unsafe" `elem` x.attributes)
          A.AFnDef x -> (x.c.genericParams, x.isIterator, x.isAccessor, snd x.c.name, fst x.c.name, Attribute "Unsafe" `elem` x.attributes)
  ctx <- makeVDefCtx userCtx outerCtx (fst <$> gArgs) astGp isIterator isAccessor (defName, defSr) isUnsafe (srcRangeToSrcLoc' defSr)
  (vDefId, t, hirDef) <- getVDefType userCtx outerCtx ctx gArgs userSr (fqn, astDef)

  unless allowUnsafe
    $ when (Attribute "Unsafe" `elem` (Hir.vDefCommon hirDef).attributes)
    $ addError userCtx.et userSr "Cannot use unsafe definition in safe context"

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
                      inUnsafeCode = Attribute "Unsafe" `elem` fnDef.attributes
                    }

            -- Store current function's state
            prevNextVarId <- peekNextLocalVarUid
            prevUsedItersList <- getUsedIters
            prevUsesThrowingFns <- getUsesThrowingFns

            -- Type check function
            resetLocalVarUid $ length newVars
            resetUsedItersList []
            setUsesThrowingFns False
            s' <- getCodeBlockStmnt ctx' [s] []

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
            (s'', terminates) <- bwCheckFn s' (zip3 p' newVars dropFns) (snd fnDef.c.name) fnDef.isAccessor
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

getAstTDefCommonFromType :: (MonadHirRead' m) => TcInputs -> I.Type -> m (Maybe A.TypeDefCommon)
getAstTDefCommonFromType tcIn t = do
  y <- getAstTDefFromType tcIn t
  case y of
    Just (A.ATypeDef x) -> pure $ Just x.c
    Just (A.AStructDef x) -> pure $ Just x.c
    Just (A.AnEnumDef x) -> pure $ Just x.c
    _ -> pure Nothing

getAstTDefFromType :: (MonadHirRead' m) => TcInputs -> I.Type -> m (Maybe A.AnyTSDef)
getAstTDefFromType tcIn = \case
  I.ANamedType tDefId -> do
    d <- getTDef tDefId
    let hirTDefCommon = I.tDefCommon d
    let (ast, _) = must $ HM.lookup hirTDefCommon.namespace tcIn.allAsts
    pure $ HM.lookup hirTDefCommon.name ast.tsDefs
  I.ArrayType _ _ -> pure $ HM.lookup (TName "Array") (fst tcIn.primitivesAst).tsDefs
  I.SliceType _ -> pure $ HM.lookup (TName "Slice") (fst tcIn.primitivesAst).tsDefs
  I.NumPrimType x -> pure $ HM.lookup (TName $ numPrimTypeToText x) (fst tcIn.primitivesAst).tsDefs
  I.BoolType -> pure $ HM.lookup (TName "Bool") (fst tcIn.primitivesAst).tsDefs
  _ -> pure Nothing

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
            A.ATypeDef d -> A.tDefCommon d
            A.AStructDef d -> A.tDefCommon d
            A.AnEnumDef d -> A.tDefCommon d
            A.ATypeAlias _ -> undefined
      let typeIsUnsafe' = Attribute "Unsafe" `elem` (A.tsDefCommon astDef).attributes

      let hasOnDrop = HM.member (VName "onDrop") (fst c.memberFns)
      case astDef of
        A.ATypeAlias _ -> undefined
        A.ATypeDef _ -> undefined -- No fields so not queued by getTSDefType
        A.AStructDef structDef -> do
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
          dataCons <- forM enumDef.dataCons $ \(sr', typeExprMaybe) -> forM typeExprMaybe $ \typeExpr -> do
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

getTSDefType ::
  (MonadTc m) =>
  Ctx ->
  Ctx ->
  [I.GenericArg'] ->
  SrcRange ->
  (TFqn, A.AnyTSDef) ->
  m I.Type
getTSDefType userCtx outerCtx gArgs sr (fqn, astDef) = do
  let typeIsUnsafe' = Attribute "Unsafe" `elem` (A.tsDefCommon astDef).attributes

  unless userCtx.inUnsafeCode
    $ when typeIsUnsafe'
    $ addError userCtx.et sr "Cannot use unsafe type in safe context"

  let gArgs' = fst <$> gArgs
  tsDefMaybe <- getCachedTSDef fqn gArgs'
  case tsDefMaybe of
    Just x -> do
      pure x
    _ -> do
      unless (length (A.tsDefCommon astDef).genericParams == length gArgs)
        $ throw userCtx.et sr "Wrong number of arguments to type"

      checkTemplateArgs userCtx (A.tsDefCommon astDef).genericParams gArgs

      let typeGArg i = case gArgs' !! i of I.TypeGenericArg t' -> t'; _ -> undefined

      case astDef of
        A.ATypeAlias alias -> do
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
                  (srcRangeToSrcLoc' (snd alias.c.name))
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

              let srcLoc = srcRangeToSrcLoc' (snd td.c.c.name)
              ctx <- makeTSDefCtx userCtx outerCtx fqn c.c.genericParams gArgs' (Just x) name typeIsUnsafe' srcLoc
              addTypeCtx x ctx
              pure x
            --
            A.AStructDef structDef -> do
              forM_ (toList $ fst structDef.c.memberFns) $ \(n, f) ->
                when (n `elem` Ins.keys structDef.fields)
                  $ addError userCtx.et f.c.name ("Member function " <> un n <> " has same name as field")

              let srcLoc = srcRangeToSrcLoc' (snd structDef.c.c.name)
              ctx <- makeTSDefCtx userCtx outerCtx fqn structDef.c.c.genericParams gArgs' Nothing name typeIsUnsafe' srcLoc

              (t, id) <- addTSDef fqn gArgs' $ I.AStructDef tDefCommon
              let ctx' = ctx {C.selfType = Just (fqn, t)}
              addTypeCtx t ctx'
              forM_ c.requireStmnts $ checkRequireStmnt ctx'
              queueTDefVisit id (ctx', userCtx, sr, astDef)
              -- Type checking continues in checkTDef2
              pure t
            --
            A.AnEnumDef enumDef -> do
              forM_ (toList $ fst enumDef.c.memberFns) $ \(n, f) ->
                when (n `elem` Ins.keys enumDef.dataCons)
                  $ addError userCtx.et f.c.name ("Member function " <> un n <> " has same name as data constructor")

              let srcLoc = srcRangeToSrcLoc' (snd enumDef.c.c.name)
              ctx <- makeTSDefCtx userCtx outerCtx fqn enumDef.c.c.genericParams gArgs' Nothing name typeIsUnsafe' srcLoc

              let canBeCastedToInt = all (isNothing . snd) $ Ins.elems enumDef.dataCons

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

getGenArg :: (MonadTc m) => Ctx -> A.GenericArg -> m I.GenericArg'
getGenArg ctx (A.TypeGenericArg e@(_, sr)) = getType ctx e <&> \x -> (I.TypeGenericArg x, sr)
getGenArg ctx (A.ValueGenericArg e@(_, sr)) = getConstLitExpr ctx NoHint e <&> \x -> (I.ValueGenericArg x, sr)

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
    unless ctx.inUnsafeCode $ addError ctx.et sr "Cannot use pointers in safe code"
    t <- forM typeMaybe $ getType ctx
    pure $ I.PtrType t
  A.ConstPtrType typeExpr -> do
    t <- getType ctx typeExpr
    pure $ I.ConstPtrType t
  A.TypeOf e ->
    snd3 <$> getExpr ctx NoHint e

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

--
-- Expressions
--

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
    unless ctx.inUnsafeCode $ addError ctx.et sr "Pointers are not valid in safe code"
    case hint of
      TypeHint t@(I.PtrType _) ->
        pure (I.ConstNullPtr, t)
      TypeHint t@(I.AFnType x)
        | x.isNullable ->
            pure (I.ConstNullPtr, t)
      _ -> do
        addError ctx.et sr "Unable to deduce pointer type"
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
      when (Attribute "Unsafe" `elem` attribs) $ addError ctx.et sr "Unsafe types not valid for constants"
      c@(_, actualType) <- getConstLitExpr ctx (TypeHint expectedType) astEx >>= iCastConstant expectedType
      unless (actualType == expectedType) $ do
        (act, ex) <- format2Types actualType expectedType
        addError ctx.et sr $ T.concat ["Wrong type for struct field ", un name, "\nExpected ", ex, ", got ", act]
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
      ("!=", I.ConstBool x, I.ConstBool y) ->
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
    unless (lhsType == bool) $ addError ctx.et lhsExpr "Expected boolean"

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
    unless (lhsType == bool) $ addError ctx.et lhsExpr "Expected boolean"
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
      addError ctx.et sr "Unable to deduce pointer type"
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
    unless (t == bool) $ addError ctx.et lhsAstExpr "Expected boolean for lhs of 'and' operator"
    rhs@(_, t', _) <- getExpr ctx (TypeHint bool) rhsAstExpr >>= iCast bool
    unless (t' == bool) $ addError ctx.et lhsAstExpr "Expected boolean for rhs of 'and' operator"
    pure (I.AndExpr lhs rhs, bool, sr)
  A.OrExpr lhsAstExpr _ rhsAstExpr -> do
    lhs@(_, t, _) <- getExpr ctx (TypeHint bool) lhsAstExpr >>= iCast bool
    unless (t == bool) $ addError ctx.et lhsAstExpr "Expected boolean for lhs of 'or' operator"
    rhs@(_, t', _) <- getExpr ctx (TypeHint bool) rhsAstExpr >>= iCast bool
    unless (t' == bool) $ addError ctx.et lhsAstExpr "Expected boolean for rhs of 'or' operator"
    pure (I.OrExpr lhs rhs, bool, sr)
  A.UninitExpr -> case hint of
    TypeHint t -> do
      unless ctx.inUnsafeCode $ addError ctx.et sr "Uninitialised data cannot be used in a safe context"
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

  unless (t == t2) $ addError ctx.et sr "Types on either side of conditional operator do not match"

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
  case lhsType of
    -- Member functions for types without definitions written in jackdaw code
    I.AFnType _ -> do
      unless (null fnAstGArgs) $ throw ctx.et sr "No such function is defined for function pointers"
      argAstExpr <- case argsExprs of [x] -> pure x; _ -> throw ctx.et sr "Wrong number of arguments"
      case () of
        _ | vOrOpName == Left (VName "eq") || vOrOpName == Right (OpName "==") -> do
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError ctx.et argSr "Incompatible types"
          pure $ Left (I.PtrEqExpr lhs argExpr, bool, sr)
        _ | vOrOpName == Left (VName "neq") || vOrOpName == Right (OpName "!=") -> do
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError ctx.et argSr "Incompatible types"
          pure $ Left (I.PtrNEqExpr lhs argExpr, bool, sr)
        _ -> throw ctx.et sr "No such member function is defined for function pointers"
    I.PtrType pointeeType -> do
      unless (null fnAstGArgs) $ throw ctx.et sr "No such function is defined for pointers"
      argAstExpr <- case argsExprs of [x] -> pure x; _ -> throw ctx.et sr "Wrong number of arguments"
      case () of
        _ | vOrOpName == Left (VName "add") || vOrOpName == Right (OpName "+") -> do
          when (isNothing pointeeType) $ throw ctx.et sr "Operation not valid on void pointers"
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint i64) argAstExpr >>= iCast i64
          unless (argType == i64) $ addError ctx.et argSr "Pointer addition expects an I64"
          pure $ Left (I.APtrAddExpr $ I.PtrAddExpr {expr = lhs, index = argExpr}, lhsType, sr)
        _ | vOrOpName == Left (VName "sub") || vOrOpName == Right (OpName "-") -> do
          when (isNothing pointeeType) $ throw ctx.et sr "Operation not valid on void pointers"
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint i64) argAstExpr >>= iCast i64
          unless (argType == i64) $ addError ctx.et argSr "Pointer subtraction expects an I64"
          pure $ Left (I.APtrSubExpr $ I.PtrSubExpr {expr = lhs, index = argExpr}, lhsType, sr)
        _ | vOrOpName == Left (VName "eq") || vOrOpName == Right (OpName "==") -> do
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError ctx.et argSr "Incompatible types"
          pure $ Left (I.PtrEqExpr lhs argExpr, bool, sr)
        _ | vOrOpName == Left (VName "neq") || vOrOpName == Right (OpName "!=") -> do
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError ctx.et argSr "Incompatible types"
          pure $ Left (I.PtrNEqExpr lhs argExpr, bool, sr)
        _ -> throw ctx.et sr "No such member function is defined for pointers"
    I.ConstPtrType _ -> do
      unless (null fnAstGArgs) $ throw ctx.et sr "No such function is defined for const pointers"
      argAstExpr <- case argsExprs of [x] -> pure x; _ -> throw ctx.et sr "Wrong number of arguments"
      case () of
        _ | vOrOpName == Left (VName "eq") || vOrOpName == Right (OpName "==") -> do
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError ctx.et argSr "Incompatible types"
          pure $ Left (I.PtrEqExpr lhs argExpr, bool, sr)
        _ | vOrOpName == Left (VName "neq") || vOrOpName == Right (OpName "!=") -> do
          argExpr@(_, argType, argSr) <- getExpr ctx (TypeHint lhsType) argAstExpr >>= iCast lhsType
          unless (argType == lhsType) $ addError ctx.et argSr "Incompatible types"
          pure $ Left (I.PtrNEqExpr lhs argExpr, bool, sr)
        _ -> throw ctx.et sr "No such member function is defined for const pointers"
    -- Member functions for types with a in-code definitions
    _ -> do
      -- Get list of member functions
      ((memberFns, memberFnOps), lhsTFqn) <-
        getMemberFnsForType ctx.tcIn lhsType >>= \case
          Just x -> pure x
          _ -> pure (def, undefined)

      -- Find the function
      let (fnDefMaybe, vOrOpName') = case vOrOpName of
            Left n -> (maybeToList $ HM.lookup n memberFns, un n)
            -- Potential operator functions are filtered by length to allow
            -- overloading between prefix and unary operators
            -- TODO Filter by second arg type for operators
            Right n -> (filter (\f -> length f.parameters == length argsExprs + 1) $ HMM.lookup n memberFnOps, un n)

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
            _ -> throw ctx.et nameSr $ "No such member function: " <> vOrOpName'
        [] -> throw ctx.et nameSr $ "No such member function: " <> vOrOpName'
        [x] -> pure $ Left x
        _ -> throw ctx.et nameSr $ "Operator is ambiguous: " <> vOrOpName'

      case fnDefOrAutoGenFn of
        Left fnDef -> do
          let fqn = VFqn $ un lhsTFqn <> "." <> un (fst fnDef.c.name)

          typeCtx <- getTypeCtx ctx lhsType <&> must -- Type has member functions and therefore has a context
          fnGArgs <- forM fnAstGArgs $ getGenArg ctx

          unless (length fnAstGArgs == length fnDef.c.genericParams)
            $ throw ctx.et sr "Wrong number of generic arguments to member function"

          (id, fnType, _) <- visitVDef ctx typeCtx fnGArgs sr (fqn, A.AFnDef fnDef) ctx.inUnsafeCode

          let fnExpr = (I.LoadConstantExpr $ I.ConstFnPtr id, fnType, sr)

          getCallExpr ctx nameSr sr fnExpr (Just lhs) argsExprs expectIterator <&> \(ce, r) -> case (r, fnDef.isAccessor) of
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
      when expectIterator $ addError ctx.et sr "Not an iterator"
      pure (f.params, f.isVarArgs, f.ret)
    I.AnAccessorType f -> do
      when expectIterator $ addError ctx.et sr "Not an iterator"
      pure (toList f.params, f.isVarArgs, Just f.ret)
    I.AnIteratorType f -> do
      unless expectIterator $ addError ctx.et sr "Cannot call an iterator, consider using a for loop"
      pure (f.params, False, Just f.ret)
    I.AnAccessorIteratorType f -> do
      unless expectIterator $ addError ctx.et sr "Cannot call an iterator, consider using a for loop"
      pure (toList f.params, False, Just f.ret)
    _ -> throw ctx.et fnSr "Type is not callable"

  -- Check the self type (in case the member function's first arg is not Self)
  forM_ selfArgMaybe $ \(_, act, argSr) -> do
    case uncons expectedArgs' of
      Just ((_, ex), _) ->
        unless (act == ex) $ do
          (act', ex') <- format2Types act ex
          addError ctx.et argSr $ T.concat ["Incorrect type for function self argument\nExpected ", ex', ", got ", act']
      _ ->
        throw ctx.et argSr $ T.concat ["Member function takes no parameters"]

  -- Remove self arg from expectedArgs as it is dealt with separately ^
  let expectedArgs = if isJust selfArgMaybe then tail expectedArgs' else expectedArgs'

  if isVarArgs
    then
      unless (length astArgExprs >= length expectedArgs) $ addError ctx.et sr "Wrong number of arguments to function"
    else
      unless (length astArgExprs == length expectedArgs) $ addError ctx.et sr "Wrong number of arguments to function"

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
      addError ctx.et argSr $ T.concat ["Incorrect type for function argument\nExpected ", ex', ", got ", act']

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
          $ addError ctx.et astAccessorExpr.accessor "Index out of range"
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
                  $ addError ctx.et sr "Cannot access unsafe field in safe context"
                dropFn <- getDropFn ctx.tcIn t sr
                let accExpr = I.FieldAccessorExpr {expr = e, index = fromIntegral fieldIdx, dropFn = dropFn}
                pure (I.AFieldAccessorExpr accExpr, fieldType, sr)
          _ -> throw ctx.et sr "Accessor type is not valid on structs"
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
        unless (all (== y) ys) $ addError ctx.et sr "Conflicting types for array elements"
        pure $ Just y
  A.StructDes _ ->
    pure Nothing

-- This prevents the Slice type from being stored in a variable or field
checkTypeHasRuntimeRepr :: (MonadTcError m) => [(Text, SrcLoc')] -> SrcRange -> I.Type -> m ()
checkTypeHasRuntimeRepr st sr t =
  unless (I.typeHasRuntimeRepr t)
    $ throw st sr "Type does not have a runtime representation"

getVarStmnt :: (MonadTc m) => Ctx -> A.Destructure -> A.Expr -> m ((I.Destructure, I.Expr), Ctx)
getVarStmnt ctx astDes astExpr = do
  hint <- getDestructureTypeHint ctx astDes
  let hint' = maybe NoHint TypeHint hint
  e@(_, t, _) <- getExpr ctx hint' astExpr >>= case hint of Just h -> iCast h; _ -> pure
  checkTypeHasRuntimeRepr ctx.et (snd astExpr) t
  (d, ctx') <- makeDestructure ctx t astDes
  pure ((d, e), ctx')

getAstAssignmentStmnt :: (MonadTcError m) => Ctx -> A.Statement -> m A.AssignmentStmnt
getAstAssignmentStmnt ctx (s, sr) = case s of
  A.AnAssignmentStmnt x -> pure x
  A.CompoundAssignmentOpStmnt o -> pure $ compoundIntoAssignmentStmnt sr o
  _ -> throw ctx.et sr "Expected assignment"

compoundIntoAssignmentStmnt :: SrcRange -> A.InfixOpExpr -> A.AssignmentStmnt
compoundIntoAssignmentStmnt sr o = a
  where
    op = first (\(OpName n) -> OpName $ T.take (length n - 1) n) o.op -- Remove '=' from end
    rhs = (A.AnInfixOpExpr $ A.InfixOpExpr op o.lhs o.rhs, sr)
    a = A.AssignmentStmnt (Just $ fst o.lhs) (snd o.lhs) rhs

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
    unless (lhsType == rhsType) $ addError ctx.et sr "Expression type does not match LHS type"
    des <- getDropFn ctx.tcIn lhsType x.lhsSr
    pure $ I.AssignmentStmnt {lhs = Just lhs, value = e, lhsDestructor = des}

getFnCallStmnt :: (MonadTc m) => Ctx -> A.FnCallExpr -> SrcRange -> m I.Statement
getFnCallStmnt ctx x sr = do
  getFnCallExpr ctx NoHint sr x False >>= \case
    Left e@(_, t, sr') -> do
      des <- getDropFn ctx.tcIn t sr'
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
      when ctx.inIterator $ addError ctx.et sr "Iterators must return void; use yield to produce a value"

      e'' <- case ctx.returnType of
        Just r -> do
          e''@(_, actualType, _) <- getExpr ctx (TypeHint r) e' >>= if ctx.inAccessor then pure else iCast r

          if actualType == r || not ctx.inAccessor
            then
              pure e''
            else do
              let isAccRawPtr = actualType == I.PtrType (Just r)
              -- Check if the function return type is Slice[A] and the returned value is RawSlice[A]
              isAccRawSlice <- case (r, actualType) of
                (I.SliceType t, I.ANamedType id) -> do
                  c <- getTDef id <&> I.tDefCommon
                  pure $ c.fqn == TFqn "@stlib/raw_slice:RawSlice" && (c.genericArgs !! 0) == I.TypeGenericArg t
                _ -> pure False

              unless (isAccRawPtr || isAccRawSlice)
                $ addError ctx.et e' "Expression type does not match function return type"

              pure $ if isAccRawPtr then (I.PtrDerefExpr e'', r, sr) else (I.RawSliceToSliceExpr e'', r, sr)
        _ -> do
          addError ctx.et e' "Returning expression in function that returns void"
          getExpr ctx NoHint e'
      pure (I.ReturnStmnt (Just e''), sr)
    _ -> do
      unless (isNothing ctx.returnType || ctx.inIterator) $ addError ctx.et sr "Expected an expression"
      pure (I.ReturnStmnt Nothing, sr)

fnIsNoThrow :: (MonadHirRead' m) => I.VDefId -> m Bool
fnIsNoThrow id = do
  d <- getVDef id
  x <- getFnDefBodyMaybe id <&> ((<&> snd) >>> fromMaybe False)
  pure $ x || Attribute "NoThrow" `elem` (Hir.vDefCommon d).attributes

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
          -- If there isn't a definition for the compound assignment then the assignment is transformed into
          -- lhsExpr = lhsExpr op rhsExpr
          -- If the lhs expression has side effects then this is not ideal
          -- TODO borrow ref r = f(x()) { r = r + y; }
          s' <- getAssignmentStmnt ctx $ compoundIntoAssignmentStmnt sr o
          getCodeBlockStmnt ctx astStmnts ((I.AnAssignmentStmnt s', sr) : hirStmnts)

    -- TODO This code is very similar to the regular infix op code, can it be merged or something?
    lhs@(_, lhsType, _) <- getExpr ctx NoHint o.lhs
    getMemberFnsForType ctx.tcIn lhsType >>= \case
      Nothing -> basic
      Just (memberFns, lhsTFqn) -> do
        let fnDefMaybe = filter (\f -> length f.parameters == 2) $ HMM.lookup (fst o.op) $ snd memberFns
        case fnDefMaybe of
          [] ->
            basic
          [fnDef] -> do
            let fqn = VFqn $ un lhsTFqn <> "." <> un (fst fnDef.c.name)
            typeCtx <- getTypeCtx ctx lhsType <&> must -- Type has member functions and therefore has a context
            unless (null fnDef.c.genericParams)
              $ throw ctx.et sr "Operators cannot take generic arguments" -- TODO type inference?
            (id, fnType, _) <- visitVDef ctx typeCtx [] sr (fqn, A.AFnDef fnDef) ctx.inUnsafeCode

            let fnExpr = (I.LoadConstantExpr $ I.ConstFnPtr id, fnType, def)

            s' <-
              getCallExpr ctx (snd o.op) sr fnExpr (Just lhs) [o.rhs] False >>= \(ce, r) ->
                case (r, fnDef.isAccessor) of
                  (Just _, _) -> throw ctx.et sr "Compound assignment operator functions must return void"
                  (Nothing, True) -> throw ctx.et sr "Compound assignment operator functions cannot be accessors"
                  (Nothing, False) -> pure $ I.FnCallStmnt ce
            getCodeBlockStmnt ctx astStmnts ((s', sr) : hirStmnts)
          -- TODO Use type hint to choose an operator function?
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
      $ addError ctx.et sr "Iterators cannot return values; yield to produce a value or return void to terminate early"
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
      $ addError ctx.et sr' ("Wrong type for yield expression\nExpected " <> exp' <> ", got " <> act')
    getCodeBlockStmnt ctx astStmnts ((I.YieldStmnt e, sr) : hirStmnts)
  A.ForLoopStmnt vars cond as False innerStmnt -> do
    (varsRev, ctx') <-
      foldM
        (\(acc :: [(I.Destructure, I.Expr)], c) (d, e) -> getVarStmnt c d e <&> first (: acc))
        ([], ctx)
        vars

    let ctx'' = ctx' {inLoop = True}
    condExpr <- getExpr ctx'' (TypeHint bool) cond

    as' <- forM as $ \a@(_, sr') -> do
      s' <- getAstAssignmentStmnt ctx a
      getAssignmentStmnt ctx'' s' <&> (,sr')

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
                      a <- getAstAssignmentStmnt ctx a'
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
  A.MatchStmnt mode astExpr arms -> do
    e@(_, t, _) <- getExpr ctx NoHint astExpr
    checkTypeHasRuntimeRepr ctx.et (snd astExpr) t
    arms' <- forM arms $ \b -> do
      -- TODO Check for exhaustiveness
      (ctx', p) <- getMatchBranchCtx ctx b.pattern t
      code <- getCodeBlockStmnt ctx' [b.code] []
      pure $ I.MatchBranch p (snd b.pattern) code
    getCodeBlockStmnt ctx astStmnts $ (I.MatchStmnt mode e arms', sr) : hirStmnts
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
      addError ctx.et sr $ T.concat ["Wrong type for throw statement\nExpected ", ex, ", got ", act]

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
      addError ctx.et sr $ T.concat ["Error types do not match\nExpected ", retErrType', ", got ", errType']

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
          addError ctx.et sr $ T.concat ["Wrong type for borrow statement\nExpected ", ex, ", got ", act]
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
    >>= \isUnsafe -> when isUnsafe $ addError ctx.et sr "Cannot use unsafe type in safe code"
  id <- newLocalVarUid
  pure (ctx {variables = Variable name (Left id) typ : ctx.variables}, id)

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
  enumDef <- case enumType of
    I.ANamedType tDefId -> do
      checkTDef2 tDefId >>= \case
        I.AnEnumDef2 x -> pure x
        _ -> throw ctx.et sr "Not an enum"
    _ -> throw ctx.et sr "Not an enum"
  (consActualTypeMaybe, consIdx) <- case Ins.lookupWithIndex consName enumDef.dataCons of
    Just x -> pure x
    _ -> throw ctx.et sr $ "No such data constructor: " <> un consName
  when (isJust consActualTypeMaybe) $ throw ctx.et sr "Data constructor holds a value"
  pure (ctx, I.PatternDataCons0 consIdx)
getMatchBranchCtx ctx (A.PatternDataCons1 consName innerPattern, sr) enumType = do
  enumDef <- case enumType of
    I.ANamedType tDefId -> do
      checkTDef2 tDefId >>= \case
        I.AnEnumDef2 x -> pure x
        _ -> throw ctx.et sr "Not an enum"
    _ -> throw ctx.et sr "Not an enum"
  (consActualTypeMaybe, consIdx) <- case Ins.lookupWithIndex (fst consName) enumDef.dataCons of
    Just x -> pure x
    _ -> throw ctx.et consName $ "No such data constructor: " <> un (fst consName)
  consActualType <- case consActualTypeMaybe of
    Just x -> pure x
    _ -> throw ctx.et consName "Data constructor does not hold a value"
  (ctx', p) <- getMatchBranchCtx ctx innerPattern consActualType
  pure (ctx', I.PatternDataCons1 consIdx p)

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
    when (not ctx.inUnsafeCode && Attribute "Unsafe" `elem` attribs) $ addError ctx.et sr "Cannot access unsafe fields in safe code"
    e@(_, actualType, _) <- getExpr ctx (TypeHint expectedType) astEx >>= iCast expectedType
    unless (actualType == expectedType) $ do
      (act, ex) <- format2Types actualType expectedType
      addError ctx.et sr $ T.concat ["Wrong type for struct field ", un name, "\nExpected ", ex, ", got ", act]
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

getMemberFnsForType ::
  (MonadTc m) =>
  TcInputs ->
  I.Type ->
  m (Maybe (A.MemberFns, TFqn))
getMemberFnsForType tcIn lhsType = do
  getAstTDefCommonFromType tcIn lhsType >>= \case
    Just c -> case lhsType of
      I.ANamedType tdId -> do
        lhsTypeDef <- getTDef tdId
        let lhsTDCommon = I.tDefCommon lhsTypeDef
        pure $ Just (c.memberFns, lhsTDCommon.fqn)
      I.ArrayType _ _ ->
        pure $ Just (c.memberFns, TFqn "@stlib/primitives:Array")
      I.SliceType _ ->
        pure $ Just (c.memberFns, TFqn "@stlib/primitives:Slice")
      I.BoolType -> do
        pure $ Just (c.memberFns, TFqn "@stlib/primitives:Bool")
      I.NumPrimType numTyp -> do
        let name = numPrimTypeToText numTyp
        pure $ Just (c.memberFns, TFqn $ "@stlib/primitives:" <> name)
      _ -> pure Nothing
    _ -> pure Nothing

getTypeAccessExpr :: (MonadTc m) => Ctx -> TypeHint -> SrcRange -> Maybe A.TypeExpr -> VName' -> Maybe [A.GenericArg] -> m I.Expr
getTypeAccessExpr ctx hint sr astTypeExprMaybe (name, nameSr) gArgsMaybe = do
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
          I.AnEnumDef2 enumDef -> do
            case Ins.lookupWithIndex name enumDef.dataCons of
              Just x -> pure $ Just (enumDef, x)
              _ -> pure Nothing
          _ -> pure Nothing
      _ -> pure Nothing

  case (dataConsMaybe, typeOrNs) of
    (Just (enumDef, (consType, consIdx)), Right t) -> do
      case consType of
        Nothing -> do
          -- Data constructor does not hold a value so just produce a value of the enum type
          pure (I.DataConsExpr t consIdx Nothing, t, sr)
        Just dcType -> do
          -- Data constructor does hold a value so need to produce a function that returns the enum value

          let fnType = I.AFnType $ I.FnType [(Move, dcType)] False (Just t) False
          let fqn = VFqn $ un enumDef.e.c.fqn <> ".$" <> un name

          -- Function is cached
          vDefIdMaybe <- getCachedVDef fqn enumDef.e.c.genericArgs <&> (<&> fst)
          vDefId <- case vDefIdMaybe of
            Just x -> pure x
            Nothing -> do
              reachableFromStart <- getStartedFromStart
              let c =
                    I.VDefCommon
                      { name = (VName $ "_" <> un name, sr),
                        fqn = fqn,
                        genericArgs = enumDef.e.c.genericArgs,
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
              let body = Hir.ReturnStmnt (Just (Hir.DataConsExpr t consIdx (Just (getArg, sr)), sr)) []
              addFnDefBody vDefId (body, sr) True
              pure vDefId
          pure (I.LoadConstantExpr (I.ConstFnPtr vDefId), fnType, sr)
    (Nothing, Left (ns, ast, astImports)) -> do
      case HM.lookup name ast.vDefs of
        Nothing -> throw ctx.et sr $ "No such definition: " <> un name
        Just astVDef -> do
          let outerCtx = mkFileCtx ns (ast, astImports) ctx.tcIn
          let fqn = mkVFqn ns name
          args <- forM (fromMaybe [] gArgsMaybe) $ getGenArg ctx
          visitVDef ctx outerCtx args sr (fqn, astVDef) ctx.inUnsafeCode <&> getVDefExpr sr
    (Nothing, Right t) ->
      getMemberFnsForType ctx.tcIn t >>= \case
        Nothing ->
          throw ctx.et nameSr $ "Name not found: " <> un name
        Just (memberFns, lhsTFqn) ->
          case HM.lookup name (fst memberFns) of
            Nothing ->
              throw ctx.et nameSr $ "Name not found: " <> un name
            Just fnDef -> do
              let fqn = VFqn $ un lhsTFqn <> "." <> un (fst fnDef.c.name)

              typeCtx <- getTypeCtx ctx t <&> must -- Type has member functions and therefore has a context
              let fnAstGArgs = fromMaybe [] gArgsMaybe
              fnGArgs <- forM fnAstGArgs $ getGenArg ctx

              unless (length fnAstGArgs == length fnDef.c.genericParams)
                $ throw ctx.et sr "Wrong number of generic arguments to member function"

              (id, fnType, _) <- visitVDef ctx typeCtx fnGArgs sr (fqn, A.AFnDef fnDef) ctx.inUnsafeCode

              _ <- case (fnType, hint) of
                (I.AFnType f, FnReturningHint (TypeHint r))
                  | f.ret == Just t && isJust astTypeExprMaybe && r == t ->
                      pure () -- Could add a hint to use type inference
                (I.AFnType f, _)
                  | f.ret /= Just t && isNothing astTypeExprMaybe -> do
                      t' <- formatType False t
                      throw ctx.et sr $ "Member function has wrong return type, expected " <> t'
                _ -> pure ()

              pure (I.LoadConstantExpr $ I.ConstFnPtr id, fnType, sr)
    _ -> undefined

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
    addError ctx.et sr $ T.concat ["Error types do not match\nExpected ", retErrType', ", got ", errType']

  pure (I.BubbleExpr e'', dataType, sr)