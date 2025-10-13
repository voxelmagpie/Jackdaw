-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use maybe" #-}
module C (evalCExpr, jdTypeToText, translateFile, CException (..)) where

import Control.Exception (Exception, handle, throwIO)
import Control.Monad (forM, forM_, unless, void, when)
import Data.Bits (Bits (complement, shift), (.&.), (.|.))
import Data.Char (ord)
import Data.Foldable (find)
import Data.HashTable.IO qualified as HT
import Data.IORef (modifyIORef', readIORef, writeIORef)
import Data.Maybe (fromMaybe, isNothing, mapMaybe)
import Data.Text qualified as T
import GHC.IORef (IORef, newIORef)
import Language.C
import Language.C.Data.Ident (Ident (Ident))
import Names
import Numeric (showHex)
import Prelude2
import State

newtype CException = CException Text
  deriving (Show)
  deriving anyclass (Exception)

getNextAnonId :: State -> IO Text
getNextAnonId s = do
  i <- readIORef s.nextAnonId
  writeIORef s.nextAnonId (i + 1)
  pure $ T.pack $ show i

getTypeSpecs :: [CDeclarationSpecifier a] -> [CTypeSpecifier a]
getTypeSpecs ts = flip mapMaybe ts $ \case CTypeSpec t -> Just t; _ -> Nothing

translateFile :: State -> [CExternalDeclaration NodeInfo] -> IO ()
translateFile s decls = do
  forM_ decls $ \case
    -- Structs, typedefs
    CDeclExt x -> case x of
      CDecl declSpecs xs _ ->
        case declSpecs of
          -- Typedef
          (CStorageSpec (CTypedef _) : ts) -> do
            case xs of
              [(Just (CDeclr (Just ident) deriv _ _ _), Nothing, Nothing)] -> do
                let ident' = identToText ident
                let typeSpecs = getTypeSpecs ts
                handle (\(CException msg) -> addLine s $ "// Skipped typedef " <> ident' <> ": " <> msg) $ do
                  case (typeSpecs, deriv) of
                    ([CVoidType _], []) -> do
                      HT.insert s.nameMap (identToText ident) "void"
                      showAndThrow "typedef void" typeSpecs
                    _ -> pure ()
                  t <- processType s (Just $ toTsDefNamingConv ident) False typeSpecs deriv
                  name <- forceTsDefNamingConv s ident
                  unless (name == t) $ addLine s $ "@Unsafe alias " <> name <> " = " <> t
              a -> do
                traceM "Invalid typedef"
                traceShowM a
                addLine s "// Skipped typedef"
          ts -> do
            let typeSpecs = getTypeSpecs ts
            case xs of
              -- Function declaration
              [(Just (CDeclr (Just ident) (CFunDeclr (Right (params, isVarArgs)) _ _ : deriv) _ _ _), Nothing, Nothing)] -> do
                let name = identToText ident
                handle (\(CException msg) -> addLine s $ "// Skipped " <> name <> ": " <> msg) $ do
                  ret <- processType s Nothing False typeSpecs deriv
                  unless (isVDefNamingConv name) $ throwIO $ CException "Naming convention"
                  addNameUnmodified s ident

                  params' <- forM params $ \case
                    (CDecl pDeclSpecs ys _) -> do
                      let pTypeSpecs = getTypeSpecs pDeclSpecs
                      paramType <- case ys of
                        [(Just (CDeclr _ pDeriv _ _ _), _, _)] -> processType s Nothing True pTypeSpecs pDeriv
                        _ -> processType s Nothing True pTypeSpecs []

                      -- C array parameters are actually pointers
                      let paramType' = if "Array[" `T.isPrefixOf` paramType then T.cons '*' paramType else paramType

                      let nameMaybe = case ys of
                            [(Just (CDeclr identMaybe _ _ _ _), Nothing, Nothing)] -> identMaybe
                            _ -> Nothing

                      let p = case nameMaybe of
                            Just n -> toVDefNamingConv n <> ": " <> paramType'
                            _ -> paramType'
                      pure $ if paramNeedsVarKw paramType' then "var " <> p else p
                    p -> showAndThrow "Invalid parameter" p

                  let params'' = if params' == ["void"] then [] else params'
                  let params''' = if isVarArgs then params'' ++ ["..."] else params''

                  case ret of
                    "void" -> addLine s $ "@Unsafe fn " <> name <> " (" <> T.intercalate ", " params''' <> ")"
                    _ -> addLine s $ "@Unsafe fn " <> name <> " (" <> T.intercalate ", " params''' <> "): " <> ret
              -- Struct/enum def
              [] ->
                handle (\(CException e) -> addLine s $ "// Skipped: " <> e) $ do
                  -- processType will add the struct definition
                  void $ processType s Nothing False typeSpecs []
              -- Extern const
              [(Just (CDeclr (Just ident) deriv _ _ _), Nothing, Nothing)] -> do
                let name = identToText ident
                handle (\(CException msg) -> addLine s $ "// Skipped " <> name <> ": " <> msg) $ do
                  t <- processType s Nothing False typeSpecs deriv
                  unless (isVDefNamingConv name) $ throwIO $ CException "Naming convention"
                  addLine s $ "@Unsafe const " <> name <> ": " <> t
              _ -> traceShow xs $ addLine s "// Skipping ??"
      CStaticAssert {} -> trace "static assert" $ pure ()
    -- Functions (definitions rather than declarations)
    CFDefExt (CFunDef _ (CDeclr identMaybe _ _ _ _) _ _ _) -> do
      let i = fromMaybe "" $ identMaybe <&> identToText
      addLine s $ "// Skipping function definition " <> i
    d -> traceShow d $ pure ()

  flip HT.mapM_ s.gotStructDef $ \(name, fullDefSeen) ->
    unless fullDefSeen $ addLine s $ "@Unsafe struct " <> name <> " { dummyStruct: I8 }"

showAndThrow :: (Show a) => Text -> a -> IO b
showAndThrow err x = trace (T.unpack err) $ traceShow x $ throwIO $ CException err

-- TODO Convert into JD source instead of evaluating?

data JdType = JdInt Integer Bool | JdChar Char | JdFloat Text | JdString Text | JdCast Text JdType | JdSizeOf Text
  deriving (Show, Eq, Generic)

evalCExpr :: State -> [(Text, JdType)] -> CExpr -> IO JdType
evalCExpr s vars = \case
  (CVar ident _) ->
    case find (fst >>> (== identToText ident)) vars of
      Just (_, x) -> pure x
      _ -> throwIO $ CException $ "Unknown variable: " <> identToText ident
  (CConst (CIntConst (CInteger x HexRepr _) _)) -> pure $ JdInt x True
  (CConst (CIntConst (CInteger x _ _) _)) -> pure $ JdInt x False
  (CConst (CCharConst (CChar x _) _)) -> pure $ JdChar x
  (CConst (CFloatConst (CFloat x) _)) -> pure $ JdFloat $ T.pack x
  (CConst (CStrConst (CString x _) _)) -> pure $ JdString $ T.pack x
  (CUnary CMinOp e _) ->
    evalCExpr s vars e >>= \case
      JdInt x isHex -> pure $ JdInt (-x) isHex
      JdFloat x ->
        pure $ JdFloat $ if T.head x == '-' then T.tail x else T.cons '-' x
      x -> showAndThrow "Unexpected value for unary -" x
  (CUnary CCompOp e _) ->
    evalCExpr s vars e >>= \case
      JdInt x isHex -> pure $ JdInt (complement x) isHex
      x -> showAndThrow "Unexpected value for unary ~" x
  (CBinary op l r _) -> do
    l' <- evalCExpr s vars l
    r' <- evalCExpr s vars r
    case (l', r') of
      (JdInt x isHex, JdInt y isHex') ->
        evalIntBinOp op x y <&> \z -> JdInt z (isHex || isHex')
      x -> showAndThrow "Unexpected input for binary op" x
  (CCast (CDecl declSpecs [] _) e _) -> do
    t <- processType s Nothing False (getTypeSpecs declSpecs) []
    evalCExpr s vars e <&> JdCast t
  (CCast (CDecl declSpecs [(Just (CDeclr Nothing deriv _ _ _), _, _)] _) e _) -> do
    t <- processType s Nothing False (getTypeSpecs declSpecs) deriv
    evalCExpr s vars e <&> JdCast t
  (CSizeofType (CDecl declSpecs [] _) _) -> do
    t <- processType s Nothing False (getTypeSpecs declSpecs) []
    pure $ JdSizeOf t
  (CSizeofType (CDecl declSpecs [(Just (CDeclr Nothing deriv _ _ _), _, _)] _) _) -> do
    t <- processType s Nothing False (getTypeSpecs declSpecs) deriv
    pure $ JdSizeOf t
  e -> showAndThrow "C const eval error" e

evalIntBinOp :: CBinaryOp -> Integer -> Integer -> IO Integer
evalIntBinOp op x y = case op of
  CAddOp -> pure $ x + y
  CSubOp -> pure $ x - y
  CMulOp -> pure $ x * y
  CDivOp -> pure $ x `div` y
  COrOp -> pure $ x .|. y
  CAndOp -> pure $ x .&. y
  CShlOp -> pure $ x `shift` fromIntegral y
  CShrOp -> pure $ x `shift` (-(fromIntegral y))
  _ -> showAndThrow "Unknown int op" op

intToHex :: Integer -> Text
intToHex x | x < 0 = T.pack $ '-' : '0' : 'x' : showHex (-x) ""
intToHex x = T.pack $ '0' : 'x' : showHex x ""

jdTypeToText :: JdType -> (Text, Text)
jdTypeToText = \case
  JdInt x True -> (pickIntType x, intToHex x)
  JdInt x _ -> (pickIntType x, tShow x)
  JdChar x -> ("I32", tShow (ord x))
  -- JdChar x | ord x <= 0xffff -> ("I32", "'\\u" <> T.pack (printf "\'%04x\'" (ord x)) <> "'")
  -- JdChar x -> ("I32", "'\\U" <> T.pack (printf "\'%08x\'" (ord x)) <> "'")
  JdFloat x -> ("F64", x)
  JdString x -> ("String", "\"" <> x <> "\"")
  JdCast t x -> (t, "(" <> snd (jdTypeToText x) <> ") as " <> t)
  JdSizeOf t -> ("I32", "sizeOf[" <> t <> "]")

pickIntType :: Integer -> Text
pickIntType x
  | x >= -2147483648 && x <= 2147483647 = "I32"
  | x <= 9223372036854775807 = "I64"
  | otherwise = "U64"

addNameUnmodified :: State -> Ident -> IO ()
addNameUnmodified s x = let x' = identToText x in HT.insert s.nameMap x' x'

-- Gets the Jackdaw name for the given C name or returns the C name if there is no entry for this name
mapName' :: State -> Text -> IO Text
mapName' s x = do
  y <- HT.lookup s.nameMap x
  case y of
    Just x' -> if x == x' then pure x' else mapName s x'
    _ -> pure x

-- Gets the Jackdaw name for the given C name or throws if there is no such name
mapName :: State -> Text -> IO Text
mapName s x = do
  y <- HT.lookup s.nameMap x
  case y of
    Just x' -> if x == x' then pure x else mapName' s x'
    _ -> throwIO $ CException $ "Name not found: " <> x

-- Translates a struct type, may be named or anonymous
processCSUType :: State -> Maybe Text -> CStructureUnion NodeInfo -> IO Text
-- Struct
processCSUType s nameMaybe (CStruct CStructTag identMaybe (Just decls) _ _) =
  createStructUnion s False identMaybe decls nameMaybe
-- Struct forward declaration
processCSUType s _ (CStruct CStructTag (Just ident) Nothing _ _) = do
  let name = "S_" <> identToText ident
  x <- HT.lookup s.gotStructDef name
  when (isNothing x) $ HT.insert s.gotStructDef name False
  pure name
-- Union
processCSUType s nameMaybe (CStruct CUnionTag identMaybe (Just decls) _ _) =
  createStructUnion s True identMaybe decls nameMaybe
-- Union forward declaration
processCSUType s _ (CStruct CUnionTag (Just ident) Nothing _ _) = do
  let name = "U_" <> identToText ident
  x <- HT.lookup s.gotUnionDef name
  when (isNothing x) $ HT.insert s.gotUnionDef name False
  pure name
processCSUType _ _ s = showAndThrow "Invalid struct" s

createStructUnion :: State -> Bool -> Maybe Ident -> [CDeclaration NodeInfo] -> Maybe Text -> IO Text
createStructUnion s isUnion identMaybe decls nameMaybe = do
  let letter = if isUnion then "U" else "S"
  name <- case (identMaybe, nameMaybe) of
    (Just x, _) ->
      pure $ letter <> "_" <> identToText x
    (_, Just n) ->
      pure n
    (_, _) ->
      (\x -> "A" <> letter <> "_" <> x) <$> getNextAnonId s

  if isUnion
    then
      HT.insert s.gotUnionDef name True
    else
      HT.insert s.gotStructDef name True

  fields <- forM decls $ \case
    CDecl declSpecs xs _ -> do
      let typeSpecs = getTypeSpecs declSpecs

      forM xs $ \case
        (Just (CDeclr identMaybe' deriv _ _ _), _, _) ->
          case identMaybe' of
            Just x -> do
              t <- processType s Nothing False typeSpecs deriv
              pure
                $ if isUnion
                  then
                    "\t" <> toVDefNamingConv x <> "(" <> t <> ")"
                  else
                    "\t" <> toVDefNamingConv x <> ": " <> t
            _ -> throwIO $ CException "No field name"
        _ -> showAndThrow "Invalid field" xs
    _ -> pure []

  -- Add these lines now in case the fields threw an exception

  if isUnion
    then
      addLine s $ "union " <> name <> " {"
    else
      addLine s $ "@Unsafe\nstruct " <> name <> " {"

  addLine s $ T.intercalate ",\n" $ concat fields
  addLine s "}"

  pure name

processCEnumType :: State -> Maybe Text -> CEnumeration NodeInfo -> IO Text
-- Forward declaration
processCEnumType s _ (CEnum (Just ident) Nothing _ _) = do
  forceTsDefNamingConv s ident
processCEnumType s nameMaybe (CEnum identMaybe fields' _ _) = do
  let fields = fromMaybe [] fields'

  (name, constsType) <- case identMaybe of
    Just ident -> do
      -- The enum has a name, e.g. enum foo {...}
      -- Use this name as the type of the enum
      name <- forceTsDefNamingConv s ident
      addLine s $ "@Unsafe alias " <> name <> " = I32"
      pure (name, name)
    _ ->
      -- Anonymous enum, make it an I32
      -- If this enum is part of a typedef then use that name
      pure ("I32", fromMaybe "I32" nameMaybe)

  handle (\(CException msg) -> addLine s $ "// Skipped (rest of) enum " <> constsType <> ": " <> msg) $ do
    i <- newIORef (-1)
    fieldValues :: IORef [(Text, Integer)] <- newIORef []

    forM_ fields $ \(fieldName, valueMaybe) -> do
      isHex <- case valueMaybe of
        -- Autoincrementing enum value
        Nothing -> modifyIORef' i (+ 1) >> pure False
        -- Explicit enum value
        Just e -> do
          names <- readIORef fieldValues <&> (<&> \(n, x) -> (n, JdInt x False))
          value <- evalCExpr s names e
          case value of
            JdInt i' isHex -> do
              writeIORef i i'
              pure isHex
            _ -> showAndThrow "Invalid enum value expression" e

      i' <- readIORef i
      fieldName' <- forceVDefNamingConv s fieldName
      modifyIORef' fieldValues ((fieldName', i') :)

      -- If an exception is thrown then the constants before the invalid one are still written
      let i'' = if isHex then intToHex i' else tShow i'
      addLine s $ "@Unsafe const " <> fieldName' <> ": " <> constsType <> " = " <> i''

  pure name

processType :: State -> Maybe Text -> Bool -> [CTypeSpecifier NodeInfo] -> [CDerivedDeclarator NodeInfo] -> IO Text
processType s nameMaybe isParam xs deriv = processType' s nameMaybe xs >>= flip (applyDeriv s isParam) deriv

processType' :: State -> Maybe Text -> [CTypeSpecifier NodeInfo] -> IO Text
processType' s nameMaybe xs = do
  -- unsigned xxx, signed xxx
  let (xs', signed) = case head xs of
        CSignedType _ -> (tail xs, True)
        CUnsigType _ -> (tail xs, False)
        _ -> (xs, True)

  case (xs', signed) of
    ([CVoidType _], _) -> pure "void"
    ([CCharType _], True) -> pure "I8"
    ([CCharType _], False) -> pure "U8"
    (CShortType _ : _, True) -> pure "I16"
    (CShortType _ : _, False) -> pure "U16"
    ([CIntType _], True) -> pure "I32"
    ([CIntType _], False) -> pure "U32"
    ([], True) -> pure "I32"
    ([], False) -> pure "U32"
    (CLongType _ : _, True) -> pure "I64"
    (CLongType _ : _, False) -> pure "U64"
    ([CFloatType _], _) -> pure "F32"
    ([CDoubleType _], _) -> pure "F64"
    ([CBoolType _], _) -> pure "Bool"
    ([CTypeDef (Ident "__builtin_va_list" _ _) _], _) -> throwIO $ CException "__builtin_va_list"
    ([CTypeDef ident _], _) -> mapName s $ identToText ident
    ([CSUType x _], _) -> processCSUType s nameMaybe x
    ([CEnumType x _], _) -> processCEnumType s nameMaybe x
    _ -> showAndThrow "Unknown type(2)" xs'

applyDeriv :: State -> Bool -> Text -> [CDerivedDeclarator NodeInfo] -> IO Text
applyDeriv s isParam t xs = applyDeriv' s isParam t (reverse xs)

applyDeriv' :: State -> Bool -> Text -> [CDerivedDeclarator NodeInfo] -> IO Text
applyDeriv' s isParam type' = \case
  [] -> pure type'
  (CArrDeclr _ (CArrSize False e) _ : xs) -> do
    sz <- evalCExpr s [] e >>= \case JdInt i _ -> pure i; x -> showAndThrow "Expected int" x
    applyDeriv' s isParam ("Array[" <> type' <> ", " <> tShow sz <> "]") xs
  -- Pointer to unsized array is just a pointer to the first element in the array
  (CArrDeclr _ (CNoArrSize False) _ : CPtrDeclr _ _ : xs) ->
    applyDeriv' s isParam ("*" <> type') xs
  -- Unsized arrays can be parameters, in which case they are just pointers
  -- Unsized arrays are not supported as struct fields
  [CArrDeclr _ (CNoArrSize False) _] -> do
    unless isParam $ throwIO $ CException "Unsized array"
    pure ("*" <> type')
  -- Function pointer
  (CFunDeclr (Right (params, isVarArgs)) _ _ : CPtrDeclr _ _ : xs) -> do
    params' <- forM params $ \case
      CDecl declSpecs ys _ -> do
        let typeSpecs = getTypeSpecs declSpecs
        t <- case ys of
          [(Just (CDeclr _ deriv _ _ _), _, _)] -> processType s Nothing True typeSpecs deriv
          _ -> processType s Nothing True typeSpecs []
        let t' = if "Array[" `T.isPrefixOf` t then T.cons '*' t else t
        pure $ if paramNeedsVarKw t' then "var " <> t' else t'
      x -> showAndThrow "Invalid parameter" x

    let params'' = if params' == ["void"] then [] else params'
    let params''' = if isVarArgs then params'' ++ ["..."] else params''

    case type' of
      "void" -> applyDeriv' s isParam ("?fn (" <> T.intercalate ", " params''' <> ")") xs
      _ -> applyDeriv' s isParam ("?fn (" <> T.intercalate ", " params''' <> "): " <> type') xs
  (CPtrDeclr _ _ : xs) ->
    applyDeriv' s isParam (T.cons '*' type') xs
  ds -> showAndThrow "Unknown [CDerivedDeclarator] " ds

paramNeedsVarKw :: Text -> Bool
paramNeedsVarKw x = T.head x `notElem` ['*', '?'] && not ("fn " `T.isPrefixOf` x) && x `notElem` prims
  where
    prims = ["void", "Bool", "I8", "I16", "I32", "I64", "U8", "U16", "U32", "U64", "F32", "F64"]
