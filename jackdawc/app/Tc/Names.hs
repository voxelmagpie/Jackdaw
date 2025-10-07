-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.Names where

import Ast qualified as A
import Control.Monad (foldM, forM, unless, when)
import Data.HashMap.Strict qualified as HM
import Data.List (init)
import Data.Maybe (mapMaybe)
import Data.Text qualified as T
import Hir qualified as H
import Names
import Prelude2
import Tc.Ctx
import Tc.Error (MonadTcError)
import Tc.State (MonadTc)
import Tc.TcErr

mkVFqn :: Namespace -> VName -> VFqn
mkVFqn (Namespace n) (VName n') = VFqn $ n <> ":" <> n'

mkTFqn :: Namespace -> TName -> TFqn
mkTFqn (Namespace n) (TName n') = TFqn $ n <> ":" <> n'

-- Resolves all imports in the source file with the given namespace and AST
getImports :: (MonadTcError m) => HashMap Namespace A.Ast -> Namespace -> A.Ast -> m [(Namespace, Maybe TName, ImportNames)]
getImports allAsts ns ast = do
  -- Extract @package_name and file path within the current package
  let allNsParts = T.split (== '/') (un ns)
  let pkg = must $ head allNsParts
  let nsParts = tail allNsParts
  assertM $ notNull nsParts

  xs <- forM ast.imports $ \(A.Import i sr qual names) -> do
    importNs <-
      if "@" `T.isPrefixOf` i
        then do
          -- Absolute path
          unless (HM.member (Namespace i) allAsts) $ throw [] sr "Invalid import path"
          pure (Namespace i)
        else do
          -- Relative path
          let astImportParts = T.split (== '/') i
          importParts <-
            foldM
              ( \importParts iPart ->
                  if iPart == ".."
                    then do
                      -- Go up a directory by removing the last element in the list
                      when (null importParts) $ throw [] sr "Import path may not escape the package"
                      pure $ init importParts
                    else
                      pure $ importParts ++ [iPart]
              )
              (init nsParts) -- Start by going up to the directory containing the current file
              astImportParts

          let importNs = Namespace $ T.intercalate "/" $ pkg : importParts
          unless (HM.member importNs allAsts) $ throw [] sr $ "Invalid import path: '" <> un importNs <> "'"
          pure importNs
    pure (importNs, fst <$> qual, names)

  let defaultImports =
        [ (Namespace "@stlib/stlib", Nothing, AllNames),
          (Namespace "@stlib/primitives", Nothing, AllNames),
          (Namespace "@stlib/string", Nothing, AllNames),
          (Namespace "@stlib/list", Nothing, AllNames),
          (Namespace "@stlib/maybe", Nothing, AllNames),
          (Namespace "@stlib/errors", Nothing, AllNames)
        ]
  pure $ defaultImports <> xs

data TNameLookupResult = NlType H.Type | NlTypeDef (Ctx, TFqn, A.AnyTSDef) | NlNamespace (Namespace, A.Ast, ImportsList)

-- Returned ctx is the outer context of the type definition (for types this is a file context)
-- This function returns a Type if the name leads to a generic argument
lookupTypeName :: (MonadTc m) => Ctx -> TName' -> m TNameLookupResult
lookupTypeName ctx (name, sr) = do
  case HM.lookup name ctx.tNameToGp of
    Just x ->
      pure $ NlType x
    _ ->
      -- Definitions in the current file are searched before imports
      case HM.lookup name ctx.thisAst.tsDefs of
        Just tsDef ->
          pure $ NlTypeDef (mkFileCtx' ctx, mkTFqn ctx.namespace name, tsDef)
        _ -> do
          let found = flip concatMap ctx.thisAstImports $ \(importNs, qualNameMaybe, names) ->
                let (ast, astImports) = must $ HM.lookup importNs ctx.tcIn.allAsts
                    qualResult = [(importNs, NlNamespace (importNs, ast, astImports)) | qualNameMaybe == Just name]
                    doCheck = case names of
                      AllNames -> True
                      VisibleNames ns -> un name `elem` ns
                      HiddenNames ns -> un name `notElem` ns
                 in if not doCheck
                      then
                        -- The name was not in the names list or was in the hidden names list,
                        -- no need to search the AST
                        qualResult
                      else case HM.lookup name ast.tsDefs of
                        Nothing -> qualResult
                        Just tsDef ->
                          let ctx' = mkFileCtx importNs (ast, astImports) ctx.tcIn
                           in (importNs, NlTypeDef (ctx', mkTFqn importNs name, tsDef)) : qualResult

          case found of
            [] -> throw ctx.et sr $ "Name not found: " <> un name
            ((ns, x) : xs) -> do
              -- The name may have been imported multiple times from the same namespace
              -- This is valid but need to check the name isn't both an imported name and a qualified ('as') name
              let isSame = \case (NlTypeDef _, NlTypeDef _) -> True; (NlNamespace _, NlNamespace _) -> True; _ -> False
              unless (all (\(ns', y) -> ns == ns' && isSame (x, y)) xs)
                $ throw ctx.et sr
                $ "Ambiguous name: "
                <> un name
              pure x

lookupVName :: (MonadTc m) => Ctx -> VName' -> m (Either (Ctx, VFqn, A.AnyVDef) H.Constant)
lookupVName ctx (name, sr) = do
  case HM.lookup name ctx.vNameToGp of
    Just x ->
      pure $ Right x
    _ ->
      case HM.lookup name ctx.thisAst.astVDefs.defs of
        Just vDef ->
          pure $ Left (mkFileCtx' ctx, mkVFqn ctx.namespace name, vDef)
        _ -> do
          let found = flip mapMaybe ctx.thisAstImports $ \(importNs, _, names) ->
                let doCheck = case names of
                      AllNames -> True
                      VisibleNames ns -> un name `elem` ns
                      HiddenNames ns -> un name `notElem` ns
                 in if not doCheck
                      then Nothing
                      else
                        let (ast, i) = must $ HM.lookup importNs ctx.tcIn.allAsts
                            defMaybe = HM.lookup name ast.astVDefs.defs
                         in case defMaybe of Just x -> Just (importNs, ast, i, x); _ -> Nothing

          case found of
            [] -> throw ctx.et sr $ "Name not found: " <> un name
            ((ns, ast, imports, tsDef) : xs) -> do
              unless (all ((== ns) . \(n, _, _, _) -> n) xs)
                $ throw ctx.et sr
                $ "Ambiguous name: "
                <> un name
              pure $ Left (mkFileCtx ns (ast, imports) ctx.tcIn, mkVFqn ns name, tsDef)
