-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module ParserHelperCode where

import Ast qualified as A
import Control.Monad (unless, when)
import Control.Monad.Reader (MonadReader (ask), ReaderT (..))
import Data.Bits (Bits (complement))
import Data.Either (isRight)
import Data.HashMap.Strict qualified as HM
import Data.Int (Int64)
import Data.Maybe (isJust, mapMaybe)
import Data.Text qualified as T
import HashMultiMap qualified as HMM
import Names
import Prelude2
import SrcLoc
import Tokens

type ParseM = ReaderT FilePath (Either (Text, SrcRange))

parseError :: ([TokenL], [String]) -> ParseM a
parseError ([], _) = let x = SrcLoc 0 0 in ask >>= \n -> throwError ("Unexpected EOF", SrcRange n x x)
parseError ((token, r@(SrcRange srcPath' l _)) : _, strings) =
  throwError (msg, r)
  where
    msg1 = "Parse error at token " <> prettyPrintToken token <> " in " <> T.pack srcPath' <> ":" <> tShow l.line
    msg =
      if null strings
        then msg1 <> "\n"
        else
          T.concat
            [ msg1,
              ":\nPossible next tokens: ",
              T.intercalate ", " $ T.pack <$> strings
            ]

range :: TokenL -> TokenL -> SrcRange
range (_, SrcRange f l _) (_, SrcRange _ _ r) = SrcRange f l r

getTypeName :: TokenL -> TName
getTypeName (TypeName x, _) = x
getTypeName _ = error "Not a type name"

getValueName :: TokenL -> VName
getValueName (IdentOrKw x, _) = x
getValueName _ = error "Not a value name"

getOp :: TokenL -> OpName'
getOp (Op x, r) = (x, r)
getOp _ = error "Not an operator"

getFloatLit :: TokenL -> Text
getFloatLit (FloatLiteral x, _) = x
getFloatLit _ = error "Not a float"

getIntLit :: TokenL -> Integer
getIntLit (IntLiteral x, _) = x
getIntLit _ = error "Not an int"

getInt64Lit :: TokenL -> ParseM Int64
getInt64Lit (IntLiteral x, sr) =
  if x >= 0 && x <= 18446744073709551615 then pure $ fromIntegral x else throwError ("Int out of range", sr)
getInt64Lit _ = error "Not an int"

getStringLit :: TokenL -> Text
getStringLit (StringLiteral x, _) = x
getStringLit _ = error "Not a string"

getCharLit :: TokenL -> Char
getCharLit = \case (CharLiteral c, _) -> c; _ -> error "Not a character literal"

liftExprMaybe :: (Maybe A.Expr', SrcRange) -> Maybe A.Expr
liftExprMaybe (Just e, r) = Just (e, r)
liftExprMaybe (Nothing, _) = Nothing

addVDef :: A.VDefs -> (VName', A.AnyVDef) -> ParseM A.VDefs
addVDef vDefs ((n, sr), d) = do
  m <- hmTryInsert sr n d vDefs.defs
  let opVDefs = case (A.vDefCommon d).opMaybe of
        Just o -> HMM.insert (fst o) d vDefs.operators
        _ -> vDefs.operators
  pure $ A.VDefs m opVDefs

hmTryInsert :: (Hashable k, Eq k) => SrcRange -> k -> v -> HashMap k v -> ParseM (HashMap k v)
hmTryInsert sr key !val m = do
  when (isJust $ HM.lookup key m) $ throwError ("Duplicate name", sr)
  pure $ HM.insert key val m

mkExprStmnt :: A.Expr -> ParseM A.Statement
mkExprStmnt (A.AFnCallExpr f, sr) = pure (A.FnCallStmnt (f, sr), sr)
mkExprStmnt (A.BubbleExpr e, sr) = pure (A.BubbleStmnt e, sr)
mkExprStmnt (_, sr) = throwError ("Expected function call", sr)

getPrefixOpExpr :: OpName' -> A.Expr -> A.Expr'
getPrefixOpExpr (OpName "-", _) (A.FloatLitExpr i, _) =
  A.FloatLitExpr $ if "-" `T.isPrefixOf` i then T.tail i else "-" <> i
getPrefixOpExpr (OpName "-", _) (A.IntLitExpr i, _) =
  A.IntLitExpr (-i)
getPrefixOpExpr (OpName "~", _) (A.IntLitExpr i, _) =
  A.IntLitExpr (complement i)
getPrefixOpExpr op e =
  A.APrefixOpExpr $ A.PrefixOpExpr op e

getParams :: [Either a SrcRange] -> ParseM ([a], Bool)
getParams xs = do
  isVarArgs <- case findWithIndex isRight xs of
    Just (Right sr, i) -> do
      unless (length xs > 1 && i == (length xs - 1)) $ throwError ("Var-args (...) must be after parameters", sr)
      pure True
    _ ->
      pure False
  pure (flip mapMaybe xs $ \case Left x -> Just x; _ -> Nothing, isVarArgs)
