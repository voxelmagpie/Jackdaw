-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use head" #-}
module Tc.Borrow (runBorrowChecker) where

import AccessMode
import Control.Monad (forM, forM_, unless, when)
import Data.Foldable (find)
import Data.Functor (($>))
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe, maybeToList)
import Data.Text qualified as T
import Hir qualified as H
import Names (Attribute (Attribute), VName (VName))
import Prelude2
import SrcLoc
import Tc.Error qualified as E
import Tc.State
import Tc.TcIr qualified as I

runBorrowChecker :: (MonadBrwChk m) => BwCheckFnType m
runBorrowChecker s' params sr fnIsAcc = do
  forM_ params $ \((mode, _), (nameMaybe, uid), dropFn) -> do
    let ref = if mode == Move then Nothing else Just (AccLocalVar uid)
    addVar uid (maybe (VName "_") fst nameMaybe) ref dropFn 0 0 0
    when (mode == Shared)
      $ markBorrowed (uid, SharedBorrow, sr)

  (s'', terminates) <- borrowCheckStmnt def {inAccessorFn = fnIsAcc} s'

  -- Get drop functions for outermost statement
  ds <- copyVarsList <&> mapMaybe getDropFnForVarMaybe
  pure $ case s'' of
    (H.CodeBlockStmnt ss ds', ln) ->
      ((H.CodeBlockStmnt ss $ ds' <> ds, ln), terminates)
    (_, ln) -> ((H.CodeBlockStmnt [s''] ds, ln), terminates)

data Ctx = Ctx
  { loopDepth :: LoopCounter,
    refVarsList :: [H.LocalVarUid],
    tryCtr :: TryCounter,
    tryCatchCtr :: TryCatchCounter,
    inAccessorFn :: Bool
  }
  deriving (Show, Generic, Default)

throw :: (MonadBrwChk m, HasSrcRange r) => r -> Text -> m a
throw sr msg = do
  et <- getEt
  E.throw E.BorrowCheckerError et sr msg

addError :: (MonadBrwChk m, HasSrcRange r) => r -> Text -> m ()
addError sr msg = do
  et <- getEt
  E.addError E.BorrowCheckerError et sr msg

type ExprOrAccExpr = Either H.Expr (H.AccessorExpr, AccessorTo)

type ExprOrAccExpr' = Either H.Expr' (H.AccessorExpr', AccessorTo)

-- Dereferences the given accessor (l-value) expression (unless already an r-value)
-- and restores the borrow state to the given state
accessorIntoExpr :: (MonadBrwChk m) => SrcRange -> Borrows -> (ExprOrAccExpr, H.Type) -> m H.Expr
accessorIntoExpr _ b (Left x, _) = restoreBorrowState b >> pure x
accessorIntoExpr sr b (Right (accExpr, AccRawPtr), _) =
  -- Raw pointers bypass move semantics
  restoreBorrowState b $> (H.DerefAccessorExpr accExpr, sr)
accessorIntoExpr sr b (Right (accExpr, _), t) = do
  copy <- getTypeIsCopyableFn >>= \f -> f t
  unless copy $ addError sr "Cannot move or copy value"
  restoreBorrowState b
  pure (H.DerefAccessorExpr accExpr, sr)

getDropFnForVarMaybe :: Var -> Maybe (H.LocalVarUid, H.DropFn)
getDropFnForVarMaybe v = case v.dropFn of Just d' | not v.moved && v.initialised -> Just (v.uid, d'); _ -> Nothing

-- Compares the state of variables before and after an if/else or match
-- Checks that the initialised and moved variables are consistent on each branch
-- Caller has already identified branches which are guaranteed to terminate (throw/panic/return)
-- from the list of var lists and passed Nothing instead of Just [Var] for that entry in updatedVarsLists
-- Returns a list of drop functions to run for each branch
checkMovedInitedVarsAndGetDropFns :: (MonadBrwChk m) => SrcRange -> [Var] -> [Maybe [Var]] -> m [H.DropFns]
checkMovedInitedVarsAndGetDropFns sr varsBefore updatedVarsLists = do
  -- Filter out the branches that terminate
  let updatedVarsListsNoTerm = catMaybes updatedVarsLists

  -- List of lists of vars which were uninitialised before but are initialised now
  let initialisedVarsLists =
        updatedVarsListsNoTerm <&> \l ->
          zip varsBefore l
            & filter (\(bef, aft) -> not bef.initialised && aft.initialised)
            & (<&> snd)

  -- Check all initialised vars are consistent
  unless (all (== must (head initialisedVarsLists)) initialisedVarsLists)
    -- Not consistent, find the first inconsistency
    $ forM_ initialisedVarsLists
    $ \l ->
      forM_ l $ \v -> do
        let initedOnAllBranches = all (\l' -> v.uid `elem` ((.uid) <$> l')) initialisedVarsLists
        unless initedOnAllBranches $ addError sr $ un v.name <> " is not initialised in every branch"

  forM_ (concat initialisedVarsLists) $ \v -> markVarInitialised v.uid

  -- Gather list of all moved variables (may contain duplicates)
  -- Lists don't have to be the same, variables moved on one branch but not the other will be dropped on the
  -- branch where they are not moved
  let allMoved =
        flip concatMap updatedVarsListsNoTerm $ \l ->
          zip varsBefore l
            & filter (\(bef, aft) -> not bef.moved && aft.moved)
            & (<&> snd)

  forM_ allMoved $ \v -> markVarMoved v.uid

  pure
    $ flip fmap updatedVarsLists
    $ \case
      Nothing ->
        [] -- Terminates, no additional drop functions to run
      Just l ->
        flip
          mapMaybe
          l
          $ \v ->
            if not v.moved && (v.uid `elem` (allMoved <&> (.uid)))
              then -- Moved on another branch so drop
                getDropFnForVarMaybe v
              else
                Nothing

-- Borrow checks each argument separately, resulting borrow states are then merged
-- This allows for code such as `f(x, x.a + 1)` where the first parameter is an exclusive reference
getArgsExprAndBorrows ::
  (MonadBrwChk m) => Ctx -> [(AccessMode, (I.Expr, Maybe I.VDefId))] -> m [(H.FnArg, Borrows)]
getArgsExprAndBorrows ctx args =
  forM args $ \(argMode', (argExpr, dropFn)) -> do
    isCopy <- getTypeIsCopyableFn >>= \f -> f $ snd3 argExpr
    -- Moving a copyable value is just copying. Access it by shared reference then copy
    let argMode = if argMode' == Move && isCopy then Shared else argMode'

    -- Borrow check the arg, get the new borrows, restore the borrow state
    b <- copyBorrowState
    argExpr'@(argExprOrAccExpr, _) <- borrowCheckExpr ctx argMode argExpr
    b' <- copyBorrowState
    let newBws = take (length b' - length b) b'
    restoreBorrowState b

    case (argExprOrAccExpr, argMode) of
      -- R-value
      (Left e', Move) -> pure (H.RValueArg e', [])
      -- R-value -> reference
      (Left e', _) -> pure (H.RValueRefArg (e', argMode, dropFn), [])
      -- Reference -> r-value
      (Right _, Move) -> accessorIntoExpr (thd3 argExpr) b argExpr' <&> \e' -> (H.RValueArg e', [])
      -- Shared reference to copyable -> r-value
      (Right (e', _), Shared) | isCopy -> pure (H.RValueRefArg ((H.DerefAccessorExpr e', thd3 argExpr), argMode, dropFn), [])
      -- Reference, keep the new borrows in this case as the argument is a reference (RefArg)
      (Right (e', _), _) -> pure (H.RefArg (e', argMode), newBws)

-- Applies the borrows for a function call one by one
applyArgsBorrows :: (MonadBrwChk m) => [Borrow] -> m ()
applyArgsBorrows newBorrows =
  forM_ newBorrows $ \(uid, bwType, sr) -> do
    b <- getBorrow uid
    case (bwType, b) of
      (ExclusiveBorrow, Nothing) -> do
        markBorrowed (uid, ExclusiveBorrow, sr)
      (ExclusiveBorrow, Just (_, _, SrcRange _ sr0' _)) ->
        throw sr $ "Invalid (exclusive) borrow in function arguments, due to borrow on line " <> tShow sr0'.line
      (SharedBorrow, Nothing) -> do
        markBorrowed (uid, SharedBorrow, sr)
      (SharedBorrow, Just (_, SharedBorrow, _)) -> do
        markBorrowed (uid, SharedBorrow, sr)
      (SharedBorrow, Just (_, ExclusiveBorrow, SrcRange _ sr0' _)) ->
        throw sr $ "Invalid (shared) borrow in function arguments, due to borrow on line " <> tShow sr0'.line

borrowCheckFnCall :: (MonadBrwChk m) => Ctx -> I.FnCallExpr -> m (H.FnCallExpr, Maybe H.Type)
borrowCheckFnCall ctx e = do
  b <- copyBorrowState

  -- Get function and restore borrow state
  calleeExprOrAccExpr@(_, calleeType) <- borrowCheckExpr ctx Shared e.fn
  calleeExpr@(_, _) <- accessorIntoExpr (thd3 e.fn) b calleeExprOrAccExpr

  let (paramsModes, retType) = case calleeType of
        H.AFnType f -> ((f.params <&> fst) ++ repeat Move, f.ret)
        _ -> error "Not a function type"

  -- Get arguments
  argsAndNewBorrows <- getArgsExprAndBorrows ctx $ zip paramsModes e.args
  applyArgsBorrows $ concatMap snd argsAndNewBorrows
  restoreBorrowState b

  -- Get the drop functions to run if the called function throws an exception
  toDrop <- if e.fnIsNoThrow then pure Nothing else getThrowDropFns ctx <&> Just
  pure (H.FnCallExpr calleeExpr (fst <$> argsAndNewBorrows) toDrop, retType)

borrowCheckExpr :: (MonadBrwChk m) => Ctx -> AccessMode -> I.Expr -> m (ExprOrAccExpr, H.Type)
borrowCheckExpr ctx mode e@(_, _, sr) = do
  (e', t) <- borrowCheckExpr' ctx mode e
  -- Add source location information
  pure $ case e' of
    Left e'' -> (Left (e'', sr), t)
    Right (e'', to) -> (Right ((e'', sr), to), t)

borrowCheckExpr' :: (MonadBrwChk m) => Ctx -> AccessMode -> I.Expr -> m (ExprOrAccExpr', H.Type)
borrowCheckExpr' ctx mode (expr, t, sr@(SrcRange fileName' sr0 _)) = case expr of
  I.LoadConstantExpr x -> do
    when (mode == Exclusive) $ addError sr "Cannot mutate constants"
    let isSmallType = case x of
          H.ConstInt _ -> True
          H.ConstFloatOrDouble _ -> True
          H.ConstBool _ -> True
          H.ConstNullPtr -> True
          H.ConstStructOrTuple _ -> False
          H.ConstArray _ _ -> False
          H.ConstSizeof _ -> True
          H.ConstFnPtr _ -> True
          H.ConstExtern _ -> False
          H.ConstAddrOf _ -> True
          H.ConstAddrOfArray0 _ -> True
          H.ConstEnum _ -> True -- Only for data constructors with no value
    pure
      $ if not isSmallType
        then
          (Right (H.ConstantAccessorExpr (x, t), AccStatic), t)
        else
          (Left $ H.LoadConstantExpr (x, t), t)
  I.MkTupleExpr xs -> do
    xs' <- forM xs $ \z@(_, t', _) -> do
      b <- copyBorrowState
      isCopy <- getTypeIsCopyableFn >>= \f -> f t'
      borrowCheckExpr ctx (if isCopy then Shared else Move) z >>= accessorIntoExpr sr b
    pure (Left $ H.MkTupleExpr xs', t)
  I.AStructInitExpr x -> do
    fields <- forM x.exprs $ \z@(_, t', _) -> do
      b <- copyBorrowState
      isCopy <- getTypeIsCopyableFn >>= \f -> f t'
      borrowCheckExpr ctx (if isCopy then Shared else Move) z >>= accessorIntoExpr sr b
    pure (Left $ H.AStructInitExpr $ H.StructInitExpr fields x.fieldIndexToExprsIndex, t)
  I.ArrayInitExpr es@(List1 (_, t', _) _) -> do
    isCopy <- getTypeIsCopyableFn >>= \f -> f t'
    es' <- forM es $ \e -> do
      b <- copyBorrowState
      borrowCheckExpr ctx (if isCopy then Shared else Move) e >>= accessorIntoExpr sr b
    pure (Left $ H.ArrayInitExpr es', t)
  I.ALocalVarExpr e -> do
    b <- getBorrow e.uid

    v <- getVar e.uid
    unless (isJust v.refToMaybe) $ do
      unless v.initialised $ throw sr "Cannot access uninitialised variable"
      when v.moved $ throw sr "Cannot access moved variable"

    let accExpr = H.ALocalVarAccessorExpr $ H.LocalVarAccessorExpr {uid = e.uid, name = fst e.name}

    case mode of
      Move -> do
        isCopy <- getTypeIsCopyableFn >>= \f -> f t
        if isCopy
          then
            pure (Left $ H.DerefAccessorExpr (accExpr, sr), t)
          else do
            when (isJust v.refToMaybe) $ addError e.name "Cannot move reference"
            when (v.vTryCatchCtr /= ctx.tryCatchCtr)
              $ addError e.name "Cannot move value from outside the current try/catch block"
            case b of
              Just (_, b', SrcRange _ sr0' _) -> do
                let problemType = case b' of SharedBorrow -> "borrowed (shared)"; ExclusiveBorrow -> "borrowed (exclusive)"
                addError e.name
                  $ "Cannot move "
                  <> un (fst e.name)
                  <> " in "
                  <> T.pack fileName'
                  <> ":"
                  <> tShow sr0.line
                  <> " as it is already "
                  <> problemType
                  <> " on line "
                  <> tShow sr0'.line
              Nothing -> do
                markVarMoved e.uid
                unless (v.loop >= ctx.loopDepth) $ throw sr "Cannot move value from outside loop"
            pure (Left $ H.MoveLocalVarExpr e.uid (fst e.name), t)
      _ -> do
        let accExpr' = (Right (accExpr, fromMaybe (AccLocalVar e.uid) v.refToMaybe), t)
        case (mode, b) of
          (Shared, Just (_, ExclusiveBorrow, SrcRange _ sr0' _)) -> do
            addError e.name
              $ "Cannot borrow (shared) "
              <> un (fst e.name)
              <> " as it is already borrowed (exclusive) on line "
              <> tShow sr0'.line
            pure accExpr'
          (Shared, _) -> do
            markBorrowed (e.uid, SharedBorrow, sr)
            pure accExpr'
          (Exclusive, Nothing) -> do
            markBorrowed (e.uid, ExclusiveBorrow, sr)
            pure accExpr'
          (Exclusive, Just (_, b', SrcRange _ sr0' _)) -> do
            let borrowType = case b' of SharedBorrow -> "(shared)"; ExclusiveBorrow -> "(exclusive)"
            addError e.name
              $ "Cannot borrow (exclusive) "
              <> un (fst e.name)
              <> " as it is already borrowed "
              <> borrowType
              <> " on line "
              <> tShow sr0'.line
            markBorrowed (e.uid, ExclusiveBorrow, sr)
            pure accExpr'
  I.AFieldAccessorExpr e -> do
    fieldCopyable <- getTypeIsCopyableFn >>= \f -> f t
    (lhsExpr, lhsType) <- borrowCheckExpr ctx (if fieldCopyable && mode == Move then Shared else mode) e.expr
    lhsTypeCopyable <- getTypeIsCopyableFn >>= \f -> f lhsType
    case lhsExpr of
      Left x -> do
        -- Extract field from rvalue
        -- Other fields are discarded so type must be plain data or field must be copyable
        -- (onDrop cannot be called on a partial type)
        -- TODO Could drop the other fields individually
        unless (lhsTypeCopyable || fieldCopyable) $ addError e.expr "Cannot extract value from non-copy type"
        pure (Left $ H.AGetFieldExpr $ H.GetFieldExpr x e.index e.dropFn, t)
      Right (x, accTo) ->
        if mode == Move
          then
            if fieldCopyable
              then
                -- Make a copy of the field
                pure (Left $ H.DerefAccessorExpr (H.AFieldAccessorExpr $ H.FieldAccessorExpr x e.index, sr), t)
              else
                -- Cannot move one field as the value would be left invalid
                throw sr "Cannot extract individual fields"
          else
            -- Reference to the field
            pure (Right (H.AFieldAccessorExpr $ H.FieldAccessorExpr {expr = x, index = e.index}, accTo), t)
  I.PtrDerefExpr e -> do
    lhsExpr <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared e >>= accessorIntoExpr sr b
    pure (Right (H.PtrDerefExpr lhsExpr t, AccRawPtr), t)
  I.APtrAddExpr e -> do
    b <- copyBorrowState
    idxExpr <- borrowCheckExpr ctx Shared e.index >>= accessorIntoExpr sr b
    lhsExpr <- borrowCheckExpr ctx mode e.expr >>= accessorIntoExpr sr b
    let pointee = case t of H.PtrType (Just x) -> x; _ -> undefined
    pure (Left $ H.APtrAddExpr $ H.PtrAddExpr lhsExpr idxExpr pointee, t)
  I.APtrSubExpr e -> do
    b <- copyBorrowState
    idxExpr <- borrowCheckExpr ctx Shared e.index >>= accessorIntoExpr sr b
    lhsExpr <- borrowCheckExpr ctx mode e.expr >>= accessorIntoExpr sr b
    let pointee = case t of H.PtrType (Just x) -> x; _ -> undefined
    pure (Left $ H.APtrSubExpr $ H.PtrSubExpr lhsExpr idxExpr pointee, t)
  I.AFnCallExpr e -> do
    case e.fn of
      (_, H.AFnType _, _) -> do
        (x, retType) <- borrowCheckFnCall ctx e
        pure (Left $ H.AFnCallExpr x, must retType)
      (_, H.AnAccessorType _, _) -> do
        -- Get the function
        b <- copyBorrowState
        calleeExprOrAccExpr@(_, calleeType) <- borrowCheckExpr ctx Shared e.fn
        calleeExpr <- accessorIntoExpr sr b calleeExprOrAccExpr

        let (selfParamMode, otherParamsModes, retType) = case calleeType of
              H.AnAccessorType f ->
                let (List1 p0 ps) = f.params
                 in (fst p0, (ps <&> fst) ++ repeat Move, f.ret)
              _ -> error "Not a function type"

        assertM $ selfParamMode /= Move
        when (mode == Move) $ throw sr "Cannot move from reference"

        -- If accessor function takes its reference as exclusive then this can only be an exclusive reference
        let mode' = if selfParamMode == Exclusive then Exclusive else mode
        selfExpOrAcc <- borrowCheckExpr ctx mode' $ fst $ e.args !! 0
        (selfExpr, uid') <- case fst selfExpOrAcc of
          Left _ -> throw (fst $ e.args !! 0) "Argument is not an accessor"
          Right x -> pure x

        -- Get the list of new borrows from the first argument
        b' <- copyBorrowState
        let selfNewBorrows = take (length b' - length b) b'
        restoreBorrowState b

        -- Get the other args
        otherArgsAndNewBorrows <- getArgsExprAndBorrows ctx $ zip otherParamsModes $ tail e.args

        -- Apply borrows for the other args
        let newBorrows = concat $ selfNewBorrows : (snd <$> otherArgsAndNewBorrows)
        applyArgsBorrows newBorrows
        restoreBorrowState b'

        -- Get drop functions in case the accessor function throws
        toDrop <- if e.fnIsNoThrow then pure Nothing else getThrowDropFns ctx <&> Just

        let callEx =
              H.AccessorCallExpr
                $ H.AccessorFnCallExpr mode calleeExpr selfExpr (fst <$> otherArgsAndNewBorrows) toDrop
        pure (Right (callEx, uid'), retType)
      _ -> error "Not a fn/acc"
  I.ACondOpExpr e -> do
    -- Get the condition boolean
    b <- copyBorrowState
    condExpr <- borrowCheckExpr ctx Shared e.condExpr >>= accessorIntoExpr sr b

    -- Get the state of variables before and then get the then/else branches and resulting vars lists
    varsBefore <- copyVarsList

    thenExpr <- borrowCheckExpr ctx Shared e.thenExpr >>= accessorIntoExpr sr b
    varsAfterThen <- copyVarsList

    restoreVarsList varsBefore
    elseExpr <- borrowCheckExpr ctx Shared e.elseExpr >>= accessorIntoExpr sr b
    varsAfterElse <- copyVarsList

    restoreVarsList varsBefore

    -- New variables cannot have been added because expressions cannot define variables
    assertM $ length varsAfterThen == length varsBefore
    assertM $ length varsAfterElse == length varsBefore

    -- Check consistency, neither branch terminates because they are expressions
    (x, y) <-
      checkMovedInitedVarsAndGetDropFns sr varsBefore [Just varsAfterThen, Just varsAfterElse]
        <&> \x' -> (x' !! 0, x' !! 1)

    pure
      ( Left
          $ H.ACondOpExpr
          $ H.CondOpExpr
            { condExpr = condExpr,
              thenExpr = thenExpr,
              elseExpr = elseExpr,
              dropFnsForThen = x,
              dropFnsForElse = y
            },
        t
      )
  I.BitCast e -> do
    b <- copyBorrowState
    e' <- borrowCheckExpr ctx mode e >>= accessorIntoExpr sr b
    pure (Left $ H.BitCast e' t, t)
  I.AndExpr lhs rhs -> do
    lhs' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared lhs >>= accessorIntoExpr (thd3 lhs) b
    rhs' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared rhs >>= accessorIntoExpr (thd3 rhs) b
    pure (Left $ H.AndExpr lhs' rhs', t)
  I.OrExpr lhs rhs -> do
    lhs' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared lhs >>= accessorIntoExpr (thd3 lhs) b
    rhs' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared rhs >>= accessorIntoExpr (thd3 rhs) b
    pure (Left $ H.OrExpr lhs' rhs', t)
  I.PtrEqExpr lhs rhs -> do
    lhs' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared lhs >>= accessorIntoExpr (thd3 lhs) b
    rhs' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared rhs >>= accessorIntoExpr (thd3 rhs) b
    pure (Left $ H.PtrEqExpr lhs' rhs', t)
  I.PtrNEqExpr lhs rhs -> do
    lhs' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared lhs >>= accessorIntoExpr (thd3 lhs) b
    rhs' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared rhs >>= accessorIntoExpr (thd3 rhs) b
    pure (Left $ H.PtrNEqExpr lhs' rhs', t)
  I.AddressOfExpr e -> do
    b <- copyBorrowState
    case fst3 e of
      I.ALocalVarExpr x -> do
        -- Taking the address of a variable marks it initialised so values can be initialised by
        -- passing the address into a function. E.g. to create OpenGL IDs
        markVarInitialised x.uid
        let accExpr = H.ALocalVarAccessorExpr $ H.LocalVarAccessorExpr {uid = x.uid, name = fst x.name}
        pure (Left $ H.AddressOfExpr (accExpr, sr), t)
      _ -> do
        (e', t') <- borrowCheckExpr ctx Shared e
        case e' of
          Left _ -> throw e "Cannot take address of rvalue (expected accessor)"
          Right (accExpr, _) -> do
            restoreBorrowState b
            pure (Left $ H.AddressOfExpr accExpr, t')
  I.UninitExpr ->
    pure (Left $ H.UninitExpr t, t)
  I.DataConsExpr {} ->
    -- Functions for data constructors with values are generated in Tc.hs
    undefined
  I.ActiveDataConsExpr e -> do
    (e', t') <- borrowCheckExpr ctx Shared e
    case e' of
      Left e'' -> do
        copy <- getTypeIsCopyableFn >>= \f -> f t'
        -- TODO Could call the drop fn..
        unless copy $ throw sr "Cannot discard non-copy enum type"
        pure (Left $ H.ActiveDataConsExpr $ Left e'', t)
      Right (e'', _) ->
        pure (Left $ H.ActiveDataConsExpr $ Right e'', t)
  I.RawSliceToSliceExpr e -> do
    e' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared e >>= accessorIntoExpr (thd3 e) b
    let pointeeType = case t of H.SliceType x -> x; _ -> undefined
    pure (Right (H.RawSliceToSliceExpr e' pointeeType, AccRawPtr), t)
  I.BubbleExpr e -> do
    when ctx.inAccessorFn $ addError sr "Error bubble operator is not valid in accessors"
    e' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared e >>= accessorIntoExpr (thd3 e) b
    vs <- copyVarsList
    let toDrop = mapMaybe getDropFnForVarMaybe vs
    pure (Left $ H.BubbleExpr e' toDrop, t)

borrowCheckCodeBlockStmnt :: (MonadBrwChk m) => Ctx -> [I.Statement] -> m (H.Statement', Terminates)
borrowCheckCodeBlockStmnt ctx ss = do
  vars <- copyVarsList
  b <- copyBorrowState
  ss' <- forM ss $ borrowCheckStmnt ctx
  restoreBorrowState b -- Undo borrows from borrow statements
  vars' <- copyVarsList

  let newVars = take (length vars' - length vars) vars'
  let drops = mapMaybe getDropFnForVarMaybe newVars
  dropVars $ length newVars

  let terminates = any snd ss'
  -- TODO If last in ss' does not terminate then warn about unused code

  pure (H.CodeBlockStmnt (fst <$> ss') drops, terminates)

borrowCheckDestructure :: (MonadBrwChk m) => Ctx -> I.Destructure -> m H.DropFns
borrowCheckDestructure ctx = \case
  I.NameDes uid name dropFn -> do
    addVar uid (fst name) Nothing dropFn ctx.loopDepth ctx.tryCtr ctx.tryCatchCtr
    pure $ maybeToList $ (uid,) <$> dropFn
  I.IgnoreDes _ -> pure []
  I.TupleDes xs -> concat <$> forM xs (borrowCheckDestructure ctx)
  I.ArrayDes xs -> concat <$> forM xs (borrowCheckDestructure ctx)
  I.AStructDes ds -> concat <$> forM (fst <$> ds) (borrowCheckDestructure ctx)

borrowCheckVarStmnt :: (MonadBrwChk m) => Ctx -> I.Destructure -> I.Expr -> m (H.Destructure, H.Expr)
borrowCheckVarStmnt ctx d e = do
  isCopy <- getTypeIsCopyableFn >>= \f -> f $ snd3 e
  let mode = if isCopy then Shared else Move
  e' <- copyBorrowState >>= \b -> borrowCheckExpr ctx mode e >>= accessorIntoExpr (thd3 e) b
  _ <- borrowCheckDestructure ctx d
  pure (d, e')

borrowCheckAssignmentStmnt :: (MonadBrwChk m) => Ctx -> I.AssignmentStmnt -> m H.Statement'
borrowCheckAssignmentStmnt ctx s = do
  b <- copyBorrowState
  isCopy <- getTypeIsCopyableFn >>= \f -> f $ snd3 s.value
  let mode = if isCopy then Shared else Move
  e <- borrowCheckExpr ctx mode s.value >>= accessorIntoExpr (thd3 s.value) b

  case s.lhs of
    Nothing ->
      -- _ = ...;
      -- Value is immediately discarded
      pure $ H.ExprStmnt e s.lhsDestructor
    Just lhs' -> do
      -- If assigning to a variable then mark it initialised
      -- If it was uninitialised before then mustn't try to drop the old value
      noDrop <- case fst3 lhs' of
        I.ALocalVarExpr varExpr -> do
          v <- getVar varExpr.uid
          if isJust v.refToMaybe || v.initialised
            then pure False
            else do
              unless (v.loop == ctx.loopDepth) $ throw lhs' "Cannot initialise value outside loop"
              markVarInitialised varExpr.uid
              pure True
        _ -> pure False

      lhs <- borrowCheckExpr ctx Exclusive lhs'
      case lhs of
        (Left _, _) ->
          throw lhs' "Expected accessor expression"
        (Right (lhsAcc, to), _) -> do
          restoreBorrowState b
          -- AccRawPtr disables move semantics for the LHS
          let dropFn = if noDrop || to == AccRawPtr then Nothing else s.lhsDestructor
          pure $ H.AnAssignmentStmnt $ H.AssignmentStmnt {lhs = lhsAcc, value = e, lhsDestructor = dropFn}

type Terminates = Bool

borrowCheckStmnt :: (MonadBrwChk m) => Ctx -> I.Statement -> m (H.Statement, Terminates)
borrowCheckStmnt ctx (stmnt, sr) = borrowCheckStmnt' ctx (stmnt, sr) <&> first (,sr)

borrowCheckStmnt' :: (MonadBrwChk m) => Ctx -> I.Statement -> m (H.Statement', Terminates)
borrowCheckStmnt' ctx (stmnt, sr) = case stmnt of
  I.VarStmnt d e ->
    borrowCheckVarStmnt ctx d e <&> \(d', e') -> (H.VarStmnt d' e', False)
  I.UninitVarStmnt uid name dropFn t -> do
    addUninitVar uid name dropFn ctx.loopDepth ctx.tryCtr ctx.tryCatchCtr
    pure (H.UninitVarStmnt uid name dropFn t, False)
  I.AnAssignmentStmnt s ->
    borrowCheckAssignmentStmnt ctx s <&> (,False)
  I.FnCallStmnt e -> do
    terminates <- case fst3 e.fn of
      I.LoadConstantExpr (I.ConstFnPtr id) ->
        getVDef id <&> \d -> Attribute "NoReturn" `elem` (H.vDefCommon d).attributes
      _ -> pure False
    borrowCheckFnCall ctx e <&> \(x, _) -> (H.FnCallStmnt x, terminates)
  I.ExprStmnt e d -> do
    e' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared e >>= accessorIntoExpr (thd3 e) b
    pure (H.ExprStmnt e' d, False)

  -- Same as CondOpExpr but the branches can declare variables, terminate, etc.
  I.AnIfElseStmnt s -> do
    b <- copyBorrowState
    condExpr <- borrowCheckExpr ctx Shared s.cond >>= accessorIntoExpr (thd3 s.cond) b

    varsBefore <- copyVarsList

    (thenStmnt, thenTerminates) <- borrowCheckStmnt ctx s.thenStmnt
    restoreBorrowState b
    varsAfterThen <- copyVarsList

    restoreVarsList varsBefore
    elseStmntMaybe <- forM s.elseStmntMaybe $ borrowCheckStmnt ctx
    let elseTerminates = maybe False snd elseStmntMaybe
    restoreBorrowState b
    varsAfterElse <- copyVarsList

    restoreVarsList varsBefore

    assertM $ length varsAfterThen == length varsBefore
    assertM $ length varsAfterElse == length varsBefore

    (x, y) <-
      -- If a branch terminates then pass Nothing instead of the vars list
      let varsAfter = [toMaybe (not thenTerminates) varsAfterThen, toMaybe (not elseTerminates) varsAfterElse]
       in checkMovedInitedVarsAndGetDropFns sr varsBefore varsAfter
            <&> \x' -> (x' !! 0, x' !! 1)

    pure
      ( H.AnIfElseStmnt
          $ H.IfElseStmnt
            { cond = condExpr,
              thenStmnt = thenStmnt,
              elseStmntMaybe = fst <$> elseStmntMaybe,
              dropFnsForThen = x,
              dropFnsForElse = y
            },
        thenTerminates && elseTerminates
      )
  I.LoopStmnt s -> do
    b <- copyBorrowState
    s' <- borrowCheckStmnt ctx {loopDepth = ctx.loopDepth + 1} s
    restoreBorrowState b
    pure (H.LoopStmnt $ fst s', False)
  I.BreakStmnt -> do
    vs <- copyVarsList
    let toDrop = mapMaybe getDropFnForVarMaybe $ filter (\v -> v.loop == ctx.loopDepth) vs
    pure (H.BreakStmnt toDrop, True)
  I.ContinueStmnt -> do
    vs <- copyVarsList
    let toDrop = mapMaybe getDropFnForVarMaybe $ filter (\v -> v.loop == ctx.loopDepth) vs
    pure (H.ContinueStmnt toDrop, True)
  I.CodeBlockStmnt ss ->
    borrowCheckCodeBlockStmnt ctx ss
  -- isAccRawRet is True if this is an accessor function and a raw pointer is being
  -- returned that will be implicitly casted to a reference
  I.ReturnStmnt e -> do
    b <- copyBorrowState
    case e of
      Just e'@(_, _, sr') -> do
        let mode = if ctx.inAccessorFn then Shared else Move
        -- Set loopDepth to -1 to allow moving and returning any local variable, regardless of whether the
        -- variable or return statement are in the same loop or not
        expOrAcc <- borrowCheckExpr ctx {loopDepth = -1} mode e'
        toDrop <- copyVarsList <&> mapMaybe getDropFnForVarMaybe
        if ctx.inAccessorFn
          then case fst expOrAcc of
            Left _ ->
              throw sr' "Expected reference"
            Right (a, accTo) -> do
              unless (accTo == AccRawPtr || accTo == AccLocalVar (H.LocalVarUid 0))
                $ addError sr' "Accessor functions must return a reference to the first parameter"
              restoreBorrowState b
              pure (H.AccessorReturnStmnt a toDrop, True)
          else do
            e'' <- accessorIntoExpr sr' b expOrAcc
            pure (H.ReturnStmnt (Just e'') toDrop, True)
      _ -> do
        toDrop <- copyVarsList <&> mapMaybe getDropFnForVarMaybe
        pure (H.ReturnStmnt Nothing toDrop, True)
  I.YieldStmnt e'@(_, t, sr') -> do
    b <- copyBorrowState
    isCopy <- getTypeIsCopyableFn >>= \f -> f t
    let mode = if isCopy || ctx.inAccessorFn then Shared else Move
    expOrAcc <- borrowCheckExpr ctx mode e'
    toDrop <- copyVarsList <&> mapMaybe getDropFnForVarMaybe
    if ctx.inAccessorFn
      then case fst expOrAcc of
        Left _ -> throw sr' "Expected accessor"
        Right (a, accTo) -> do
          unless (accTo == AccRawPtr || accTo == AccLocalVar (H.LocalVarUid 0))
            $ addError sr' "Accessor iterator must yield references to the first parameter"
          restoreBorrowState b
          pure (H.AccessorYieldStmnt a toDrop, False)
      else do
        e'' <- accessorIntoExpr sr' b expOrAcc
        pure (H.YieldStmnt e'' toDrop, False)
  I.AForEachLoopStmnt s -> do
    b <- copyBorrowState
    prevVarsList <- copyVarsList

    -- Get fn expr and drop functions for the yielded value
    (args, mode, dropFns') <- case snd s.fn of
      H.AnIteratorType f -> do
        let paramsModes = f.params <&> fst
        argsAndNewBorrows <- getArgsExprAndBorrows ctx $ zip paramsModes s.args
        applyArgsBorrows $ concatMap snd argsAndNewBorrows

        dropFns' <- borrowCheckDestructure ctx s.var
        pure (Left $ fst <$> argsAndNewBorrows, Move, dropFns')
      H.AnAccessorIteratorType f -> do
        when (s.varMode == Move) $ throw sr "Cannot move from accessor"

        let (selfParamMode, otherParamsModes) =
              let (List1 p0 ps) = f.params in (fst p0, ps <&> fst)
        let mode' = if selfParamMode == Exclusive then Exclusive else s.varMode

        selfExpOrAcc <- borrowCheckExpr ctx mode' $ fst $ s.args !! 0
        let (selfExpr, to) = case fst selfExpOrAcc of
              Left _ -> error "First argument to iterator function is not a reference"
              Right x -> x

        b' <- copyBorrowState
        let selfNewBorrows = take (length b' - length b) b'
        restoreBorrowState b

        otherArgsAndNewBorrows <- getArgsExprAndBorrows ctx $ zip otherParamsModes $ tail s.args

        let newBorrows = concat $ selfNewBorrows : (snd <$> otherArgsAndNewBorrows)
        applyArgsBorrows newBorrows

        addDestructureRefs ctx to (s.varMode == Shared) s.var

        pure (Right (selfParamMode, selfExpr, fst <$> otherArgsAndNewBorrows), s.varMode, [])
      _ -> error "Not an iterator function type"

    -- Get body
    body <- fst <$> borrowCheckStmnt ctx {loopDepth = ctx.loopDepth + 1} s.body

    varsAfter <- copyVarsList
    let dropFns = flip filter dropFns' $ \(uid, _) ->
          -- The yielded values may be moved within the loop body
          let v = must $ find (\v' -> v'.uid == uid) varsAfter in not v.moved
    restoreVarsList prevVarsList

    restoreBorrowState b

    onThrowDropFns <- if s.iterFnIsNoThrow then pure Nothing else getThrowDropFns ctx <&> Just

    pure
      ( H.AForEachLoopStmnt
          $ H.ForEachLoopStmnt s.var mode s.yieldType (fst s.fn) args body dropFns onThrowDropFns,
        False
      )
  I.ForLoopStmnt vars cond as innerStmnt -> do
    varsListBefore <- copyVarsList
    vars' <- forM vars $ uncurry (borrowCheckVarStmnt ctx)
    varsListAfter <- copyVarsList
    let newVars = take (length varsListAfter - length varsListBefore) varsListAfter
    let drops = mapMaybe getDropFnForVarMaybe newVars

    let ctx' = ctx {loopDepth = ctx.loopDepth + 1}

    cond' <- copyBorrowState >>= \b -> borrowCheckExpr ctx' Shared cond >>= accessorIntoExpr (thd3 cond) b

    b <- copyBorrowState
    innerStmnt' <- fst <$> borrowCheckStmnt ctx' innerStmnt
    restoreBorrowState b
    as' <- forM as $ \a -> borrowCheckStmnt ctx' a <&> fst
    restoreBorrowState b

    dropVars $ length newVars
    copyVarsList >>= \v -> assertM $ v == varsListBefore

    pure (H.AForLoopStmnt $ H.ForLoopStmnt vars' cond' as' innerStmnt' drops, False)
  I.MatchStmnt mode e branches -> do
    b <- copyBorrowState
    (e', _) <- borrowCheckExpr ctx mode e
    b' <- copyBorrowState
    varsBefore <- copyVarsList

    codeAndVarsAndDropFns <- forM (toList branches) $ \br -> do
      dropFns' <- case e' of
        Left _ -> addMatchPatternVars ctx br.pattern
        Right (_, to) -> addMatchPatternRefs ctx to (mode == Shared) br.pattern $> []
      s <- borrowCheckStmnt ctx br.code
      varsAfter <- copyVarsList
      let dropFns = flip filter dropFns' $ \(uid, _) ->
            -- The matched values may be moved within the branch body
            let v = must $ find (\v' -> v'.uid == uid) varsAfter in not v.moved
      restoreBorrowState b'
      restoreVarsList varsBefore
      pure (s, drop (length varsAfter - length varsBefore) varsAfter, dropFns)

    restoreBorrowState b

    let statements = codeAndVarsAndDropFns <&> (fst . fst3)
    let branchesTerminate = codeAndVarsAndDropFns <&> (snd . fst3)
    let updatedVarsLists = codeAndVarsAndDropFns <&> \((_, terminates), x, _) -> toMaybe (not terminates) x
    -- Drop functions for the (destructured) matched value minus any parts that were moved in each branch
    let dropFnsLists1 = codeAndVarsAndDropFns <&> \((_, terminates), _, x) -> if terminates then [] else x

    -- Drop functions for values dropped in some branches but not others
    dropFnsLists2 <- checkMovedInitedVarsAndGetDropFns sr varsBefore updatedVarsLists

    let branches' =
          zip3 (toList branches) statements (zip dropFnsLists1 dropFnsLists2)
            <&> \(br, s, (d1, d2)) -> H.MatchBranch br.pattern br.patternSr s (d1 ++ d2)

    pure (H.MatchStmnt mode (e' <&> fst) (List1 (must $ head branches') (tail branches')), and branchesTerminate)
  I.ThrowStmnt e -> do
    toDrop <- getThrowDropFns ctx
    e' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared e >>= accessorIntoExpr sr b
    pure (H.ThrowStmnt e' toDrop, True)
  I.TryCatchStmnt tryStmnt varMaybe catchStmnt -> do
    b <- copyBorrowState
    varsBefore <- copyVarsList

    (tryStmnt', _) <- borrowCheckStmnt ctx {tryCtr = ctx.tryCtr + 1, tryCatchCtr = ctx.tryCatchCtr + 1} tryStmnt
    restoreVarsList varsBefore
    restoreBorrowState b

    forM_ varMaybe $ \(uid, name, _) ->
      addVar uid name Nothing Nothing ctx.loopDepth ctx.tryCtr (ctx.tryCatchCtr + 1)

    (catchStmnt', _) <- borrowCheckStmnt ctx {tryCatchCtr = ctx.tryCatchCtr + 1} catchStmnt
    restoreVarsList varsBefore
    restoreBorrowState b

    pure (H.TryCatchStmnt tryStmnt' varMaybe catchStmnt', False)
  I.BubbleStmnt e -> do
    when ctx.inAccessorFn $ addError sr "Error bubble operator is not valid in accessors"
    e' <- copyBorrowState >>= \b -> borrowCheckExpr ctx Shared e >>= accessorIntoExpr (thd3 e) b
    vs <- copyVarsList
    let toDrop = mapMaybe getDropFnForVarMaybe vs
    pure (H.BubbleStmnt e' toDrop, False)
  I.BorrowStatement mode uid name e -> do
    (e', _) <- borrowCheckExpr ctx mode e
    (e'', to) <- case e' of
      Right x -> pure x
      Left _ -> throw sr "Expected reference"
    addVar uid name (Just to) Nothing ctx.loopDepth ctx.tryCtr ctx.tryCatchCtr
    when (mode == Shared)
      $ markBorrowed (uid, SharedBorrow, sr)
    pure (H.BorrowStatement mode uid name e'', False)

getThrowDropFns :: (MonadBrwChk m) => Ctx -> m H.DropFns
getThrowDropFns ctx =
  copyVarsList <&> (filter (\v -> v.vTryCtr == ctx.tryCtr) >>> mapMaybe getDropFnForVarMaybe)

addMatchPatternVars :: (MonadBrwChk m) => Ctx -> I.Pattern -> m H.DropFns
addMatchPatternVars ctx = \case
  I.PatternAny _ -> pure []
  I.PatternName uid name dropFn -> do
    addVar uid (fst name) Nothing dropFn ctx.loopDepth ctx.tryCtr ctx.tryCatchCtr
    pure $ maybeToList $ (uid,) <$> dropFn
  I.PatternDataCons0 _ -> pure []
  I.PatternDataCons1 _ p -> addMatchPatternVars ctx p

addMatchPatternRefs :: (MonadBrwChk m) => Ctx -> AccessorTo -> Bool -> I.Pattern -> m ()
addMatchPatternRefs ctx to markShared = \case
  I.PatternAny _ -> pure ()
  I.PatternName uid name _ -> do
    addVar uid (fst name) (Just to) Nothing ctx.loopDepth ctx.tryCtr ctx.tryCatchCtr
    when markShared $ markBorrowed (uid, SharedBorrow, snd name)
  I.PatternDataCons0 _ -> pure ()
  I.PatternDataCons1 _ p -> addMatchPatternRefs ctx to markShared p

addDestructureRefs :: (MonadBrwChk m) => Ctx -> AccessorTo -> Bool -> I.Destructure -> m ()
addDestructureRefs ctx to markShared = \case
  I.NameDes uid name _ -> do
    addVar uid (fst name) (Just to) Nothing ctx.loopDepth ctx.tryCtr ctx.tryCatchCtr
    when markShared $ markBorrowed (uid, SharedBorrow, snd name)
  I.IgnoreDes _ -> pure ()
  I.TupleDes xs -> forM_ xs $ addDestructureRefs ctx to markShared
  I.ArrayDes xs -> forM_ xs $ addDestructureRefs ctx to markShared
  I.AStructDes ds -> forM_ (fst <$> ds) $ addDestructureRefs ctx to markShared
