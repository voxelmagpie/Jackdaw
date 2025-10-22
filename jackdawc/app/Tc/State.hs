-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.State where

import AccessMode
import Ast qualified as A
import Control.Exception (throwIO)
import Control.Monad (unless)
import Control.Monad.Reader (MonadIO (liftIO), MonadReader (ask), ReaderT (runReaderT), asks)
import Data.Foldable (find)
import Data.HashTable.IO qualified as HT
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (findIndex)
import Data.Maybe (fromMaybe, isJust)
import GHC.Stack (HasCallStack)
import Hir qualified as H
import Names
import Prelude2
import SrcLoc (SrcRange)
import Tables
import Tc.Ctx (Ctx, ErrorTrace, TypeHint)
import Tc.Error (Error, MonadTcError (..))
import Tc.TcIr qualified as I

-- 0 = Not in loop
type LoopCounter = Int

-- 0 = Not in try
type TryCounter = Int

-- 0 = Not in try/catch
type TryCatchCounter = Int

type TDef2Data = (Ctx, Ctx, SrcRange, A.AnyTSDef)

data TDef2State
  = Td2Queued TDef2Data
  | Td2Visiting (Ctx, SrcRange)
  | Td2Visited I.AnyTDef2

data CachedTSDef = TsDefVisiting | TsDefVisited H.Type

-- This is for breaking the cyclic module dependency between the type checker and borrow checker
type BwCheckFnType m =
  I.Statement ->
  [((AccessMode, I.Type), (Maybe VName', I.LocalVarUid), Maybe I.DropFn)] ->
  SrcRange ->
  Bool ->
  m (H.Statement, Bool)

type BwCheckFnType' m = ErrorTrace -> BwCheckFnType m

convertBwCheckFnTypeIO :: BwCheckFnType BcM -> BwCheckFnType' TcM
convertBwCheckFnTypeIO f et a0 a1 a2 a3 = do
  s <- ask
  s' <- liftIO $ newBcState s et
  liftIO $ runReaderT (f a0 a1 a2 a3) s'

data TcState = TcState
  { fns :: TcFns TcM,
    isCopyFn :: I.Type -> TcM Bool,
    hir :: H.Ir,
    hirVDefCache :: HashTable (VFqn, [H.GenericArg]) (H.VDefId, H.AnyVDef),
    hirTSDefCache :: HashTable (TFqn, [H.GenericArg]) CachedTSDef,
    hirTDef2Queue :: HashTable H.TDefId TDef2State,
    hirTypeDefsVisited :: HashTable (TFqn, [I.GenericArg]) (),
    hirValueDefsVisited :: HashTable (VFqn, [I.GenericArg]) (),
    hirFnBodiesVisited :: HashTable H.VDefId (),
    typeContexts :: HashTable H.Type Ctx,
    startedFromStart :: IORef Bool,
    -- Per-function state
    usesIterators :: IORef [H.VDefId],
    nextLocalVarUid :: IORef Int,
    usesThrowingFns :: IORef Bool,
    -- Errors
    errorsRev :: IORef [Error]
  }
  deriving (Generic)

type GetConstLitExprType m = Ctx -> TypeHint -> A.Expr -> m I.Constant

type GetExprType m = Ctx -> TypeHint -> A.Expr -> m I.Expr

type GetCodeBlockStmntType m = Ctx -> [A.Statement] -> [I.Statement] -> m I.Statement

data TcFns m = TcFns
  { bwCheckFn :: BwCheckFnType' TcM,
    getConstLitExprFn :: GetConstLitExprType TcM,
    getExprFn :: GetExprType TcM,
    getCodeBlockStmntFn :: GetCodeBlockStmntType TcM
  }

newTcState :: TcFns TcM -> (I.Type -> TcM Bool) -> IO TcState
newTcState f cf =
  TcState f cf
    <$> H.emptyHir
    <*> HT.new
    <*> HT.new
    <*> HT.new
    <*> HT.new
    <*> HT.new
    <*> HT.new
    <*> HT.new
    <*> newIORef def
    <*> newIORef def
    <*> newIORef def
    <*> newIORef def
    <*> newIORef def

type TcM = ReaderT TcState IO

data BcState = BcState
  { tcState :: TcState,
    et :: ErrorTrace,
    borrows :: IORef Borrows,
    vars :: IORef [Var],
    refVarsList :: IORef [H.LocalVarUid]
  }
  deriving (Generic)

newBcState :: TcState -> ErrorTrace -> IO BcState
newBcState s et =
  BcState s et
    <$> newIORef def
    <*> newIORef def
    <*> newIORef def

type BcM = ReaderT BcState IO

class (Monad m) => MonadHirRead' m where
  getVDef :: H.VDefId -> m H.AnyVDef
  getFnDefBodyMaybe :: H.VDefId -> m (Maybe (H.Statement, H.IsNoThrow))
  getFnDeps :: H.VDefId -> m [H.VDefId]
  getTDef :: H.TDefId -> m H.AnyTDef
  getTDef2 :: H.TDefId -> m (Maybe H.AnyTDef2)
  loopOverVDefs :: (H.VDefId -> m ()) -> m ()
  loopOverTSDefs :: (H.TDefId -> m ()) -> m ()

class (MonadHirRead' m, MonadTcError m) => MonadTc m where
  getBwCheckFn :: m (BwCheckFnType' m)
  getConstLitExprFn :: m (GetConstLitExprType m)
  getExprFn :: m (GetExprType m)
  getCodeBlockStmntFn :: m (GetCodeBlockStmntType m)

  addVDef :: H.AnyVDef -> m H.VDefId
  getCachedVDef :: VFqn -> [I.GenericArg] -> m (Maybe (H.VDefId, H.AnyVDef))

  addFnDefBody :: H.VDefId -> H.Statement -> H.IsNoThrow -> m ()

  markFnDefBodyVisited :: H.VDefId -> m ()
  fnDefBodyVisited :: H.VDefId -> m Bool

  queueTDefVisit :: H.TDefId -> TDef2Data -> m ()
  markTypeDefVisiting :: H.TDefId -> m ()
  markTypeDefVisited :: H.TDefId -> I.AnyTDef2 -> m I.AnyTDef2
  typeDefVisited :: H.TDefId -> m TDef2State
  getQueuedTsDef2s :: m [H.TDefId]

  markVDefVisited :: VFqn -> [I.GenericArg] -> m ()
  vDefVisited :: VFqn -> [I.GenericArg] -> m Bool

  addTSDef :: TFqn -> [I.GenericArg] -> H.AnyTDef -> m (H.Type, H.TDefId)
  addTSDef' :: TFqn -> [I.GenericArg] -> H.Type -> m H.Type
  markTsDefVisiting :: TFqn -> [I.GenericArg] -> m ()
  getCachedTSDef :: TFqn -> [I.GenericArg] -> m (Maybe CachedTSDef)

  -- Contexts only exist for H.ANamedType
  addTypeCtx :: H.Type -> Ctx -> m ()
  getCachedTypeCtx :: H.Type -> m (Maybe Ctx)

  newLocalVarUid :: m H.LocalVarUid
  peekNextLocalVarUid :: m Int
  resetLocalVarUid :: Int -> m ()

  setStartedFromStart :: Bool -> m ()
  getStartedFromStart :: m Bool

  addUsedIter :: H.VDefId -> m ()
  getUsedIters :: m [H.VDefId]
  resetUsedItersList :: [H.VDefId] -> m ()
  setFnDeps :: H.VDefId -> [H.VDefId] -> m ()

  getUsesThrowingFns :: m Bool
  setUsesThrowingFns :: Bool -> m ()

type Borrow = (H.LocalVarUid, BorrowType, SrcRange)

type Borrows = [Borrow]

data BorrowType = SharedBorrow | ExclusiveBorrow
  deriving (Show, Eq)

data Var = Var
  { uid :: H.LocalVarUid,
    name :: VName,
    refToMaybe :: Maybe AccessorTo,
    dropFn :: Maybe H.DropFn,
    moved :: Bool,
    loop :: LoopCounter,
    vTryCtr :: TryCounter,
    vTryCatchCtr :: TryCatchCounter,
    initialised :: Bool
  }
  deriving (Show, Eq)

-- Tracks what a reference is pointing to
data AccessorTo = AccRawPtr | AccStatic | AccLocalVar H.LocalVarUid
  deriving (Show, Eq)

class (MonadTcError m, MonadHirRead' m) => MonadBrwChk m where
  markBorrowed :: Borrow -> m ()
  getBorrow :: H.LocalVarUid -> m (Maybe Borrow)
  resetBorrowList :: m ()
  copyBorrowState :: m Borrows
  restoreBorrowState :: Borrows -> m ()

  -- Does not do checks, only updates state
  addVar :: H.LocalVarUid -> VName -> Maybe AccessorTo -> Maybe H.VDefId -> LoopCounter -> TryCounter -> TryCatchCounter -> m ()
  addUninitVar :: H.LocalVarUid -> VName -> Maybe H.VDefId -> LoopCounter -> TryCounter -> TryCatchCounter -> m ()
  getVar :: (HasCallStack) => H.LocalVarUid -> m Var
  markVarMoved :: (HasCallStack) => H.LocalVarUid -> m ()
  markVarInitialised :: H.LocalVarUid -> m ()
  copyVarsList :: m [Var]
  restoreVarsList :: [Var] -> m ()
  dropVars :: Int -> m ()
  resetVarsList :: m ()

  -- This is needed to break the module dependency cycle between the type checker and borrow checker
  getTypeIsCopyableFn :: m (I.Type -> m Bool)

  getEt :: m ErrorTrace

instance MonadHirRead' TcM where
  getVDef id = ask >>= \s -> liftIO $ tblGet id s.hir.vDefs
  getFnDefBodyMaybe id = ask >>= \s -> liftIO $ HT.lookup s.hir.fnBodies id
  getFnDeps id = ask >>= \s -> liftIO $ HT.lookup s.hir.fnDeps id <&> fromMaybe []
  getTDef id = ask >>= \s -> liftIO $ tblGet id s.hir.tDefs
  getTDef2 id = ask >>= \s -> liftIO $ HT.lookup s.hir.tDefs2 id
  loopOverVDefs f = ask >>= \a -> liftIO $ tblForEach (\(k, _) -> runReaderT (f k) a) a.hir.vDefs
  loopOverTSDefs f = ask >>= \a -> liftIO $ tblForEach (\(k, _) -> runReaderT (f k) a) a.hir.tDefs

instance MonadHirRead' BcM where
  getVDef id = ask >>= \s -> liftIO $ tblGet id s.tcState.hir.vDefs
  getFnDefBodyMaybe id = ask >>= \s -> liftIO $ HT.lookup s.tcState.hir.fnBodies id
  getFnDeps id = ask >>= \s -> liftIO $ HT.lookup s.tcState.hir.fnDeps id <&> fromMaybe []
  getTDef id = ask >>= \s -> liftIO $ tblGet id s.tcState.hir.tDefs
  getTDef2 id = ask >>= \s -> liftIO $ HT.lookup s.tcState.hir.tDefs2 id
  loopOverVDefs f = ask >>= \a -> liftIO $ tblForEach (\(k, _) -> runReaderT (f k) a) a.tcState.hir.vDefs
  loopOverTSDefs f = ask >>= \a -> liftIO $ tblForEach (\(k, _) -> runReaderT (f k) a) a.tcState.hir.tDefs

instance MonadTcError TcM where
  getErrsListRev = do
    x <- asks (.errorsRev)
    liftIO $ readIORef x

  consErr e = do
    x <- asks (.errorsRev)
    liftIO $ modifyIORef' x (e :)

  throwTcException x = liftIO $ throwIO x

instance MonadTc TcM where
  getBwCheckFn = asks (.fns.bwCheckFn)

  getConstLitExprFn = asks (.fns.getConstLitExprFn)
  getExprFn = asks (.fns.getExprFn)
  getCodeBlockStmntFn = asks (.fns.getCodeBlockStmntFn)

  addVDef vDef = do
    let c = H.vDefCommon vDef
    s <- ask
    id <- liftIO $ tblInsert vDef s.hir.vDefs
    liftIO $ HT.insert s.hirVDefCache (c.fqn, c.genericArgs) (id, vDef)
    pure id

  getCachedVDef fqn gArgs = ask >>= \s -> liftIO $ HT.lookup s.hirVDefCache (fqn, gArgs)
  addFnDefBody id st n = ask >>= \s -> liftIO $ HT.insert s.hir.fnBodies id (st, n)

  queueTDefVisit id x = do
    ask >>= \s -> liftIO $ HT.insert s.hirTDef2Queue id (Td2Queued x)
    pure ()

  markTypeDefVisiting id = do
    s <- ask
    x <- liftIO $ HT.lookup s.hirTDef2Queue id <&> must
    case x of
      Td2Queued (_, ctx, sr, _) -> liftIO $ HT.insert s.hirTDef2Queue id (Td2Visiting (ctx, sr))
      Td2Visiting _ -> pure ()
      _ -> undefined

  markTypeDefVisited id x = do
    ask >>= \s -> liftIO $ HT.insert s.hirTDef2Queue id (Td2Visited x)
    ask >>= \s -> liftIO $ HT.insert s.hir.tDefs2 id x
    pure x

  typeDefVisited id =
    ask >>= \s -> liftIO $ HT.lookup s.hirTDef2Queue id <&> must

  getQueuedTsDef2s = do
    xs <- ask >>= \s -> liftIO $ HT.toList s.hirTDef2Queue
    pure $ filter (snd >>> \case Td2Queued _ -> True; _ -> False) xs <&> fst

  addTSDef' fqn gArgs typ = do
    ask >>= \s -> liftIO $ HT.insert s.hirTSDefCache (fqn, gArgs) (TsDefVisited typ)
    pure typ

  addTSDef fqn gArgs tDef = do
    s <- ask
    id <- liftIO $ tblInsert tDef s.hir.tDefs
    let t = I.ANamedType id
    liftIO $ HT.insert s.hirTSDefCache (fqn, gArgs) (TsDefVisited t)
    pure (t, id)

  markTsDefVisiting fqn gArgs = ask >>= \s -> liftIO $ HT.insert s.hirTSDefCache (fqn, gArgs) TsDefVisiting

  getCachedTSDef fqn gArgs = ask >>= \s -> liftIO $ HT.lookup s.hirTSDefCache (fqn, gArgs)

  addTypeCtx t c = ask >>= \s -> liftIO $ HT.insert s.typeContexts t c
  getCachedTypeCtx t = ask >>= \s -> liftIO $ HT.lookup s.typeContexts t

  newLocalVarUid = do
    s <- ask
    id <- liftIO $ readIORef s.nextLocalVarUid <&> H.LocalVarUid
    liftIO $ modifyIORef' s.nextLocalVarUid (+ 1)
    pure id

  resetLocalVarUid parametersCount = ask >>= \s -> liftIO $ writeIORef s.nextLocalVarUid parametersCount
  peekNextLocalVarUid = ask >>= \s -> liftIO $ readIORef s.nextLocalVarUid

  markVDefVisited n args = ask >>= \s -> liftIO $ HT.insert s.hirValueDefsVisited (n, args) ()
  vDefVisited n args = ask >>= \s -> liftIO $ HT.lookup s.hirValueDefsVisited (n, args) <&> isJust
  markFnDefBodyVisited id = ask >>= \s -> liftIO $ HT.insert s.hirFnBodiesVisited id ()
  fnDefBodyVisited id = ask >>= \s -> liftIO $ HT.lookup s.hirFnBodiesVisited id <&> isJust
  setStartedFromStart x = ask >>= \s -> liftIO $ writeIORef s.startedFromStart x
  getStartedFromStart = ask >>= \s -> liftIO $ readIORef s.startedFromStart

  addUsedIter id = ask >>= \s -> liftIO $ modifyIORef' s.usesIterators (id :)
  getUsedIters = ask >>= \s -> liftIO $ readIORef s.usesIterators
  resetUsedItersList xs = ask >>= \s -> liftIO $ writeIORef s.usesIterators xs
  setFnDeps dependant dependsOn =
    ask >>= \s -> liftIO $ unless (null dependsOn) $ HT.insert s.hir.fnDeps dependant dependsOn

  getUsesThrowingFns = ask >>= \s -> liftIO $ readIORef s.usesThrowingFns
  setUsesThrowingFns x = ask >>= \s -> liftIO $ writeIORef s.usesThrowingFns x

instance MonadTcError BcM where
  getErrsListRev = do
    x <- asks (.tcState.errorsRev)
    liftIO $ readIORef x

  consErr e = do
    x <- asks (.tcState.errorsRev)
    liftIO $ modifyIORef' x (e :)

  throwTcException x = liftIO $ throwIO x

instance MonadBrwChk BcM where
  markBorrowed x = ask >>= \s -> liftIO $ modifyIORef' s.borrows (x :)
  getBorrow uid = ask >>= \s -> liftIO $ readIORef s.borrows <&> find ((== uid) . fst3)
  resetBorrowList = ask >>= \s -> liftIO $ writeIORef s.borrows []
  copyBorrowState = ask >>= \s -> liftIO $ readIORef s.borrows
  restoreBorrowState b = ask >>= \s -> liftIO $ writeIORef s.borrows b

  addVar uid name refToMaybe d l tc tc' = ask >>= \s -> liftIO $ modifyIORef' s.vars (Var uid name refToMaybe d False l tc tc' True :)
  addUninitVar uid name d l tc tc' = ask >>= \s -> liftIO $ modifyIORef' s.vars (Var uid name Nothing d False l tc tc' False :)
  getVar uid = ask >>= \s -> liftIO $ readIORef s.vars <&> \x -> x & must' (show uid <> "\n" <> show x) . find (\v -> v.uid == uid)
  markVarMoved uid = do
    s <- ask
    i <- liftIO $ readIORef s.vars <&> (must' (show uid) . findIndex (\x -> x.uid == uid))
    liftIO
      $ modifyIORef' s.vars
      $ updateAt i (\x -> x {moved = True})
  markVarInitialised uid = do
    s <- ask
    i <- liftIO $ readIORef s.vars <&> (must' (show uid) . findIndex (\x -> x.uid == uid))
    liftIO
      $ modifyIORef' s.vars
      $ updateAt i (\x -> x {initialised = True})
  copyVarsList = ask >>= \s -> liftIO $ readIORef s.vars
  restoreVarsList v = ask >>= \s -> liftIO $ writeIORef s.vars v
  dropVars i = ask >>= \s -> liftIO $ modifyIORef' s.vars $ drop i
  resetVarsList = ask >>= \s -> liftIO $ writeIORef s.vars []
  getTypeIsCopyableFn = do
    s <- ask
    pure $ \t -> liftIO $ runReaderT (s.tcState.isCopyFn t) s.tcState
  getEt = asks (.et)
