
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.Demutation.Definitions where

import DiffMu.Prelude -- hiding (TeVar)
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Logging
import DiffMu.Abstract.Data.Permutation
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.TopLevel

import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as HS

import qualified Data.Text as T
import Data.Foldable

import Debug.Trace

import qualified Prelude as P
default (Text,Int)



--------------------------------------------------------------------------------------
-- Demutation Type
--------------------------------------------------------------------------------------


data IsMutated = Mutated | NotMutated
  deriving (Generic, Show, Eq)

data IsLocalMutation = LocalMutation | NotLocalMutation
  deriving (Show, Eq)

data MutationArgumentType = MutatedArg | NotMutatedArg ImmutType

--
-- NOTE: We later sort `VarAccessType`s,
-- and we do not want that the `IsLocalMutation`
-- content influences this sort --- we need to know
-- which comes first.
--
-- Hence this type is "contractible".
--
instance Ord IsLocalMutation where
  a <= b = True

-- But we need a comparison anyways:
le_ilm :: IsLocalMutation -> IsLocalMutation -> Bool
le_ilm LocalMutation _ = True
le_ilm NotLocalMutation LocalMutation = False
le_ilm NotLocalMutation NotLocalMutation = True

onlyLocallyMutatedVariables :: [(ProcVar,IsLocalMutation)] -> Bool
onlyLocallyMutatedVariables xs = [v | (v, NotLocalMutation) <- xs] == []


{-
data PureType =
  UserValue
  -- | DefaultValue
  | SingleArg ProcVar 
  | SingleArgPart ProcVar 
  -- | SingleRef
  | PureTuple [PureType] 
  deriving (Show)

data ImmutType = Pure PureType | Mutating [IsMutated] | VirtualMutated [ProcVar] | PureBlackBox
  deriving (Show)

-}

data ImmutType = Pure | Mutating [IsMutated] | PureBlackBox
  deriving (Show,Eq)

instance ShowPretty ImmutType where
  showPretty = showT

-- consumeDefaultValue :: ImmutType -> ImmutType
-- consumeDefaultValue (Pure DefaultValue) = Pure UserValue
-- consumeDefaultValue a = a

-- the scope
-- type Scope = Ctx ProcVar ImmutType


---------------------------------------------------
-- These types describe which variable names
-- are in the RHS and must be moved on tlet/slet assignment
-- See #171 #172
data MoveType =
  TupleMove [LocMoveType]
  | SingleMove ProcVar
  | RefMove DemutDMTerm
  | NoMove DemutDMTerm
  | PhiMove LocDemutDMTerm (LocMoveType,LocDemutDMTerm) (LocMoveType,LocDemutDMTerm)
  deriving (Eq, Show)

instance ShowPretty MoveType where
  showPretty = showT

type LocMoveType = Located MoveType

-- singleMoveMaybe :: Maybe ProcVar -> MoveType
-- singleMoveMaybe (Just a) = SingleMove a
-- singleMoveMaybe Nothing  = NoMove

data TermType =
  Value ImmutType LocMoveType
  | Statement SourceLocExt DemutDMTerm MoveType
  | StatementWithoutDefault SourceLocExt DemutDMTerm
  -- | PurePhiTermType LocDemutDMTerm ([MoveType],LocDemutDMTerm) (TermType,LocDemutDMTerm)
  | MutatingFunctionEnd SourceLocExt

data LastValue =
   PureValue LocMoveType
   | MutatingFunctionEndValue SourceLocExt
   | NoLastValue

data PhiBranchType =
  ValueBranch SourceLocExt [LocDemutDMTerm] LocMoveType
  | StatementBranch SourceLocExt [LocDemutDMTerm]
  deriving (Show)

--------------------------------------------------
-- memory state
--
-- Tracking memory locations for demutation.
-- This mirrors the `MoveType` above, but with `MemVar`
-- instead of `ProcVar`.
--
-- See #185.
--

data MemType = TupleMem [MemType] | SingleMem MemVar | RefMem MemVar
  deriving (Eq, Show, Ord)

data MemState = MemExists [MemType] | MemMoved [SourceLocExt]
  deriving (Show)

data MemAssignmentType = AllocNecessary | PreexistingMem

type MemCtx = Ctx ProcVar MemState


data IsSplit = Split [MemVar] | NotSplit
  deriving (Show,Eq)

-- instance Semigroup IsSplit where
--   (<>) Split a = Split
--   (<>) NotSplit b = b

data TeVarMutTrace = TeVarMutTrace (Maybe ProcVar) IsSplit [(TeVar,[SourceLocExt])] -- (every tevar also carries the locations where it was created as result of a mutation)
  deriving (Show,Eq)

newtype Scope = Scope [ScopeVar]
  deriving (Eq, Show)

type MutCtx = Ctx MemVar (Scope, TeVarMutTrace)

instance Eq MemState where
  (==) (MemMoved _) (MemMoved _) = True
  (==) (MemExists as) (MemExists bs) = sort (nub as) == sort (nub bs)
  (==) _ _ = False


-- type MemRedirectionCtx = Ctx MemVar [MemVar]

--------------------------------------------------------
-- monoid instance for isMutated

instance Monad m => SemigroupM m IsMutated where
  (NotMutated) ⋆ b = pure b
  Mutated ⋆ b = pure Mutated
instance Monad m => MonoidM m IsMutated where
  neutral = pure NotMutated
instance Monad m => CheckNeutral m IsMutated where
  checkNeutral (NotMutated) = pure True
  checkNeutral (Mutated) = pure False

instance Semigroup IsMutated where
  (<>) = (⋆!)

instance Monoid IsMutated where
  mempty = neutralId


--------------------------------------------------------------------------------------
-- Memory info
--------------------------------------------------------------------------------------

data IsFunctionArgument = FunctionArgument | NotFunctionArgument
  deriving (Eq,Show)

data MemVarInfo = MemVarInfo
  {
    _ifaInfo :: IsFunctionArgument
  , _lastAssignmentLocInfo :: SourceLocExt
  }
$(makeLenses ''MemVarInfo)

type MemVarInfoCtx = Ctx MemVar MemVarInfo

--------------------------------------------------------------------------------------
-- Variable Access Type
--------------------------------------------------------------------------------------

-- NOTE: The order of constructors is relevant!
--       (in `computeVarAccessType`)
data VarAccessType = ReadSingle | ReadMulti | WriteSingleBase IsFLetDefined
  deriving (Show,Eq,Ord)

-- NOTE: The order of constructors is relevant!
--       (in `computeVarAccessType`)
data IsFLetDefined = NotFLetDefined | FLetDefined
  deriving (Show,Eq,Ord)

pattern WriteSingle = WriteSingleBase NotFLetDefined
pattern WriteSingleFunction = WriteSingleBase FLetDefined

-- type ImVarAccessCtx = Ctx ProcVar ()
type VarAccessCtx = Ctx ProcVar ([Scope], VarAccessType, ImmutType)


isIndependent :: Scope -> [Scope] -> Bool
isIndependent (Scope new) = all (\(Scope old) -> and [not (old `isSuffixOf` new), not (new `isSuffixOf` old)])


computeVarAccessType :: ProcVar -> ([Scope],VarAccessType) -> (Scope,VarAccessType) -> MTC VarAccessType
computeVarAccessType var (a,xvat) (b,yvat) = do
  let iOrE as b = or [b `isIndependent` as, b `elem` as]
  logForce $ "Computing var access type: "
  logForce $ "as: " <> showT a
  logForce $ "b:  " <> showT b
  logForce $ "indep: " <> showT (b `isIndependent` a) <> ", elem: " <> showT (b `elem` a)
  let f cur =
         case cur of
           [(ReadSingle), (ReadSingle)] | a `iOrE` b   -> pure ((ReadSingle))
           [(ReadSingle), (ReadSingle)] | otherwise    -> pure (ReadMulti)
           [(ReadSingle), (ReadMulti)]                 -> pure ((ReadMulti))
           [(ReadSingle), (WriteSingle)] | a `iOrE` b  -> pure ((WriteSingle))
           [(ReadSingle), (WriteSingle)] | otherwise   -> throwUnlocatedError $ DemutationVariableAccessTypeError $ "The variable '" <> showT var <> "' "
                                                                                  <> "' is being mutated and read in two different scopes.\n"
                                                                                  <> "This is not allowed."
           -- [(ReadSingle), (WriteSingleFunction)] | a == b -> pure ((WriteSingleFunction))
           -- [(ReadSingle), (WriteSingleFunction)] | a /= b -> throwUnlocatedError $ DemutationVariableAccessTypeError $ "The variable '" <> showT var <> "' "
           --                                                                                <> "' is being mutated and read in two different scopes.\n"
           --                                                                                <> "This is not allowed."
           [(ReadSingle), (WriteSingleFunction)]   -> pure ((WriteSingleFunction))
           [(ReadMulti),(ReadMulti)]                   -> pure ((ReadMulti))
           [(ReadMulti),(WriteSingle)]               -> throwUnlocatedError $ DemutationVariableAccessTypeError $ "The variable '" <> showT var <> "' "
                                                                                   <> "' is being mutated and read in two different scopes.\n"
                                                                                   <> "This is not allowed."
           [(ReadMulti),(WriteSingleFunction)]       -> throwUnlocatedError $ DemutationVariableAccessTypeError $ "The variable '" <> showT var <> "' cannot be redefined as a function after already being read somewhere. "
            --  pure ((WriteSingleFunction)) -- because of flet reordering it is allowed to mutate functions
           [(WriteSingle), (WriteSingle)] | a `iOrE` b  -> pure ((WriteSingle))
           -- [(WriteSingle) l, (WriteSingle) k] | a == b -> throwUnlocatedError $ DemutationError $ "The function argument '" <> showT var <> "' has been mutated.\n"
           --                                                                             <> "But then a statement follows which assigns a variable with the same name."
           --                                                                             <> "This is not allowed, please use a different name here."
           [(WriteSingle), (WriteSingle)]          -> throwUnlocatedError $ DemutationVariableAccessTypeError $ "The variable '" <> showT var <> "' "
                                                                                   <> "' is being mutated in two different scopes.\n"
                                                                                   <> "This is not allowed."
           [(WriteSingle), (WriteSingleFunction)]  -> throwUnlocatedError $ DemutationVariableAccessTypeError $ "The variable '" <> showT var <> "' is defined as function and as value."
                                                                                   <> "This is not allowed."
           [(WriteSingleFunction), (WriteSingleFunction)] | a `iOrE` b -> pure ((WriteSingleFunction))
           -- [(WriteSingleFunction), (WriteSingleFunction)] | a == b         -> throwUnlocatedError $ DemutationError $ "The function argument '" <> showT var <> "' has been mutated.\n"
           --                                                                             <> "But then a statement follows which assigns a variable with the same name."
           --                                                                             <> "This is not allowed, please use a different name here."
           [(WriteSingleFunction), (WriteSingleFunction)] | otherwise -> throwUnlocatedError $ DemutationVariableAccessTypeError $ "The variable '" <> showT var <> "' "
                                                                                   <> "' is being mutated in two different scopes.\n"
                                                                                   <> "This is not allowed."
           vavalues -> impossible $ "In demutation, while computing var access type. This branch should be inaccessible.\nlist is:\n" <> showT vavalues
  case xvat <= yvat of
    True -> f [(xvat), (yvat)]
    False -> f [(yvat), (xvat)]




--------------------------------------------------------------------------------------
-- The demutation monad
--------------------------------------------------------------------------------------

data MFull = MFull
  {
    _vaCtx :: VarAccessCtx
  , _memCtx :: MemCtx
  -- , _memRedirectionCtx :: MemRedirectionCtx
  , _mutCtx :: MutCtx
  , _termVarsOfMut :: NameCtx
  , _scopeNames :: NameCtx
  , _memNames :: NameCtx
  , _memVarInfo :: MemVarInfoCtx
  , _topLevelInfo :: TopLevelInformation
  }


type MTC = LightTC Location_PrePro_Demutation MFull

$(makeLenses ''MFull)


-- new variables
newTeVarOfMut :: (MonadState MFull m) => Text -> Maybe ProcVar -> m (TeVar)
newTeVarOfMut hint original = termVarsOfMut %%= (first (\x -> GenTeVar x (UserTeVar <$> original)) . (newName GeneratedNamePriority hint))

newScopeVar :: (MonadState MFull m) => Text -> m (ScopeVar)
newScopeVar hint = scopeNames %%= (first ScopeVar . (newName GeneratedNamePriority hint))

appendNewScopeVar :: (MonadState MFull m) => Text -> Scope -> m Scope
appendNewScopeVar hint (Scope old) = do
  v <- newScopeVar hint
  return (Scope (v : old))

newMemVar :: (MonadState MFull m) => Either ProcVar Text -> MemVarInfo -> m (MemVar)
newMemVar (Left hint) mvi = do
  mv <- scopeNames %%= (first (MemVarForProcVar hint) . (newName GeneratedNamePriority ""))
  memVarInfo %= (setValue mv mvi)
  return mv
newMemVar (Right hint) mvi = do
  mv <- scopeNames %%= (first StandaloneMemVar . (newName GeneratedNamePriority hint))
  memVarInfo %= (setValue mv mvi)
  return mv

allocateMem :: Scope -> Maybe ProcVar -> MemVarInfo -> MTC (MemVar)
allocateMem scopename procvar mvi = do
  let hint = case procvar of
              Just a -> Left a
              Nothing -> Right "anon"
  mv <- newMemVar hint mvi
  mutCtx %= (setValue mv (scopename, TeVarMutTrace Nothing NotSplit []))
  return mv

cleanupMem :: Scope -> MTC ()
cleanupMem scname = mutCtx %= (\ctx -> f ctx)
  where
    f = fromKeyElemPairs . filter (\(_,(scname2,_)) -> scname2 /= scname) . getAllKeyElemPairs

-- resetMutCtx :: MTC ()
-- resetMutCtx = mutCtx %= (\ctx -> f ctx)
--   where
--     f = fromKeyElemPairs . fmap ((\(k,(sc,v)) -> (k,(sc,[])))) . getAllKeyElemPairs

instance Monad m => MonoidM m MemState where
    neutral = pure $ MemExists []

instance Monad m => CheckNeutral m MemState where
    checkNeutral a = return (a == (MemExists []))

instance Monad m => SemigroupM m MemState where
    (⋆) (MemMoved l1) (MemMoved l2) = pure (MemMoved (nub (l1 <> l2)))
    (⋆) (MemMoved l1) (MemExists _) = pure (MemMoved l1)
    (⋆) (MemExists _) (MemMoved l2) = pure (MemMoved l2)
    (⋆) (MemExists l1) (MemExists l2) = pure $ MemExists (nub (l1 ++ l2))

mergeMemCtx = (⋆!)


-----------------------------------------------------------------------------------------------------
-- Memory and VA actions
-----------------------------------------------------------------------------------------------------


fst3 (a,b,c) = a

throwLocatedError err loc = throwError (WithContext err (DMPersistentMessage loc))
demutationError err loc = throwLocatedError (DemutationError err) loc
demutationErrorNoLoc err = throwUnlocatedError (DemutationError err)

-- buildReturnValue :: [ProcVar] -> DMTerm
-- buildReturnValue [x] = Var (Just x :- JTAny)
-- buildReturnValue xs = Tup [Var (Just x :- JTAny) | x <- xs]

-- buildCopyReturnValue :: [ProcVar] -> DMTerm
-- buildCopyReturnValue [x] = DeepcopyValue $ Var (Just x :- JTAny)
-- buildCopyReturnValue xs = Tup [DeepcopyValue $ Var (Just x :- JTAny) | x <- xs]

--------------------------------------------------------------------------------------
-- Accessing the VA-Ctx in the MTC monad

markReassignedBase :: IsFLetDefined -> Scope -> ProcVar -> ImmutType -> MTC ()
markReassignedBase fletdef scname tevar itype = do
  debug $ "[markReassignedBase]: called for " <> showT tevar <> " in " <> showT scname 

  -- make sure that we are still allowed to access this var
  -- memvar <- expectSingleMem =<< expectNotMoved tevar

  vaCtx %=~ (markReassignedInScope scname tevar itype)

  newvatype <- getValue tevar <$> use vaCtx

  -- extracting the new locality
  -- newloc <- case newvatype of
  --               Just (WriteSingleBase _ _ newloc) -> return newloc
  --               _ -> impossible "Expected the resulting locality after `markReassignedBase` to be a `WriteSingleBase`."

  return ()

    -- The actual updating function
    where 
      markReassignedInScope :: Scope -> ProcVar -> ImmutType -> VarAccessCtx -> MTC VarAccessCtx 
      markReassignedInScope scname tevar itype ctx =
        case getValue tevar ctx of
          Nothing -> return $ setValue tevar ([scname], ReadSingle, itype) ctx
          Just (oldscname, oldvatype, olditype) -> do
            case olditype == itype of
              True -> do
                newvatype <- computeVarAccessType tevar (oldscname, oldvatype) (scname, WriteSingleBase fletdef)
                debug $ "[markReassignedBase]: VA type for '" <> showT tevar <> "' changes from " <> showT oldvatype <> " to " <> showT newvatype
                return (setValue tevar (scname:oldscname, newvatype, olditype) ctx)
              False ->
                throwUnlocatedError (DemutationError $ "Found a redefinition of the variable '" <> showT tevar
                            <> "', where the old type (" <> showT olditype <> ") and the new type (" <> showT itype
                            <> ") differ. This is not allowed.")

markReassignedFLet :: Scope -> ProcVar -> ImmutType -> MTC ()
markReassignedFLet scname var itype = do
  log $ "Marking flet mutated for " <> showT var
  markReassignedBase FLetDefined scname var itype

--
-- Apply a mutation of `loc` locality to the `var`.
-- This might or might not change `loc`, depending on whether this variable
-- is already local or not-local.
-- The resulting locality is returned.
--
markReassigned :: Scope -> ProcVar -> ImmutType -> MTC ()
markReassigned scname var itype = do
  log $ "Marking simple mutated for " <> showT var
  markReassignedBase NotFLetDefined scname var itype


markRead :: Scope -> ProcVar -> MTC ImmutType
markRead scname tevar = do
   debug $ "[markRead]: called for tevar" <> showT tevar <> " in " <> showT scname 
  --  mvars <- getAllMemVars <$> expectNotMoved var -- we make sure that we are still allowed to use this variable
   let f v = vaCtx %=~ (markReadInScope scname v) 
        where 
          markReadInScope :: Scope -> ProcVar -> VarAccessCtx -> MTC VarAccessCtx 
          markReadInScope scname tevar ctx =
            case getValue tevar ctx of
              Nothing -> throwUnlocatedError (DemutationDefinitionOrderError tevar)
              Just (oldscname, oldvatype, olditype) -> do
                newvatype <- computeVarAccessType tevar (oldscname, oldvatype) (scname, ReadSingle)
                return (setValue tevar (scname:oldscname,newvatype, olditype) ctx)

   f tevar

   val <- getValue tevar <$> use vaCtx 
   case val of
     Nothing -> internalError $ "Expected the procvar " <> showT tevar <> " to have an assignment because it was set just a moment ago."
     Just (_,_,itype) -> return itype

markReadMaybe :: Scope -> Maybe ProcVar -> MTC (Maybe ImmutType)
markReadMaybe scname (Just x) = Just <$> markRead scname x
markReadMaybe scname Nothing = pure Nothing

markReadOverwritePrevious :: Scope -> ProcVar -> ImmutType -> MTC ()
markReadOverwritePrevious scname var itype = vaCtx %%= (\scope -> ((), setValue var ([scname], ReadSingle, itype) scope))


cleanupVACtxAfterScopeEnd :: VarAccessCtx -> MTC ()
cleanupVACtxAfterScopeEnd vaCtxBefore = do
  --
  -- if a procvar was not in the vactx before,
  -- it means that it is localnd thus should be removed.
  let restoreArg procvar = do
        case getValue procvar vaCtxBefore of
          Nothing       -> vaCtx %%= (\ctx -> ((), deleteValue procvar ctx))
          Just oldvalue -> pure ()
  --
  -- We do this for all vars in the current vactx
  vaCtxAfter <- use vaCtx
  mapM_ restoreArg (getAllKeys vaCtxAfter)



--------------------------------------------------------------------------------------

markMutated :: ProcVar -> SourceLocExt -> DMPersistentMessage MTC -> MTC TeVar
markMutated pv loc msg = do
  mv <- expectSingleMem msg =<< expectNotMoved loc pv
  tevar <- newTeVarOfMut (showT mv) (Just pv)
  let f ctx = do
        case getValue mv ctx of
          Nothing -> impossible $ "Wanted to mark the memvar " <> showT mv <> " as mutated, but it was not in the mutctx."
          Just (scvar, TeVarMutTrace pv split tevars) -> return $ setValue mv (scvar, TeVarMutTrace pv split ((tevar,[loc]):tevars)) ctx

  mutCtx %=~ f
  return tevar


--------------------------------------------------------------------------------------


{-
wrapReorder :: (Eq a, Show a) => [a] -> [a] -> PreDMTerm t -> PreDMTerm t
wrapReorder have want term | have == want = term
wrapReorder have want term | otherwise    =
  let σ = getPermutationWithDrop have want
  in Reorder σ (term)

immutTypeEq :: ImmutType -> ImmutType -> Bool
immutTypeEq (Pure _) (Pure _) = True
immutTypeEq (Mutating a) (Mutating b) = a == b
immutTypeEq (VirtualMutated a) (VirtualMutated b) = a == b
immutTypeEq (PureBlackBox) (PureBlackBox) = True
immutTypeEq _ _ = False
-}

-- set the type of the variable in scope,
-- but do not allow to change that value afterwards.
-- This has to happen after the memory location is set
{-
safeSetValueBase :: IsFLetDefined -> ScopeVar -> Maybe ProcVar -> ImmutType -> MTC ()
safeSetValueBase fletdef scname (Nothing) itype = pure ()
safeSetValueBase fletdef scname (Just var) itype = do

  markReassignedBase fletdef scname var itype
-}
{-
  scope <- use vaCtx

  case getValue var scope of
    Nothing -> do
      debug $ "[safeSetValue]: Var " <> showT var <> " not in scope " <> showT scname <> ". Marking read."
      markRead scname var
      -- return (setValue var newType scope)
    (Just oldType) -> do
      debug $ "[safeSetValue]: Var " <> showT var <> " is already in scope " <> showT scname <> ". Marking as mutated."
      markReassignedBase fletdef scname var -- We say that we are changing this variable. This can throw an error.
      if immutTypeEq oldType newType
                      then pure scope
                      else throwUnlocatedError (DemutationError $ "Found a redefinition of the variable '" <> showT var <> "', where the old type (" <> showT oldType <> ") and the new type (" <> showT newType <> ") differ. This is not allowed.")
-}

{-
safeSetValue = safeSetValueBase NotFLetDefined
safeSetValueAllowFLet = safeSetValueBase FLetDefined
-}
{-
safeSetValueAllowFLet :: Maybe ProcVar -> ImmutType -> Scope -> MTC Scope
safeSetValueAllowFLet (Nothing) newType scope = pure scope
safeSetValueAllowFLet (Just var) newType scope =
  case getValue var scope of
    Nothing -> pure $ setValue var newType scope
    (Just oldType) -> if immutTypeEq oldType newType
                      then pure scope
                      else throwUnlocatedError (DemutationError $ "Found a redefinition of the variable '" <> showT var <> "', where the old type (" <> showT oldType <> ") and the new type (" <> showT newType <> ") differ. This is not allowed.")
-}

--------------------------------------------------------------------------------
-- immuttype access
--------------------------------------------------------------------------------

expectImmutType :: Scope -> ProcVar -> MTC ImmutType
expectImmutType = markRead

setImmutType :: Scope -> ProcVar -> ImmutType -> MTC ()
setImmutType = markReassigned

backupAndSetImmutType :: Scope -> ProcVar -> ImmutType -> MTC (Maybe ImmutType)
backupAndSetImmutType scname procvar itype = do
  oldVal <- getValue procvar <$> use vaCtx
  case oldVal of
    Nothing          -> setImmutType scname procvar itype >> return Nothing
    Just (_,_,itype) -> setImmutType scname procvar itype >> return (Just itype)

setImmutTypeFLetDefined :: Scope -> ProcVar -> ImmutType -> MTC ()
setImmutTypeFLetDefined = markReassignedFLet

setImmutTypeOverwritePrevious :: Scope -> ProcVar -> ImmutType -> MTC ()
setImmutTypeOverwritePrevious = markReadOverwritePrevious


--------------------------------------------------------------------------------
-- memory access
--------------------------------------------------------------------------------



-- change last move Loc for memvars
setLastAssignmentLocMemVar :: SourceLocExt -> MemVar -> MTC ()
setLastAssignmentLocMemVar loc mv = do
  memVarInfo <%= changeValue mv (\(MemVarInfo a _) -> (MemVarInfo a loc))
  return ()

-- change last move Loc for memtypes
setLastAssignmentLocMem :: SourceLocExt -> MemType -> MTC ()
setLastAssignmentLocMem loc = \case
  TupleMem mts  -> mapM_ (setLastAssignmentLocMem loc) mts
  SingleMem mv  -> setLastAssignmentLocMemVar loc mv
  RefMem mv     -> setLastAssignmentLocMemVar loc mv



--
-- We have:
-- ```
-- Prelude> oneOfEach [[1,2], [10,20,30], [100]]
-- [[1,10,100],[1,20,100],[1,30,100],[2,10,100],[2,20,100],[2,30,100]]
-- ```
--
oneOfEach :: [[a]] -> [[a]]
oneOfEach (xs:yss) = let yss' = oneOfEach yss
                     in ([x:ys' | x <- xs, ys' <- yss'])
oneOfEach [] = [[]]



moveGetMem_Loc :: Scope -> SourceLocExt -> Maybe ProcVar-> LocMoveType -> MTC [MemType]
moveGetMem_Loc scname loc pv (Located _ mt) = moveGetMem scname loc pv mt

moveGetMem :: Scope -> SourceLocExt -> Maybe ProcVar -> MoveType -> MTC [MemType]
moveGetMem scname loc pv (NoMove te) = do
  mem <- allocateMem scname pv (MemVarInfo NotFunctionArgument loc)
  return [(SingleMem mem)]
moveGetMem scname loc pv (SingleMove a) = do
  memstate <- expectNotMoved loc a
  mapM (setLastAssignmentLocMem loc) memstate -- set last assignment loc for information purposes
  memCtx %= (setValue a (MemMoved [loc]))
  return (memstate)
moveGetMem scname loc pv (PhiMove _ (mt1,_) (mt2,_)) = do
  memt1 <- moveGetMem_Loc scname loc Nothing mt1
  memt2 <- moveGetMem_Loc scname loc Nothing mt2
  return (memt1 <> memt2)
moveGetMem scname loc pv (TupleMove as) = do
  mems <- mapM (moveGetMem_Loc scname loc Nothing) as
  return (TupleMem <$> oneOfEach mems)
moveGetMem scname loc pv (RefMove te) = do
  -- if we had a reference,
  -- allocate new memory for it
  memvar <- allocateMem scname pv (MemVarInfo NotFunctionArgument loc)
  pure $ [RefMem memvar]



setMem :: ProcVar -> [MemType] -> MTC () 
setMem x mt = do
  -- set the memory type for procvar `x`
  memCtx %= (setValue x (MemExists mt))

  -- set the owner of the SingleVars in `mt`
  let smt = [s | SingleMem s <- mt]
  let setOwner s = do
        mutCtx <%= changeValue s (\(scopeVar, TeVarMutTrace oldOwner split trace) -> (scopeVar, TeVarMutTrace (Just x) split trace))

  mapM_ setOwner smt

setMemMaybe :: Maybe ProcVar -> [MemType] -> MTC () 
setMemMaybe (Just x) mt = setMem x mt
setMemMaybe (Nothing) _ = pure ()


setMemTupleInManyMems :: SourceLocExt -> Scope -> [ProcVar] -> [MemType] -> MTC ()
setMemTupleInManyMems loc scname xs mems = mapM_ (setMemTuple loc scname xs) mems

setMemTuple :: SourceLocExt -> Scope -> [ProcVar] -> MemType -> MTC ()
setMemTuple loc scname xs (SingleMem a) = do
  -- we get the memory info of the input var
  mvictx <- use memVarInfo
  MemVarInfo ifa _ <- case getValue a mvictx of
        Nothing -> internalError $ "Expected the memvariable " <> showT a <> " to have an info entry."
        Just ifa -> return ifa

  -- We are deconstructing a tuple value,
  -- need to create memory locations for all parts
  let f (x) = do
        mx <- allocateMem scname (Just x) (MemVarInfo ifa loc) -- NOTE: We update the `lastAssignmentLoc` here for RHS!
        setMem x [SingleMem mx]
        return mx
  memvars <- mapM f xs

  -- furthermore we mark the rhs mem location as split
  rhs_mut <- getValue a <$> use mutCtx

  case rhs_mut of
    Nothing -> internalError $ "Expected the memory location " <> showT a <> " to have a mutation status."
    Just (scvar,TeVarMutTrace pv _ ts) -> mutCtx %= (setValue a (scvar, TeVarMutTrace pv (Split memvars) ts))

setMemTuple loc scname xs (RefMem a) = do
  mapM_ (\(x) -> setMemMaybe x ([RefMem a])) (Just <$> xs)

setMemTuple loc scname xs (TupleMem as) | length xs == length as = do
  let xas = zip xs as
  mapM_ (\(x, a) -> setMem x [a]) xas

setMemTuple loc scname xs (TupleMem as) | otherwise = demutationError ("Trying to assign a tuple where lengths do not match.")
                                                                      (loc :\\:
                                                                       ("The LHS has length " <> showT (length xs) <> ", while the RHS has length " <> showT (length as) <> ".") :\\:
                                                                       "" :\\:
                                                                       ("Debug info: the inferred memory state is: " <> showT xs <> " = " <> showT as)
                                                                      )

expectNotMoved :: SourceLocExt -> ProcVar -> MTC [MemType]
expectNotMoved loc tevar = do
  mc <- use memCtx
  case getValue tevar mc of
    Nothing          -> throwLocatedError (DemutationDefinitionOrderError $ tevar) (DMPersistentMessage @MTC loc)
    Just (MemMoved movedlocs) -> do
      let edits = (loc, "trying to access " <> quote (showPretty tevar)) :
                  [(l, "content of " <> quote (showPretty tevar) <> " is already moved away here") | l <- movedlocs]

      throwLocatedError (DemutationMovedVariableAccessError tevar) (SourceQuote edits)
                                      
    Just (MemExists a) -> pure a



-------------------------------------
-- accessing memories

getAllMemVars :: MemType -> [MemVar]
getAllMemVars (SingleMem a) = [a]
getAllMemVars (TupleMem a) = a >>= getAllMemVars
getAllMemVars (RefMem a) = [a]

getAllMemVarsOfMemState :: MemState -> [MemVar]
getAllMemVarsOfMemState (MemExists ms) = ms >>= getAllMemVars
getAllMemVarsOfMemState (MemMoved _) = []

expectSingleMem :: DMPersistentMessage MTC -> [MemType] -> MTC MemVar
expectSingleMem msg mts = do
  case mts of
    [mt] -> case mt of
              (SingleMem a) -> pure a
              (mem) -> demutationError ("Encountered a value spanning multiple memory locations where a single location value was expected.")
                                       (msg :\\:
                                        ("The encountered memory type is " <> showT mem))
    mts -> demutationError ("Encountered a value spanning multiple possible memory locations where a single location value was expected.")
                                       (msg :\\:
                                        ("The encountered memory type is " <> showT mts))




getMemVarMutationStatus :: MemVar -> MTC (IsSplit, [(TeVar,[SourceLocExt])])
getMemVarMutationStatus mv = do
  mctx <- use mutCtx
  case getValue mv mctx of
    Nothing -> internalError $ "Expected memory location to have a mutation status, but it didn't. MemVar: " <> showT mv
    Just (_, TeVarMutTrace _ split tvars) -> return (split,tvars)


coequalizeTeVarMutTrace :: TeVarMutTrace -> TeVarMutTrace -> WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC TeVarMutTrace
coequalizeTeVarMutTrace (TeVarMutTrace pv1 split1 ts1) (TeVarMutTrace pv2 split2 ts2) | and [ts1 == ts2, pv1 == pv2, split1 == split2] = pure $ TeVarMutTrace pv1 split1 ts1
coequalizeTeVarMutTrace (TeVarMutTrace pv1 split1 ts1) (TeVarMutTrace pv2 split2 ts2)  = do
  t3 <- newTeVarOfMut "phi" Nothing
  let makeProj (Just pv) []            = pure $ (Extra (DemutSLetBase PureLet (t3) (notLocated $ Var (UserTeVar pv))), [])
      makeProj Nothing   []            = lift $ demutationErrorNoLoc $ "While demutating phi encountered a branch where a proc-var-less memory location is mutated. This cannot be done."
      makeProj _         ((t,locs):ts) = pure $ (Extra (DemutSLetBase PureLet (t3) (notLocated $ Var (t))), locs)

  (proj1,locs1) <- makeProj pv1 ts1 
  (proj2,locs2) <- makeProj pv2 ts2

  lift $ debug $ "Coequalizing MutTraces:\n"
  lift $ debug $ "  proj1: " <> showT proj1
  lift $ debug $ "  proj2: " <> showT proj2

  -- we check whether the muttraces belong to the same procvars
  case pv1 == pv2 of
    --
    -- if they don't then this memory location cannot be used anymore after the if
    False -> return $ TeVarMutTrace Nothing NotSplit ([])
    --
    -- if they do, we can actually coequalize
    True -> do
      tell ([notLocated proj1],[notLocated proj2])

      let pv3 = pv1

      split3 <- case (split1,split2) of
                  (NotSplit, NotSplit) -> pure NotSplit
                  (NotSplit, Split a) -> pure (Split a)
                  (Split a, NotSplit) -> pure (Split a)
                  (Split a, Split b) -> pure (Split (a <> b))

      pure $ TeVarMutTrace pv3 split3 ((t3,locs1<>locs2) : ts1 <> ts2)



instance SemigroupM (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) TeVarMutTrace where
  (⋆) = coequalizeTeVarMutTrace
instance MonoidM (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) TeVarMutTrace where
  neutral = pure $ TeVarMutTrace Nothing NotSplit []
instance CheckNeutral (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) TeVarMutTrace where
  checkNeutral _ = pure False

instance SemigroupM (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) Scope where
  (⋆) a b | a == b    = pure a
  (⋆) a b | otherwise = lift $ demutationErrorNoLoc $ "While demutating phi, encountered two branches where the scopevars of a memvar differ. This is not allowed."
instance MonoidM (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) Scope where
  neutral = lift $ internalError $ "There is no neutral element for scopevars"

instance CheckNeutral (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) Scope where
  checkNeutral _ = pure False

coequalizeMutCtx :: MutCtx -> MutCtx -> MTC (MutCtx, ([LocDemutDMTerm], [LocDemutDMTerm]))
coequalizeMutCtx muts1 muts2 = runWriterT (muts1 ⋆ muts2)



--------------------------------------------------------------------------
-- Creating TeVars from MemVars
--
-- memTypeAsTerm :: MemType -> DemutDMTerm
-- memTypeAsTerm mt = case mt of
--   TupleMem mts -> undefined
--   SingleMem mv -> undefined
--   RefMem mv -> undefined


getLastAssignedLocs :: MemType -> MTC [SourceLocExt]
getLastAssignedLocs mt = do
  mvinfo <- use memVarInfo
  let mvs = getAllMemVars mt
  let f mv = case getValue mv mvinfo of
               Nothing -> []
               Just mvi -> [_lastAssignmentLocInfo mvi]
  return (f =<< mvs)

--
-- | Create a tevar for a procvar.
--    If procvar contains a memory location which is
--    a `SingleMem` and is mutatedse the newest variable
--    name from the `mutCtx`. Else create a tvar based on the
--    input name `mv`.
--
--    Since there are multiple memory types associated to
--    a procvar, they are dealt with as follows:
--    There are two valid possibilities:
--    1. all memory types do not contain mutated variables
--    2. all memory types are single varnd all are mutated,
--       with last tevar being the same
procVarAsTeVar :: ProcVar -> SourceLocExt -> MTC TeVar
procVarAsTeVar pv loc = do
  mts <- expectNotMoved loc pv
  --
  -- all memory types which contain mutated vars
  let getMutatedName x = do
        (_,mmut) <- getMemVarMutationStatus x
        case mmut of
          []     -> return []
          (x:xs) -> return [x]
  mut_mts <- join <$> mapM getMutatedName (getAllMemVars =<< mts)
  --
  -- if we have no mutations, we are done
  case fst <$> mut_mts of
    []     -> pure (UserTeVar pv)
    --
    -- if there are mutations, we need
    -- to make sure that all tevars are the same
    (x:xs) -> case all (== x) xs of
      False -> do
        let makeMessage (i, mt) = do
              locs <- getLastAssignedLocs mt
              return [(l, quote (showPretty pv) <> " assigned in execution branch " <> showPretty i) | l <- locs]

        messages <- (mapM makeMessage (zip [1..] mts))
        let messages' = (loc,quote (showPretty pv) <> " is used here"):join messages

        demutationError ("Illegal variable assignment combination.")
                 ("The variable " :<>: Quote pv :<>: " is being assigned different memory locations in different execution branches." :\\:
                 SourceQuote messages' :\\:
                 ("This is not allowed. A possible fix could be to write `" <> showPretty pv <> " = clone(...)` instead.") :\\:
                 "" :\\:
                 ("Debug Info: Inferred memory type is:" <> showT mts)
                 )

      True  -> pure x

procVarAsTeVarInMutCtx :: MemCtx -> MutCtx -> SourceLocExt -> ProcVar -> MTC TeVar
procVarAsTeVarInMutCtx tempMemCtx tempMutCtx msg pv = do
  oldMutCtx <- use mutCtx
  oldMemCtx <- use memCtx
  mutCtx .= tempMutCtx
  memCtx .= tempMemCtx
  val <- procVarAsTeVar pv msg
  mutCtx .= oldMutCtx
  memCtx .= oldMemCtx
  return val

moveTypeAsTerm_Loc :: SourceLocExt -> LocMoveType -> MTC LocDemutDMTerm
moveTypeAsTerm_Loc msg = mapM (moveTypeAsTerm msg)

moveTypeAsTerm :: SourceLocExt -> MoveType -> MTC DemutDMTerm
moveTypeAsTerm msg = \case
  TupleMove mts -> do
    terms <- mapM (moveTypeAsTerm_Loc msg) mts
    pure $ (Tup terms)
  SingleMove pv -> do tv <- procVarAsTeVar pv msg ; pure $ Var $ (tv)
  PhiMove cond (_,tt1) (_,tt2) -> return (Extra (DemutPhi cond tt1 tt2))
  RefMove pdt   -> pure pdt
  NoMove pdt    -> pure pdt


movedVarsOfMoveType_Loc :: LocMoveType -> [ProcVar]
movedVarsOfMoveType_Loc = movedVarsOfMoveType . getLocated

movedVarsOfMoveType :: MoveType -> [ProcVar]
movedVarsOfMoveType = \case
  TupleMove mts -> mts >>= movedVarsOfMoveType_Loc
  SingleMove pv -> return pv
  PhiMove cond (mt1,_) (mt2,_) -> movedVarsOfMoveType_Loc mt1 <> movedVarsOfMoveType_Loc mt2
  RefMove pdt -> []
  NoMove pdt -> []

termTypeAsTerm :: SourceLocExt -> TermType -> MTC LocDemutDMTerm
termTypeAsTerm msg = \case
  Value it mt -> moveTypeAsTerm_Loc msg mt
  Statement l pdt mt -> do
    mt' <- moveTypeAsTerm msg mt
    pure $ Located l $ Extra $ DemutBlock [Located l pdt, Located l mt']
  StatementWithoutDefault l pdt -> pure $ Located l $ Extra $ DemutBlock [Located l pdt]
  MutatingFunctionEnd l       -> pure $ Located l $ Extra $ DemutBlock []


