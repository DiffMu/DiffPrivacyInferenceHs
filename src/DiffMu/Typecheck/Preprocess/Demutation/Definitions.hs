
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

import qualified Data.Text as T
import Data.Foldable

import Debug.Trace

import qualified Prelude as P



--------------------------------------------------------------------------------------
-- Demutation Type
--------------------------------------------------------------------------------------


data IsMutated = Mutated | NotMutated
  deriving (Generic, Show, Eq)

data IsLocalMutation = LocalMutation | NotLocalMutation
  deriving (Show, Eq)

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

-- consumeDefaultValue :: ImmutType -> ImmutType
-- consumeDefaultValue (Pure DefaultValue) = Pure UserValue
-- consumeDefaultValue a = a

-- the scope
-- type Scope = Ctx ProcVar ImmutType


---------------------------------------------------
-- These types describe which variable names
-- are in the RHS and must be moved on tlet/slet assignment
-- See #171 #172
data MoveType = TupleMove [MoveType] | SingleMove ProcVar | RefMove DemutDMTerm | NoMove DemutDMTerm
  deriving (Eq, Show)

-- singleMoveMaybe :: Maybe ProcVar -> MoveType
-- singleMoveMaybe (Just a) = SingleMove a
-- singleMoveMaybe Nothing  = NoMove

data TermType =
  Value ImmutType MoveType
  | Statement DemutDMTerm MoveType
  | StatementWithoutDefault DemutDMTerm
  | MutatingFunctionEnd

data LastValue =
   PureValue MoveType
   | MutatingFunctionEndValue


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
  deriving (Eq, Show)

data MemState = MemExists [MemType] | MemMoved
  deriving (Show, Eq)

data MemAssignmentType = AllocNecessary | PreexistingMem

type MemCtx = Ctx ProcVar MemState

type MutCtx = Ctx MemVar (ScopeVar, [TeVar])

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
-- Variable Access Type
--------------------------------------------------------------------------------------

data VarAccessType = ReadSingle | ReadMulti | WriteSingleBase IsFLetDefined
  deriving (Show,Eq,Ord)

data IsFLetDefined = FLetDefined | NotFLetDefined
  deriving (Show,Eq,Ord)

pattern WriteSingle = WriteSingleBase NotFLetDefined
pattern WriteSingleFunction = WriteSingleBase FLetDefined

-- type ImVarAccessCtx = Ctx ProcVar ()
type VarAccessCtx = Ctx ProcVar (ScopeVar, VarAccessType, ImmutType)


computeVarAccessType :: ProcVar -> (ScopeVar,VarAccessType) -> (ScopeVar,VarAccessType) -> MTC VarAccessType
computeVarAccessType var (x,xvat) (y,yvat) = do
  let f cur =
         case cur of
           [(ReadSingle, a), (ReadSingle, b)] | a == b   -> pure ((ReadSingle))
           [(ReadSingle, a), (ReadSingle, b)] | a /= b   -> pure (ReadMulti)
           [(ReadSingle, a), (ReadMulti, u)]               -> pure ((ReadMulti))
           [(ReadSingle, a), (WriteSingle, b)] | a == b  -> pure ((WriteSingle))
           [(ReadSingle, a), (WriteSingle, b)] | a /= b  -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                                  <> "' is being mutated and read in two different scopes.\n"
                                                                                  <> "This is not allowed."
           -- [(ReadSingle, a), (WriteSingleFunction, b)] | a == b -> pure ((WriteSingleFunction, a))
           -- [(ReadSingle, a), (WriteSingleFunction, b)] | a /= b -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
           --                                                                                <> "' is being mutated and read in two different scopes.\n"
           --                                                                                <> "This is not allowed."
           [(ReadSingle, a), (WriteSingleFunction, b)]   -> pure ((WriteSingleFunction))
           [(ReadMulti, u),(ReadMulti, v)]                   -> pure ((ReadMulti))
           [(ReadMulti, u),(WriteSingle, _)]               -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                                   <> "' is being mutated and read in two different scopes.\n"
                                                                                   <> "This is not allowed."
           [(ReadMulti, u),(WriteSingleFunction, a)]       -> pure ((WriteSingleFunction)) -- because of flet reordering it is allowed to mutate functions
           [(WriteSingle, a), (WriteSingle, b)] | a == b  -> pure ((WriteSingle))
           -- [(WriteSingle, a) l, (WriteSingle, b) k] | a == b -> throwError $ DemutationError $ "The function argument '" <> show var <> "' has been mutated.\n"
           --                                                                             <> "But then a statement follows which assigns a variable with the same name."
           --                                                                             <> "This is not allowed, please use a different name here."
           [(WriteSingle, a), (WriteSingle, b)]          -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                                   <> "' is being mutated in two different scopes.\n"
                                                                                   <> "This is not allowed."
           [(WriteSingle, _), (WriteSingleFunction, _)]  -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' is defined as function and as value."
                                                                                   <> "This is not allowed."
           [(WriteSingleFunction, a), (WriteSingleFunction, b)] | a == b -> pure ((WriteSingleFunction))
           -- [(WriteSingleFunction, a), (WriteSingleFunction, b)] | a == b         -> throwError $ DemutationError $ "The function argument '" <> show var <> "' has been mutated.\n"
           --                                                                             <> "But then a statement follows which assigns a variable with the same name."
           --                                                                             <> "This is not allowed, please use a different name here."
           [(WriteSingleFunction, a), (WriteSingleFunction, b)] | a /= b -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                                   <> "' is being mutated in two different scopes.\n"
                                                                                   <> "This is not allowed."
           vavalues -> impossible $ "In demutation, while computing var access type. This branch should be inaccessible.\nlist is:\n" <> show vavalues
  case xvat <= yvat of
    True -> f [(xvat,x), (yvat,y)]
    False -> f [(yvat,y), (xvat,x)]



--------------------------------------------------------------------------------------
-- Memory types and local aliasing
--------------------------------------------------------------------------------------



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
  , _topLevelInfo :: TopLevelInformation
  }


type MTC = LightTC Location_PrePro_Demutation MFull

$(makeLenses ''MFull)


-- new variables
newTeVarOfMut :: (MonadState MFull m) => Text -> m (TeVar)
newTeVarOfMut hint = termVarsOfMut %%= (first GenTeVar . (newName hint))

newScopeVar :: (MonadState MFull m) => Text -> m (ScopeVar)
newScopeVar hint = scopeNames %%= (first ScopeVar . (newName hint))

newMemVar :: (MonadState MFull m) => Either ProcVar Text -> m (MemVar)
newMemVar (Left hint) = scopeNames %%= (first (MemVarForProcVar hint) . (newName ""))
newMemVar (Right hint) = scopeNames %%= (first StandaloneMemVar . (newName hint))

allocateMem :: ScopeVar -> Either ProcVar Text -> MTC (MemVar)
allocateMem scopename hint = do
  mv <- newMemVar (hint)
  mutCtx %= (setValue mv (scopename, []))
  return mv

cleanupMem :: ScopeVar -> MTC ()
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
    (⋆) MemMoved _ = pure MemMoved
    (⋆) _ MemMoved = pure MemMoved
    (⋆) (MemExists l1) (MemExists l2) = pure $ MemExists (l1 ++ l2)

mergeMemCtx = (⋆!)


-----------------------------------------------------------------------------------------------------
-- Memory and VA actions
-----------------------------------------------------------------------------------------------------


fst3 (a,b,c) = a

demutationError = throwError . DemutationError

-- buildReturnValue :: [ProcVar] -> DMTerm
-- buildReturnValue [x] = Var (Just x :- JTAny)
-- buildReturnValue xs = Tup [Var (Just x :- JTAny) | x <- xs]

-- buildCopyReturnValue :: [ProcVar] -> DMTerm
-- buildCopyReturnValue [x] = DeepcopyValue $ Var (Just x :- JTAny)
-- buildCopyReturnValue xs = Tup [DeepcopyValue $ Var (Just x :- JTAny) | x <- xs]

--------------------------------------------------------------------------------------
-- Accessing the VA-Ctx in the MTC monad

markReassignedBase :: IsFLetDefined -> ScopeVar -> ProcVar -> ImmutType -> MTC ()
markReassignedBase fletdef scname tevar itype = do
  debug $ "[markReassignedBase]: called for " <> show tevar <> " in " <> show scname 

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
      markReassignedInScope :: ScopeVar -> ProcVar -> ImmutType -> VarAccessCtx -> MTC VarAccessCtx 
      markReassignedInScope scname tevar itype ctx =
        case getValue tevar ctx of
          Nothing -> return $ setValue tevar (scname, ReadSingle, itype) ctx
          Just (oldscname, oldvatype, olditype) -> do
            case olditype == itype of
              True -> do
                newvatype <- computeVarAccessType tevar (oldscname, oldvatype) (scname, WriteSingleBase fletdef)
                debug $ "[markReassignedBase]: VA type for '" <> show tevar <> "' changes from " <> show oldvatype <> " to " <> show newvatype
                return (setValue tevar (scname, newvatype, olditype) ctx)
              False ->
                throwError (DemutationError $ "Found a redefinition of the variable '" <> show tevar
                            <> "', where the old type (" <> show olditype <> ") and the new type (" <> show itype
                            <> ") differ. This is not allowed.")

markReassignedFLet :: ScopeVar -> ProcVar -> ImmutType -> MTC ()
markReassignedFLet scname var itype = do
  log $ "Marking flet mutated for " <> show var
  markReassignedBase FLetDefined scname var itype

--
-- Apply a mutation of `loc` locality to the `var`.
-- This might or might not change `loc`, depending on whether this variable
-- is already local or not-local.
-- The resulting locality is returned.
--
markReassigned :: ScopeVar -> ProcVar -> ImmutType -> MTC ()
markReassigned scname var itype = do
  log $ "Marking simple mutated for " <> show var
  markReassignedBase NotFLetDefined scname var itype


markRead :: ScopeVar -> ProcVar -> MTC ImmutType
markRead scname tevar = do
   debug $ "[markRead]: called for tevar" <> show tevar <> " in " <> show scname 
  --  mvars <- getAllMemVars <$> expectNotMoved var -- we make sure that we are still allowed to use this variable
   let f v = vaCtx %=~ (markReadInScope scname v) 
        where 
          markReadInScope :: ScopeVar -> ProcVar -> VarAccessCtx -> MTC VarAccessCtx 
          markReadInScope scname tevar ctx =
            case getValue tevar ctx of
              Nothing -> throwError (DemutationDefinitionOrderError tevar)
              Just (oldscname, oldvatype, olditype) -> do
                newvatype <- computeVarAccessType tevar (oldscname, oldvatype) (scname, ReadSingle)
                return (setValue tevar (scname,newvatype, olditype) ctx)

   f tevar
   
   val <- getValue tevar <$> use vaCtx 
   case val of
     Nothing -> internalError $ "Expected the procvar " <> show tevar <> " to have an assignment because it was set just a moment ago."
     Just (_,_,itype) -> return itype

markReadMaybe :: ScopeVar -> Maybe ProcVar -> MTC (Maybe ImmutType)
markReadMaybe scname (Just x) = Just <$> markRead scname x
markReadMaybe scname Nothing = pure Nothing

markReadOverwritePrevious :: ScopeVar -> ProcVar -> ImmutType -> MTC ()
markReadOverwritePrevious scname var itype = vaCtx %%= (\scope -> ((), setValue var (scname, ReadSingle, itype) scope))


--------------------------------------------------------------------------------------

markMutated :: MemVar -> MTC TeVar
markMutated mv = do
  tevar <- newTeVarOfMut (T.pack $ show mv)
  let f ctx = do
        case getValue mv ctx of
          Nothing -> impossible $ "Wanted to mark the memvar " <> show mv <> " as mutated, but it was not in the mutctx."
          Just (scvar,tevars) -> return $ setValue mv (scvar, tevar:tevars) ctx

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
      debug $ "[safeSetValue]: Var " <> show var <> " not in scope " <> show scname <> ". Marking read."
      markRead scname var
      -- return (setValue var newType scope)
    (Just oldType) -> do
      debug $ "[safeSetValue]: Var " <> show var <> " is already in scope " <> show scname <> ". Marking as mutated."
      markReassignedBase fletdef scname var -- We say that we are changing this variable. This can throw an error.
      if immutTypeEq oldType newType
                      then pure scope
                      else throwError (DemutationError $ "Found a redefinition of the variable '" <> show var <> "', where the old type (" <> show oldType <> ") and the new type (" <> show newType <> ") differ. This is not allowed.")
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
                      else throwError (DemutationError $ "Found a redefinition of the variable '" <> show var <> "', where the old type (" <> show oldType <> ") and the new type (" <> show newType <> ") differ. This is not allowed.")
-}

--------------------------------------------------------------------------------
-- immuttype access
--------------------------------------------------------------------------------

expectImmutType :: ScopeVar -> ProcVar -> MTC ImmutType
expectImmutType = markRead

setImmutType :: ScopeVar -> ProcVar -> ImmutType -> MTC ()
setImmutType = markReassigned

backupAndSetImmutType :: ScopeVar -> ProcVar -> ImmutType -> MTC (Maybe ImmutType)
backupAndSetImmutType scname procvar itype = do
  oldVal <- getValue procvar <$> use vaCtx
  case oldVal of
    Nothing          -> setImmutType scname procvar itype >> return Nothing
    Just (_,_,itype) -> setImmutType scname procvar itype >> return (Just itype)

setImmutTypeFLetDefined :: ScopeVar -> ProcVar -> ImmutType -> MTC ()
setImmutTypeFLetDefined = markReassignedFLet

setImmutTypeOverwritePrevious :: ScopeVar -> ProcVar -> ImmutType -> MTC ()
setImmutTypeOverwritePrevious = markReadOverwritePrevious


--------------------------------------------------------------------------------
-- memory access
--------------------------------------------------------------------------------



--
-- This function marks variables as moved in the scope
-- For #172
--
-- moveGetMemAndAllocs :: ScopeVar -> MoveType -> MTC ([MemType], [(MemVar,DemutDMTerm)])
-- moveGetMemAndAllocs scname mt = runWriterT (moveGetMemAndAllocs_impl scname mt)


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



moveGetMem :: ScopeVar -> MoveType -> MTC [MemType]
moveGetMem scname (NoMove te) = do
  mem <- allocateMem scname (Right "val")
  return [(SingleMem mem)]
moveGetMem scname (SingleMove a) = do
  memstate <- expectNotMoved a
  memCtx %= (setValue a MemMoved)
  return (memstate)
moveGetMem scname (TupleMove as) = do
  mems <- mapM (moveGetMem scname) as
  return (TupleMem <$> oneOfEach mems)

moveGetMem scname (RefMove te) = do
  demutationError $ "Moving of references is not implemented."
  -- if we had a reference,
  -- allocate new memory for it
  -- memvar <- lift $ allocateMem scname (Right "ref")
  -- tell [(memvar,te)]
  -- pure $ RefMem memvar



setMem :: ProcVar -> [MemType] -> MTC () 
setMem x mt = memCtx %= (setValue x (MemExists mt))

setMemMaybe :: Maybe ProcVar -> [MemType] -> MTC () 
setMemMaybe (Just x) mt = setMem x mt
setMemMaybe (Nothing) _ = pure ()


setMemTupleInManyMems :: ScopeVar -> [ProcVar] -> [MemType] -> MTC ()
setMemTupleInManyMems scname xs mems = mapM_ (setMemTuple scname xs) mems

setMemTuple :: ScopeVar -> [ProcVar] -> MemType -> MTC ()
setMemTuple scname xs (SingleMem a) = do
  -- We are deconstructing a tuple value,
  -- need to create memory locations for all parts
  let f (x) = do
        mx <- allocateMem scname (Left x)
        memCtx %= (setValue x (MemExists ([SingleMem mx])))
  mapM_ f xs

setMemTuple scname xs (RefMem a) = internalError  $ "setMemTuple not implemented for references"
  -- undefined -- do
  -- mapM_ (\(x) -> setMemMaybe x (RefMem)) xs

setMemTuple scname xs (TupleMem as) | length xs == length as = do
  let xas = zip xs as
  mapM_ (\(x, a) -> setMem x [a]) xas

setMemTuple scname xs (TupleMem as) | otherwise = demutationError $ "Trying to assign a tuple where lengths do not match:\n"
                                                                    <> show xs <> " = " <> show as

expectNotMoved :: ProcVar -> MTC [MemType]
expectNotMoved tevar = do
  mc <- use memCtx
  case getValue tevar mc of
    Nothing          -> demutationError $ "The variable " <> show tevar <> " is not assigned to anything.\n"
                                        <> "The memctx is:\n"
                                        <> show mc
    Just (MemMoved) -> throwError $ DemutationMovedVariableAccessError tevar
    Just (MemExists a) -> pure a

-- expectNotMovedMaybe :: Maybe ProcVar -> MTC (Maybe [MemType]) 
-- expectNotMovedMaybe (Just a) = Just <$> expectNotMoved a
-- expectNotMovedMaybe Nothing = undefined -- return ()


-------------------------------------
-- memory redirection
-- setMemRedirection :: MemVar -> MemType -> MTC ()
-- setMemRedirection = undefined

-------------------------------------
-- accessing memories

getAllMemVars :: MemType -> [MemVar]
getAllMemVars (SingleMem a) = [a]
getAllMemVars (TupleMem a) = a >>= getAllMemVars
getAllMemVars (RefMem a) = [a]

getAllMemVarsOfMemState :: MemState -> [MemVar]
getAllMemVarsOfMemState (MemExists ms) = ms >>= getAllMemVars
getAllMemVarsOfMemState (MemMoved) = []

expectSingleMem :: [MemType] -> MTC MemVar
expectSingleMem mts = do
  case mts of
    [mt] -> case mt of
              (SingleMem a) -> pure a
              (mem) -> demutationError $ "The memory type " <> show mem <> " was expected to contain a single memory location."
    mts -> demutationError $ "The memory type " <> show mts <> " was expected to only have one alternative."


-- reverseMemLookup :: MemVar -> MTC ProcVar
-- reverseMemLookup wantedMem = do
--   alltemems <- getAllKeyElemPairs <$> use memCtx
--   let relevantTemems = [(t,m) | (t,MemExists m) <- alltemems, wantedMem `elem` getAllMemVars m]

--   case relevantTemems of
--     [] -> demutationError $ "When doing a reverse memory lookup for memory variable " <> show wantedMem <> ", no tevar was found."
--     [(t,a)] -> case a of
--                 SingleMem a -> return t
--                 a  -> demutationError $ "When doing a reverse memory lookup for memory variable " <> show wantedMem <> ", expected it to have an individual name.\n"
--                                       <> "but it was part of a compound type: " <> show a
--     xs -> demutationError $ "When doing a reverse memory lookup for memory variable " <> show wantedMem <> ", multiple tevars were found: " <> show xs


getMemVarMutationStatus :: MemVar -> MTC [TeVar]
getMemVarMutationStatus mv = do
  mctx <- use mutCtx
  case getValue mv mctx of
    Nothing -> internalError $ "Expected memory location to have a mutation status, but it didn't. MemVar: " <> show mv
    Just (_, tvars) -> return tvars


--------------------------------------------------------------------------
-- Creating TeVars from MemVars
--
-- memTypeAsTerm :: MemType -> DemutDMTerm
-- memTypeAsTerm mt = case mt of
--   TupleMem mts -> undefined
--   SingleMem mv -> undefined
--   RefMem mv -> undefined



--
-- | Create a tevar for a procvar.
--    If procvar contains a memory location which is
--    a `SingleMem` and is mutated, use the newest variable
--    name from the `mutCtx`. Else create a tvar based on the
--    input name `mv`.
--
--    Since there are multiple memory types associated to
--    a procvar, they are dealt with as follows:
--    There are two valid possibilities:
--    1. all memory types do not contain mutated variables
--    2. all memory types are single var, and all are mutated,
--       with last tevar being the same
procVarAsTeVar :: ProcVar -> MTC TeVar
procVarAsTeVar pv = do
  mts <- expectNotMoved pv
  --
  -- all memory types which contain mutated vars
  let getMutatedName x = do
        mmut <- getMemVarMutationStatus x
        case mmut of
          []     -> return []
          (x:xs) -> return [x]
  mut_mts <- join <$> mapM getMutatedName (getAllMemVars =<< mts)
  --
  -- if we have no mutations, we are done
  case mut_mts of
    []     -> pure (UserTeVar pv)
    --
    -- if we there are mutations, we need
    -- to make sure that all tevars are the same
    (x:xs) -> case all (== x) xs of
      False -> demutationError $ "The tevars assigned to mutated " <> show pv <> " do not match in different execution branches.\n"
                                <> "This is not allowed.\n"
                                <> "Tevars: " <> show (x:xs)

      True  -> return x


moveTypeAsTerm :: MoveType -> MTC DemutDMTerm 
moveTypeAsTerm = \case
  TupleMove mts -> do
    terms <- mapM moveTypeAsTerm mts
    pure $ Tup $ terms
  SingleMove pv -> do tv <- procVarAsTeVar pv ; pure $ Var $ (tv :- JTAny)
  RefMove pdt   -> pure pdt
  NoMove pdt    -> pure pdt

movedVarsOfMoveType :: MoveType -> [ProcVar]
movedVarsOfMoveType = \case
  TupleMove mts -> mts >>= movedVarsOfMoveType 
  SingleMove pv -> return pv
  RefMove pdt -> []
  NoMove pdt -> []

termTypeAsTerm :: TermType -> MTC DemutDMTerm
termTypeAsTerm = \case
  Value it mt -> moveTypeAsTerm mt
  Statement pdt mt -> do
    mt' <- moveTypeAsTerm mt
    pure $ Extra $ DemutBlock [pdt, mt']
  StatementWithoutDefault pdt -> pure $ Extra $ DemutBlock [pdt]
  MutatingFunctionEnd         -> pure $ Extra $ DemutBlock []


