
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.Demutation.Main where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Logging
import DiffMu.Abstract.Data.Permutation
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.TopLevel
import DiffMu.Typecheck.Preprocess.Demutation.Definitions

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T
import Data.Foldable

import Debug.Trace

import qualified Prelude as P
import DiffMu.Typecheck.Preprocess.Demutation.Definitions


demutationError = throwError . DemutationError


--------------------------------------------------------------------------------------
-- Accessing the VA-Ctx in the MTC monad

{-
markMutatedBase :: IsFLetDefined -> ScopeVar -> IsLocalMutation -> TeVar -> MTC IsLocalMutation
markMutatedBase fletdef scname loc var = undefined -- do
  {-
  mutTypes %=~ (markMutatedInScope scname var)

  newvatype <- getValue var <$> use mutTypes

  -- extracting the new locality
  newloc <- case newvatype of
                Just (WriteSingleBase _ _ newloc) -> return newloc
                _ -> impossible "Expected the resulting locality after `markMutatedBase` to be a `WriteSingleBase`."

  return newloc

    -- The actual updating function
    where 
      markMutatedInScope :: ScopeVar -> TeVar -> VarAccessCtx -> MTC VarAccessCtx 
      markMutatedInScope scname var ctx =
        case getValue var ctx of
          Nothing                      -> impossible $ "When demutating (MarkMutated), the variable "
                                                       <> show var <> " was not in the VA-Ctx."
          Just oldvatype -> do
            newvatype <- computeVarAccessType var oldvatype (WriteSingleBase fletdef scname loc)
            debug $ "[markMutatedBase]: VA type for '" <> show var <> "' changes from " <> show oldvatype <> " to " <> show newvatype
            return (setValue var newvatype ctx)
-}

markMutatedFLet :: ScopeVar -> IsLocalMutation -> TeVar -> MTC IsLocalMutation
markMutatedFLet scname loc var = do
  log $ "Marking flet mutated for " <> show var
  markMutatedBase FLetDefined scname loc var

--
-- Apply a mutation of `loc` locality to the `var`.
-- This might or might not change `loc`, depending on whether this variable
-- is already local or not-local.
-- The resulting locality is returned.
--
markMutated :: ScopeVar -> IsLocalMutation -> TeVar -> MTC IsLocalMutation
markMutated scname loc var = do
  log $ "Marking simple mutated for " <> show var
  markMutatedBase NotFLetDefined scname loc var


markRead :: ScopeVar -> MemVar -> MTC ()
markRead scname var = undefined -- mutTypes %=~ (markReadInScope scname var)
{-
    where 
      markReadInScope :: ScopeVar -> TeVar -> VarAccessCtx -> MTC VarAccessCtx 
      markReadInScope scname var ctx =
        case getValue var ctx of
          Nothing                      -> pure (setValue var (ReadSingle scname) ctx)
          Just oldvatype -> do
            newvatype <- computeVarAccessType var oldvatype (ReadSingle scname)
            return (setValue var newvatype ctx)
-}

-- markReadMaybe :: ScopeVar -> Maybe TeVar -> MTC ()
-- markReadMaybe scname (Just x) = markRead scname x
-- markReadMaybe scname Nothing = pure ()

-- markReadOverwritePrevious :: ScopeVar -> TeVar -> MTC ()
-- markReadOverwritePrevious scname var = mutTypes %%= (\scope -> ((), setValue var (ReadSingle scname) scope))
-}

applyTeVarAccess :: ScopeVar -> VarAccessType -> TeVar -> MTC ()
applyTeVarAccess scname va1 var = vactx %=~ (applyMemVarAccessPure scname var va1)
  where
    applyMemVarAccessPure :: ScopeVar -> TeVar -> VarAccessType -> VarAccessCtx -> MTC VarAccessCtx
    applyMemVarAccessPure scname1 var va1 ctx = case getValue var ctx of

      -- the first access is always a "read"
      Nothing -> return $ setValue var (ReadSingle,scname1) ctx

      -- all others are as passed
      Just (va0,scname0) -> do
        va2 <- computeVarAccessType var ((va0, scname0)) ((va1, scname1))
        return $ setValue var (va2,scname0) ctx

applyTeVarAccessMaybe :: ScopeVar -> VarAccessType -> Maybe TeVar -> MTC ()
applyTeVarAccessMaybe scname va1 (Just var) = applyTeVarAccess scname va1 var
applyTeVarAccessMaybe scname va1 Nothing    = pure ()

overwriteTeVarAccess :: ScopeVar -> VarAccessType -> TeVar -> MTC ()
overwriteTeVarAccess scname var va1 = vactx %=~ (applyMemVarAccessPure scname va1 var)
  where
    applyMemVarAccessPure :: ScopeVar -> TeVar -> VarAccessType -> VarAccessCtx -> MTC VarAccessCtx
    applyMemVarAccessPure scname1 var va1 ctx = return $ setValue var (va1,scname1) ctx


applyMemVarAccess :: ScopeVar -> MemVar -> IsMutated -> (MemType -> MTC MemType)-> MTC ()
applyMemVarAccess scname var mat memtypefun = memctx %=~ (applyMemVarAccessPure scname var mat)
  where
    applyMemVarAccessPure :: ScopeVar -> MemVar -> IsMutated -> MemCtx -> MTC MemCtx
    applyMemVarAccessPure scname1 var mut1 ctx = case getValue var ctx of
      Nothing -> demutationError $ "Expected the memory variable " <> show var <> "to be allocated, but it is not."
      Just (mt0,mut0,scname0) -> do
        -- mat2 <- computeVarAccessType var ((mat0, scname0)) ((mat1, scname1))
        let mut2 = mut0 <> mut1
        mt2 <- memtypefun mt0
        return $ setValue var (mt2,mut2,scname0) ctx


readMemVar :: ScopeVar -> MemVar -> MTC MemType
readMemVar scname var = do
  applyMemVarAccess scname var (NotMutated) pure
  mval <- getValue var <$> use memctx
  case mval of
    Nothing -> impossible $ "Non existing variable when reading memvar " <> show var
    Just (a,b,c) -> return a

readTeVar :: Scope -> ScopeVar -> TeVar -> MTC MemVar
readTeVar scope scname var = case getValue var scope of
  Nothing -> demutationError $ ""
  Just mv -> do
    applyTeVarAccess scname ReadSingle var
    return mv

writeMemVar :: ScopeVar -> MemVar -> MemType -> MTC ()
writeMemVar scname memvar mt = do
  applyMemVarAccess scname memvar (Mutated) (\_ -> pure mt)

-- writeTeVar :: ScopeVar -> TeVar -> MemVar -> MTC ()
-- writeTeVar = undefined

--
-- This creates a new MemVar, writes it into the MemCtx
--
createMemoryLocation :: Text -> ScopeVar -> MemType -> MTC MemVar
createMemoryLocation name_hint scname mt = do
  memvar <- newMemVar $ (T.pack $ show scname) <> "_" <> name_hint
  memctx %%= (\ctx -> ((), setValue memvar (mt,NotMutated,scname) ctx))
  return memvar

cleanupMemoryLocations :: ScopeVar -> MTC ()
cleanupMemoryLocations scname = memctx %%= (\ctx -> ((), f ctx))
  where
    f = fromKeyElemPairs . filter (\(_,(_,_,scname2)) -> scname2 /= scname) . getAllKeyElemPairs


--
-- This gets a memory type, and writes the value
-- to the memory location behind the TeVar.
-- If such a memory location does not exist, we create a new one.
-- If the memory location does exist, we make sure that we
-- are allowed to write into it from our current scope.
--
assignTeVar :: ScopeVar -> TeVar -> MemType -> Scope -> MTC Scope
assignTeVar scname tevar mt scope = do
  applyTeVarAccess scname WriteSingle tevar
  memvar <- createMemoryLocation (T.pack $ show tevar) scname mt
  return (setValue tevar memvar scope)
  -- get or create the memory location for `var`.
  -- case getValue tevar scope of
  --   Nothing   -> do
  --                 memvar <- createMemoryLocation (T.pack $ show tevar) scname mt
  --                 return (setValue tevar memvar scope)
  --   Just mvar -> do
      -- This currently does not quite follow the semantics, probably.
      -- Our vatypes are associated to memory locations.
      -- Thus we apply a write access to the previous memory
      -- location of tevar.
      -- But since every assignment creates a new memory location,
      -- we also create a new 
      -- writeMemVar scname mvar mt >> return scope

assignTeVarRValue :: ScopeVar -> TeVar -> RValue -> Scope -> MTC Scope
assignTeVarRValue scname tevar (RMem memvar) scope = do
  applyTeVarAccess scname WriteSingle tevar
  return (setValue tevar memvar scope)
assignTeVarRValue scname tevar (RAnonymous mt) scope = assignTeVar scname tevar mt scope

--
-- We need this one, because marking flet defined functions as `write` works
-- differently than for other values. (Because flets are reordered)
-- (https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/148#issuecomment-1004404681)
--
assignTeVarRValueFunction :: ScopeVar -> TeVar -> RValue -> Scope -> MTC Scope
assignTeVarRValueFunction scname tevar (RMem memvar) scope = do
  applyTeVarAccess scname WriteSingleFunction tevar
  return (setValue tevar memvar scope)
assignTeVarRValueFunction scname tevar (RAnonymous mt) scope = do
  applyTeVarAccess scname WriteSingleFunction tevar
  memvar <- createMemoryLocation (T.pack $ show tevar) scname mt
  return (setValue tevar memvar scope)

assignTeVarRValueMaybe :: ScopeVar -> Maybe TeVar -> RValue -> Scope -> MTC Scope
assignTeVarRValueMaybe scname (Just tevar) rv scope = assignTeVarRValue scname tevar rv scope
assignTeVarRValueMaybe scname Nothing rv scope = pure scope


assignTeVarRValuesMaybe :: ScopeVar -> [(Maybe TeVar, RValue)] -> Scope -> MTC Scope
assignTeVarRValuesMaybe scname tervars scope = foldrM (\(tev, memv) s -> assignTeVarRValueMaybe scname tev memv s) scope tervars


-- assignTeVarRValueFromImmutType :: ScopeVar -> TeVar -> ImmutType -> Scope -> MTC Scope
-- assignTeVarRValueFromImmutType scname tevar (Pure (UserValue uv)) scope  = assignTeVarRValue scname tevar uv scope
-- assignTeVarRValueFromImmutType scname tevar it@(Pure DefaultValue) scope = internalError $ "Expected a pure type, but got " <> show it
-- assignTeVarRValueFromImmutType scname tevar it@(VirtualMutated _) scope  = internalError $ "Expected a pure type, but got " <> show it
  
overwriteTeVar :: ScopeVar -> TeVar -> MemType -> Scope -> MTC Scope
overwriteTeVar scname tevar mt scope = do
  memvar <- createMemoryLocation (T.pack $ show tevar) scname mt
  return (setValue tevar memvar scope)

overwriteTeVarMaybe :: ScopeVar -> Maybe TeVar -> MemType -> Scope -> MTC Scope
overwriteTeVarMaybe scname (Just tevar) mt scope = overwriteTeVar scname tevar mt scope
overwriteTeVarMaybe scname Nothing mt scope = pure scope



metaExpectScopeValue :: TeVar -> Scope -> MTC MemVar
metaExpectScopeValue var scope = 
  case getValue var scope of
        Nothing -> impossible $ "Expected the scope " <> show scope <> " to contain variable " <> show var
        Just mv -> return mv
  

metaExpectMemCtxValue :: MemVar -> MTC (MemType,IsMutated,ScopeVar)
metaExpectMemCtxValue mv = do
  mc <- use memctx
  let mt = getValue mv mc
  case mt of
    Nothing -> impossible $ "Expected MemCtx " <> show mc <> " to contain memory location " <> show mv
    Just x0 -> return x0

metaExpectRValue :: ImmutType -> MTC RValue
metaExpectRValue (Pure (UserValue rv))  = return rv
metaExpectRValue it@(Pure DefaultValue) = internalError $ "Expected a pure type, but got " <> show it
metaExpectRValue it@(VirtualMutated _)  = internalError $ "Expected a pure type, but got " <> show it

reverseScopeLookup :: Scope -> MemVar -> MTC TeVar
reverseScopeLookup scope target = do
  let mc = getAllKeyElemPairs scope
  let tevars = [tev | (tev, memv) <- mc , memv == target]

  case tevars of
    [] -> demutationError $ "When doing reverse scope lookup, expected the memvar " <> show target <> " to have a scope entry."
    (x:_) -> return x


--
-- Create memory locations and RValues for tuple entries, if there are none.
--

--
-- All variables get a memory location,
-- including the anonymous
--
createTupleRValues :: ScopeVar -> [Maybe TeVar] -> RValue -> MTC [RValue]
-- an anonymous value
createTupleRValues scname tenames (RAnonymous MemAny) = do
  (warn "Ensuring that an anonymous value is a tuple.")
  demutationError "tuple rvalues from anonymous rvalues not implemented"

-- a value behind a single var
createTupleRValues scname tenames (RMem var) = do

  -- lookup the content of this var
  varty <- readMemVar scname var

  case varty of
    MemTup mvs -> case length mvs == length tenames of
                    True  -> return mvs
                    False -> demutationError $ "Wrong number of tuple entries."
    MemAny -> do
      -- create new memory locations for the tuple elements
      mvars <- mapM (newMemVar) (T.pack <$> show <$> tenames)

      -- write them for the tuple variable
      -- writeMemVar scname var (MemTup mvars)
      mvars <- mapM (\name -> createMemoryLocation name scname MemAny) (T.pack <$> show <$> tenames)

      return (RMem <$> mvars)

    MemPureFun -> demutationError $ "Expected a tuple, but got a function."
    MemMutatingFun ims -> demutationError $ "Expected a tuple, but got a function."
    MemPureBlackBox -> demutationError $ "Expected a tuple, but got a pure black box."

createTupleRValues scname tenames (RAnonymous (MemTup vars)) = case length vars == length tenames of
                                                          True  -> return vars
                                                          False -> demutationError $ "Wrong number of tuple entries."
createTupleRValues scname tenames (RAnonymous MemPureBlackBox) = demutationError $ "Expected a tuple, but got a pure black box."
createTupleRValues scname tenames (RAnonymous (MemPureFun)) = demutationError $ "Expected a tuple, but got a function."
createTupleRValues scname tenames (RAnonymous (MemMutatingFun _)) = demutationError $ "Expected a tuple, but got a function."

--------------------------------------------------------------------------------------


wrapReorder :: (Eq a, Show a) => [a] -> [a] -> PreDMTerm t -> PreDMTerm t
wrapReorder have want term | have == want = term
wrapReorder have want term | otherwise    =
  let σ = getPermutationWithDrop have want
  in Reorder σ (term)

immutTypeEq :: ImmutType -> ImmutType -> Bool
immutTypeEq (Pure _) (Pure _) = True
-- immutTypeEq (Mutating a) (Mutating b) = a == b
immutTypeEq (VirtualMutated a) (VirtualMutated b) = a == b
immutTypeEq _ _ = False

-- set the type of the variable in scope,
-- but do not allow to change that value afterwards.
{-
safeSetValueBase :: IsFLetDefined -> ScopeVar -> Maybe TeVar -> MemVar -> Scope -> MTC Scope
safeSetValueBase fletdef scname (Nothing) newType scope = pure scope
safeSetValueBase fletdef scname (Just var) newType scope = undefined
{-
  case getValue var scope of
    Nothing -> do
      debug $ "[safeSetValue]: Var " <> show var <> " not in scope " <> show scname <> ". Marking read."
      -- debug $ "[safeSetValue]: (for the record, locality would be " <> show loc <> ")"
      markRead scname var
      return (setValue var newType scope)
    (Just oldType) -> do
      debug $ "[safeSetValue]: Var " <> show var <> " is already in scope " <> show scname <> ". Marking as mutated."
      -- debug $ "[safeSetValue]: (locality: " <> show loc <> ")"
      markMutatedBase fletdef scname loc var -- We say that we are changing this variable. This can throw an error.
      if immutTypeEq oldType newType
                      then pure scope
                      else throwError (DemutationError $ "Found a redefinition of the variable '" <> show var <> "', where the old type (" <> show oldType <> ") and the new type (" <> show newType <> ") differ. This is not allowed.")
-}

safeSetValue :: ScopeVar -> Maybe TeVar -> MemVar -> Scope -> MTC Scope
safeSetValue = safeSetValueBase NotFLetDefined

safeSetValueAllowFLet :: ScopeVar -> Maybe TeVar -> MemVar -> Scope -> MTC Scope
safeSetValueAllowFLet = safeSetValueBase FLetDefined

safeSetNewValue :: ScopeVar -> Maybe TeVar -> MemType -> Scope -> MTC Scope
safeSetNewValue = undefined
-}

{-
safeSetValueAllowFLet :: Maybe TeVar -> ImmutType -> Scope -> MTC Scope
safeSetValueAllowFLet (Nothing) newType scope = pure scope
safeSetValueAllowFLet (Just var) newType scope =
  case getValue var scope of
    Nothing -> pure $ setValue var newType scope
    (Just oldType) -> if immutTypeEq oldType newType
                      then pure scope
                      else throwError (DemutationError $ "Found a redefinition of the variable '" <> show var <> "', where the old type (" <> show oldType <> ") and the new type (" <> show newType <> ") differ. This is not allowed.")
-}


---
-- elaborating loops
-- not allowed:
-- - FLet
-- - JuliaReturn
-- - modify iteration variable

demutate :: MutDMTerm -> MTC (DMTerm)
demutate term = do
  logForce $ "Term before mutation elaboration:\n" <> showPretty term

  topscname <- newScopeVar "toplevel"

  (res , _) <- elaborateMut topscname def term
  logForce $ "-----------------------------------"
  logForce $ "Mutation elaborated term is:\n" <> showPretty res

  let optimized = optimizeTLet res
  logForce $ "-----------------------------------"
  logForce $ "TLet optimized term is:\n" <> showPretty optimized

  return optimized


elaborateNonmut :: ScopeVar -> Scope -> MutDMTerm -> MTC (DMTerm , ImmutType)
elaborateNonmut scname scope term = do
  (resTerm , resType) <- elaborateMut scname scope term

  -- get the context and make sure that all variables are not mutated
  -- Ctx (MonCom ctx) <- use mutTypes
  -- let ctxElems = H.toList ctx
  -- let somethingMutated = [a | (a , m) <- ctxElems, m == Mutated]

  -- case somethingMutated of
  --   [] -> pure ()
  --   xs -> throwError (DemutationError $ "expected that the term " <> show term <> " does not mutate anything, but it mutates the following variables: " <> show xs)

  -- make sure that the result is not a mutation result

  case resType of
    Pure _ -> pure ()
    VirtualMutated mutvars -> throwError (DemutationError $ "expected that the term " <> showPretty term <> " does not mutate anything, but it mutates the following variables: " <> show mutvars)
    -- Mutating _ -> pure ()
    -- PureBlackBox -> pure ()

  return (resTerm , resType)

elaborateMut :: ScopeVar -> Scope -> MutDMTerm -> MTC (DMTerm , ImmutType)

elaborateMut scname scope (Op op args) = do
  args' <- mapM (elaborateNonmut scname scope) args
  pure (Op op (fst <$> args') , Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (Sng η τ) = pure (Sng η τ , Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (Rnd jt) = pure (Rnd jt , Pure (UserValue (RAnonymous MemAny)))

elaborateMut scname scope (Var (x :- j)) = do
  applyTeVarAccessMaybe scname ReadSingle x
  let mx = getValueMaybe x scope
  case mx of
    Nothing -> logForce ("checking Var term, scope: " <> show scope) >> throwError (DemutationDefinitionOrderError x)
    Just mx  -> do
      tx <- readMemVar scname mx
      return (Var (x :- j), Pure (UserValue (RMem mx)))

elaborateMut scname scope (BBLet name args tail) = do

  -- write the black box into the scope with its type
  scope'  <- assignTeVar scname name MemPureBlackBox scope

  -- typecheck the body in this new scope
  (newBody , newBodyType) <- elaborateMut scname scope' tail

  return (BBLet name args newBody , consumeDefaultValue newBodyType)


elaborateMut scname scope (SLetBase ltype (x :- τ) term body) = do

  (newTerm , newTermType) <- elaborateMut scname scope term

  ty <- case newTermType of
    Pure (UserValue ty) -> pure ty
    Pure (DefaultValue) -> throwError $ DemutationError $ "Found an assignment " <> show x <> " = " <> showPretty term <> " where RHS is a default value. This is not allowed."
    VirtualMutated _    -> throwError (DemutationError $ "Found an assignment " <> show x <> " = " <> showPretty term <> " where RHS is a mutating call. This is not allowed.")
    -- PureBlackBox     -> throwError (DemutationError $ "Found an assignment " <> show x <> " = " <> showPretty term <> " where RHS is a black box. This is not allowed.")

  debug $ "[elaborateMut/SLetBase]: The variable " <> show x <> " is being assigned." 
  --
  -- If ty is a SingleMem RHS value, then it already points to
  -- a memory location, and we take the contents from there.
  -- This should be consistent with the fact that assignments are shallow copies.
  -- (See #158, https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/158#issuecomment-1009041515)
  --
  scope' <- assignTeVarRValueMaybe scname x ty scope

  (newBody , newBodyType) <- elaborateMut scname scope' body

  return (SLetBase ltype (x :- τ) newTerm newBody , consumeDefaultValue newBodyType)


elaborateMut scname scope (TLetBase ltype vars term body) = do
  let tevars = [v | v :- _ <- vars]

  -- elaborate the term
  (newTerm , newTermType) <- elaborateMut scname scope term

  ty <- case newTermType of
    Pure (UserValue ty) -> pure ty
    Pure (DefaultValue) -> throwError (DemutationError $ "Found an assignment " <> show vars <> " = " <> showPretty term <> " where RHS is a default value. This is not allowed.")
    VirtualMutated _    -> throwError (DemutationError $ "Found an assignment " <> show vars <> " = " <> showPretty term <> " where RHS is a mutating call. This is not allowed.")

  -- get memvars for tevars
  rvalues <- createTupleRValues scname [v | (v :- _) <- vars] ty

  -- assign the created rvalues to the variables
  scope' <- assignTeVarRValuesMaybe scname (zip tevars rvalues) scope

  (newBody , newBodyType) <- elaborateMut scname scope' body

  return (TLetBase ltype vars newTerm newBody , consumeDefaultValue newBodyType)

elaborateMut scname scope (LamStar args body) = do
  bodyscname <- newScopeVar "lamstar"
  (newBody, newBodyType) <- elaborateLambda bodyscname scope [(v :- x) | (v :- (x , _)) <- args] body
  return (LamStar args newBody, newBodyType)


elaborateMut scname scope (Lam args body) = do
  bodyscname <- newScopeVar "lam"
  (newBody, newBodyType) <- elaborateLambda bodyscname scope args body
  return (Lam args newBody, newBodyType)

elaborateMut scname scope (Apply f args) = do

  -- typecheck the function f
  (newF , τ) <- elaborateNonmut scname scope f

  --------
  -- 2 cases
  --
  -- case I : A (possibly mutating) function call
  --
  let applyMutating muts retType = do
        -- make sure that there are as many arguments as the function requires
        case length muts == length args of
          True -> pure ()
          False -> throwError (DemutationError $ "Trying to call the function '" <> showPretty f <> "' with a wrong number of arguments.")

        let mutargs = zip muts args
        (newArgs , muts) <- elaborateMutList (showPretty f) scname scope mutargs

        -- the new term
        return (Apply newF newArgs , retType muts)
  --
  -- case II: A call to a pure black box
  --
  let applyPureBlackBox = do
        -- the global variables which are implicitly applied
        -- and need to be added to the `BBApply`
        glvars <- globalNames <$> (use topLevelInfo)

        -- since the box is pure, we say so to `elaborateMutList`
        let mutargs = [(NotMutated,a) | a <- args]
        (newArgs , muts) <- elaborateMutList (showPretty f) scname scope mutargs

        return (BBApply newF newArgs glvars , Pure (UserValue (RAnonymous MemAny)))
  --
  -- END cases
  --------

  --------
  -- Dispatching which type of function call we have
  --
  -- get the type of `f`. if it is not a mutating function,
  -- we give it a type where all arguments are not mutated,
  -- also set the return type.
  --
  ptau <- case τ of
    Pure ptau -> return ptau
    VirtualMutated _ -> throwError (DemutationError $ "Trying to call the result of a mutating call " <> showPretty f <> ". This is not allowed.")

  -------------------------------------
  --
  -- TODO / WARNING
  --
  -- In the cases of non-mutating functions we assume that the return type of the function
  -- is (\_ -> Pure (UserValue (RAnonymous MemAny))). That is, that it is independent of 
  -- the inputs.
  -- This is simply not always correct. See #158.
  --
  ---------
  --
  -- Get MemType, if not direct, then look up in mem
  --
  mt <- case ptau of
    UserValue (RAnonymous mt) -> return mt
    UserValue (RMem mv)       -> do
      (mt,_,_) <- metaExpectMemCtxValue mv
      return mt
    DefaultValue -> demutationError $ "Trying to call a default value."


  case mt of
    (MemPureBlackBox)     -> applyPureBlackBox
    (MemPureFun)          -> applyMutating (take (length args) (repeat NotMutated)) (\_ -> Pure (UserValue (RAnonymous MemAny)))
    (MemMutatingFun muts) -> applyMutating muts VirtualMutated
    (MemTup muts)         -> demutationError $ ""
    (MemAny)              -> do
      warn $ "Assuming that " <> showPretty f <> " is a pure function call."
      applyMutating (take (length args) (repeat NotMutated)) (\_ -> Pure (UserValue (RAnonymous MemAny)))

        -- Pure _           -> applyMutating (take (length args) (repeat NotMutated)) (\_ -> Pure (UserValue (RAnonymous MemAny)))
        -- Mutating muts    -> applyMutating muts VirtualMutated
        -- PureBlackBox     -> applyPureBlackBox
        -- VirtualMutated _ -> throwError (DemutationError $ "Trying to call the result of a mutating call " <> showPretty f <> ". This is not allowed.")



elaborateMut scname scope (FLet fname term body) = do

  -- check the term
  (newTerm, newTermType) <- elaborateNonmut scname scope term

  -- Make sure that `newTermType` is proper
  newTermTypeProper <-case newTermType of
    Pure (UserValue u)  -> return u
    Pure (DefaultValue) -> demutationError $ "A function definition cannot be a default value."
    VirtualMutated x0   -> demutationError $ "A function definition cannot be a virtual mutated."


  -- get the current type for fname from the scope
  let fvar = getValue fname scope
  ftype <- mapM metaExpectMemCtxValue fvar

  -- set the new scope with fname if not already existing
  -- (but only allow pure uservalue-functions, or single-definition mutating functions)
  scope' <- case (\(a,_,_) -> a) <$> ftype of
        Nothing                   -> assignTeVarRValueFunction scname fname newTermTypeProper scope

        Just (MemPureFun)         -> assignTeVarRValueFunction scname fname newTermTypeProper scope
        Just (MemMutatingFun _)   -> throwError (DemutationError $ "We do not allow mutating functions to have multiple definitions")

        Just _ -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"

        -- Nothing                   -> safeSetValueAllowFLet scname (Just fname) newTermType scope

        -- Just (Pure (UserValue _)) -> safeSetValueAllowFLet scname (Just fname) newTermType scope
        -- Just (Pure (UserValue _)) -> throwError (DemutationError $ "We do not allow mutating functions to have multiple definitions")

        -- Just (Pure DefaultValue) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        -- Just (Pure (SingleArg _)) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        -- Just (VirtualMutated _) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        -- Just (PureBlackBox) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"

  -- check the body with this new scope

  (newBody, newBodyType) <- elaborateMut scname scope' body

  return (FLet fname newTerm newBody, consumeDefaultValue newBodyType)


elaborateMut scname scope (Extra (MutLet ltype term1 term2)) = do

  -- elaborate the first term and get its mutated variables
  (newTerm1, newTerm1Type) <- elaborateMut scname scope term1

  --
  -- Change the scope if the first term was virtually mutating,
  -- 
  case newTerm1Type of
        Pure pt -> do
          warn $ "Found a pure term in a place where it does not have any effects.\n"
                     <> "The full term is:\n"
                     <> "# ---------------------------\n"
                     <> "# type: " <> show (Pure pt) <> "\n"
                     <> showPretty term1 <> "\n"
                     <> "# ------------\n"
                     <> "# rest:\n"
                     <> showPretty term2 <> "\n"
                     <> "\n"
                     <> "It (the first, pure part) is thus ignored in the privacy analysis."
          elaborateMut scname scope term2
        VirtualMutated newScope -> do
          let scope' = fromKeyElemPairs newScope
          (newTerm2, newTerm2Type) <- elaborateMut scname scope' term2
          let ns1 = [Just n :- JTAny | (n, _) <- newScope]
          return (TLetBase ltype ns1 newTerm1 newTerm2, newTerm2Type)


elaborateMut scname scope (Extra (MutLoop iters iterVar body)) = internalError $ "Loop demutation not supported"
 -- do
  {-
  -- first, elaborate the iters
  (newIters , newItersType) <- elaborateNonmut scname scope iters

  -- now, preprocess the body,
  -- i.e., find out which variables are getting mutated
  -- and change their `SLet`s to `modify!` terms
  (preprocessedBody, modifyVars) <- runPreprocessLoopBody scope iterVar body

  logForce $ "Preprocessed loop body. The modified vars are: " <> show modifyVars
        <> "\nThe body is:\n" <> showPretty preprocessedBody

  -- we add these variables to the scope as args, since they are allowed
  -- to occur in mutated positions
  -- let scope0 = foldr (\v s -> setValue v (Pure) s) scope modifyVars
  scope' <- safeSetValue scname LocalMutation iterVar (Pure (UserValue (RAnonymous MemAny))) scope

  --
  -- [VAR FILTERING/Begin]
  --
  vanames <- getAllKeys <$> use mutTypes
  --

  -- we can now elaborate the body, and thus get the actual list
  -- of modified variables
  (newBody, newBodyType) <- elaborateMut scname scope' preprocessedBody

  --
  -- [VAR FILTERING/End]
  --
  -- After the body was elaborated, it might be that we have new
  -- variables in scope which are only local in the body
  -- What we do is we filter the VA(Ctx) to only contain the vars
  -- which were in it before the body was checked
  --
  let deleteIfNotOld k ctx = case k `elem` vanames of
                              True  -> ctx
                              False -> deleteValue k ctx
  mutTypes %= (\ctx -> foldr (\k ctx -> deleteIfNotOld k ctx) ctx (getAllKeys ctx))
  --

  -- we accept a full virtual mutated, or a globally pure value
  case newBodyType of
    ----------
    -- case I
    -- the loop is really mutating
    VirtualMutated mutvars -> do

      -- we use the mutvars to build a tlet around the body,
      -- and return that new `Loop` term
      --
      -- the actual body term is going to look as follows:
      --
      --   let (c1...cn) = captureVar
      --   in term...
      --
      -- where `term` is made sure to return the captured tuple
      -- by the general demutation machinery
      captureVar <- newTeVarOfMut "loop_capture"

      let inScope v = case getValue v scope of
                        Just _ -> True
                        Nothing -> False

      let globalMutVars = filter (inScope . fst) mutvars

      let newBodyWithLet = TLet [(Just v :- JTAny) | (v,_) <- globalMutVars] (Var (Just captureVar :- JTAny)) (wrapReorder mutvars globalMutVars newBody)
      let newTerm = Loop newIters (fst <$> globalMutVars) (iterVar , captureVar) newBodyWithLet

      return (newTerm , VirtualMutated globalMutVars)

    ----------
    -- case I
    -- the loop only mutates local variables,
    -- and returns a pure value
    Pure p -> throwError (DemutationError $ "Expected a loop body to be mutating, but it was of type " <> show (Pure p))
    --   -> case xs of
    -- GloballyPure xs -> case xs of
      -- [] -> throwError (DemutationError $ "Expected a loop body to be mutating, but it was of type " <> show (Pure))
      -- mutvars -> do
      --   captureVar <- newTeVarOfMut "loop_capture"

      --   let inScope v = case getValue v scope of
      --                     Just _ -> True
      --                     Nothing -> False

      --   let globalMutVars = filter (inScope) mutvars
      --   let bodyProjection = getPermutationWithDrop mutvars globalMutVars

      --   let newBodyWithLet = TLet [(v :- JTAny) | (v) <- globalMutVars] (Var (captureVar :- JTAny)) (newBody)
      --   let newTerm = Loop newIters (globalMutVars) (iterVar , captureVar) newBodyWithLet

      --   return (newTerm , VirtualMutated ([(v , LocalMutation) | v <- globalMutVars]))


    -- if there was no mutation, throw error
    other -> throwError (DemutationError $ "Expected a loop body to be mutating, but it was of type " <> show other)
-}

-- the loop-body-preprocessing creates these modify! terms
-- they get elaborated into tlet assignments again.
elaborateMut scname scope (Extra (SModify (Nothing :- _) t1)) = throwError (DemutationError $ "Found a nameless variable in a modify term.")
elaborateMut scname scope (Extra (SModify (Just v :- _) t1)) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  newT1Type' <- metaExpectRValue newT1Type
  scope' <- assignTeVarRValue scname v newT1Type' scope
  return (Tup [newT1], VirtualMutated (getAllKeyElemPairs scope'))

  -- (argTerms, mutVars) <- elaborateMutList "internal_modify" scope [(Mutated , (Var v)) , (NotMutated , t1)]
  -- case argTerms of
  --   [Var (v :- jt), newT2] -> pure (Tup [newT2] , VirtualMutated mutVars)
  --   [_, newT2] -> internalError ("After elaboration of an internal_modify term result was not a variable.")
  --   _ -> internalError ("Wrong number of terms after elaborateMutList")

-- We also have tuple modify
elaborateMut scname scope (Extra (TModify xs t1)) = do
  let vars = [v | (v :- _) <- xs]
  let elabSingle (Just v :- _) = return (v, LocalMutation)
      elabSingle (Nothing :- _) = throwError (DemutationError $ "Found a nameless variable in a tuple modify term.")

  (newT1, newT1Type) <- elaborateNonmut scname scope t1

  newT1Type' <- metaExpectRValue newT1Type
  tupvals <- createTupleRValues scname vars newT1Type'
  scope' <- assignTeVarRValuesMaybe scname (zip vars tupvals) scope

  return (newT1 , VirtualMutated (getAllKeyElemPairs scope'))



elaborateMut scname scope (Extra (MutRet)) = do
  -- get all variables from the scope, whose
  -- memvars are mutated
  mc <- use memctx

  let ismutated :: MemVar -> Bool
      ismutated mv = case getValue mv mc of
        Nothing                        -> False
        Just (_, Mutated, _) -> True
        Just (_, _, _)                 -> False

  -- mutated vars with their locality
  let mvars = [v | (v, mvar) <- getAllKeyElemPairs scope, ismutated mvar ]

  -- return all these vars
  return (Tup [Var (Just v :- JTAny) | v <- mvars ] , VirtualMutated (getAllKeyElemPairs scope))

elaborateMut scname scope (LastTerm t) = do
  (newTerm, newType) <- elaborateMut scname scope t
  return (LastTerm (newTerm), newType)

elaborateMut scname scope (Extra (DefaultRet x)) = do
  (newX,newXType) <- elaborateNonmut scname scope x
  case newXType of
    -- if the term is pure, then we annotate
    -- it to say that it is default
    Pure a -> return (newX , Pure DefaultValue)

    -- if it is not pure, it makes not sense
    -- to say that it is default: we keep the actual type
    t -> return (newX , t)

elaborateMut scname scope term@(Phi cond t1 t2) = internalError "demutation of phi terms currently not supported"
  {-
  do
  -- elaborate all subterms
  (newCond , newCondType) <- elaborateNonmut scname scope cond
  (newT1 , newT1Type) <- elaborateMut scname scope t1
  (newT2 , newT2Type) <- elaborateMut scname scope t2

  ----
  -- mutated if case
  let buildMutatedPhi :: [(TeVar, IsLocalMutation)] -> [(TeVar,IsLocalMutation)] -> MTC (DMTerm , ImmutType)
      buildMutatedPhi m1 m2 = do
        let globalM1 = [v | (v , NotLocalMutation) <- m1]
        let globalM2 = [v | (v , NotLocalMutation) <- m2]

        -- the common mutated vars are
        let mutvars = nub (globalM1 <> globalM2)

        -- build local tlets which unify the mutated variables of both branches
        -- if term1/term2 do not mutate anything, their branch becomes empty
        unifiedT1 <- case globalM1 of
          [] -> do warn ("Found the term " <> showPretty t1
                         <> " which does not mutate any function arguments in the first branch of a mutating if expression.\n"
                         <> " => In the term:\n" <> parenIndent (showPretty term) <> "\n"
                         <> " => Conclusion: This computated value is not allowed to be used in the computation, \nand accordingly, it is ignored in the privacy analysis.")
                   pure $ (Tup [Var (Just v :- JTAny) | (v) <- mutvars])
          _ ->     pure $ TLet [(Just v :- JTAny) | (v, _) <- m1] newT1 (Tup [Var (Just v :- JTAny) | (v) <- mutvars])

        unifiedT2 <- case globalM2 of
          [] -> do warn ("Found the term " <> showPretty t2
                         <> " which does not mutate any function arguments in the second branch of a mutating if expression.\n"
                         <> " => In the term:\n" <> parenIndent (showPretty term) <> "\n"
                         <> " => Conclusion: This computated value is not allowed to be used in the computation, \nand accordingly, it is ignored in the privacy analysis.")
                   pure $ (Tup [Var (Just v :- JTAny) | (v) <- mutvars])
          _ ->     pure $ TLet [(Just v :- JTAny) | (v, _) <- m2] newT2 (Tup [Var (Just v :- JTAny) | (v) <- mutvars])

        return (Phi newCond unifiedT1 unifiedT2 , VirtualMutated ([(v , NotLocalMutation) | v <- mutvars]))

  -- mutated if case end
  ----

  -- depending on the types of the branches,
  -- do the following
  case (newT1Type, newT2Type) of
    -- We do not allow either of the branches to
    -- define a mutating function. This would require
    -- us to "unify" the types of those functions
    (τ1@(Mutating _), _) -> throwError (DemutationError $ "In the term\n" <> showPretty term <> "\nthe first branch is a mutating function of type " <> show τ1 <> ". This is currently not allowed.")
    (_, τ1@(Mutating _)) -> throwError (DemutationError $ "In the term\n" <> showPretty term <> "\nthe second branch is a mutating function of type " <> show τ1 <> ". This is currently not allowed.")


    -- if either of the cases is mutating,
    -- we assume that the if expression is meant to be mutating,
    -- and require to ignore the (possibly) computed and returned value
    (VirtualMutated m1, VirtualMutated m2) -> buildMutatedPhi m1 m2
    -- (VirtualMutated m1, GloballyPure p2) -> buildMutatedPhi m1 [(v,LocalMutation) | v <- p2]
    (VirtualMutated m1, Pure _) -> buildMutatedPhi m1 []
    -- (GloballyPure p1, VirtualMutated m2) -> buildMutatedPhi [(v,LocalMutation) | v <- p1] m2
    (Pure _, VirtualMutated m2) -> buildMutatedPhi [] m2

    -- if both branches are not mutating, ie. var or pure, then we have a pure
    -- if statement. The result term is the elaborated phi expression
    -- (GloballyPure p1, GloballyPure p2) -> return (Phi newCond newT1 newT2 , GloballyPure (nub (p1 <> p2)))
    -- (GloballyPure p1, SingleArg _) -> return (Phi newCond newT1 newT2 , GloballyPure p1)
    -- (SingleArg _, GloballyPure p2) -> return (Phi newCond newT1 newT2 , GloballyPure p2)
    (_, _) -> return (Phi newCond newT1 newT2 , Pure (UserValue (RAnonymous MemAny)))
-}

----
-- the mutating builtin cases

elaborateMut scname scope (SubGrad t1 t2) = do
  (argTerms, mutVars) <- elaborateMutList "subgrad" scname scope [(Mutated , t1), (NotMutated , t2)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1, newT2] -> pure (SubGrad newT1 newT2, Pure (UserValue (RAnonymous MemAny)))
    [newT1, newT2] -> pure (SubGrad newT1 newT2, VirtualMutated mutVars)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (ScaleGrad scalar grads) = do
  (argTerms, mutVars) <- elaborateMutList "scalegrad" scname scope [(NotMutated , scalar), (Mutated , grads)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1, newT2] -> pure (ScaleGrad newT1 newT2, Pure (UserValue (RAnonymous MemAny)))
    [newT1, newT2] -> pure (ScaleGrad newT1 newT2, VirtualMutated mutVars)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (ClipM c t) = do
  (argTerms, mutVars) <- elaborateMutList "clip" scname scope [(Mutated , t)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT] -> pure (ClipM c newT, Pure (UserValue (RAnonymous MemAny)))
    [newT] -> pure (ClipM c newT, VirtualMutated mutVars)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (Gauss t1 t2 t3 t4) = do
  (argTerms, mutVars) <- elaborateMutList "gauss" scname scope [(NotMutated , t1), (NotMutated , t2), (NotMutated , t3), (Mutated , t4)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1, newT2, newT3, newT4] -> pure (Gauss newT1 newT2 newT3 newT4, Pure (UserValue (RAnonymous MemAny)))
    [newT1, newT2, newT3, newT4] -> pure (Gauss newT1 newT2 newT3 newT4, VirtualMutated mutVars)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (ConvertM t1) = do
  (argTerms, mutVars) <- elaborateMutList "convert" scname scope [(Mutated , t1)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1] -> pure (ConvertM newT1, Pure (UserValue (RAnonymous MemAny)))
    [newT1] -> pure (ConvertM newT1, VirtualMutated mutVars)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

-- the non mutating builtin cases
elaborateMut scname scope (Transpose t1) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  return (Transpose newT1 , Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (Ret t1) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  return (Ret newT1 , Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (Tup t1s) = do
  newT1s <- fmap fst <$> mapM (elaborateNonmut scname scope) t1s
  return (Tup newT1s , Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (MCreate t1 t2 t3 t4) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  (newT2, newT2Type) <- elaborateNonmut scname scope t2
  (newT4, newT4Type) <- elaborateNonmut scname scope t4
  return (MCreate newT1 newT2 t3 newT4 , Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (Index t1 t2 t3) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  (newT2, newT2Type) <- elaborateNonmut scname scope t2
  (newT3, newT3Type) <- elaborateNonmut scname scope t3
  return (Index newT1 newT2 newT3 , Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (VIndex t1 t2) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  (newT2, newT2Type) <- elaborateNonmut scname scope t2
  return (VIndex newT1 newT2 , Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (Row t1 t2) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  (newT2, newT2Type) <- elaborateNonmut scname scope t2
  return (Row newT1 newT2, Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (Size t1) = do
  (newT1, newT1Type) <- elaborateMut scname scope t1
  return (Size newT1, Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (Length t1) = do
  (newT1, newT1Type) <- elaborateMut scname scope t1
  return (Length newT1, Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (ZeroGrad t1) = do
  (newT1, newT1Type) <- elaborateMut scname scope t1
  return (ZeroGrad newT1, Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (SumGrads t1 t2) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  (newT2, newT2Type) <- elaborateNonmut scname scope t2
  return (SumGrads newT1 newT2, Pure (UserValue (RAnonymous MemAny)))
elaborateMut scname scope (Sample t1 t2 t3) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  (newT2, newT2Type) <- elaborateNonmut scname scope t2
  (newT3, newT3Type) <- elaborateNonmut scname scope t3
  return (Sample newT1 newT2 newT3 , Pure (UserValue (RAnonymous MemAny)))

-- the unsupported terms
elaborateMut scname scope term@(Choice t1)        = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname scope term@(Loop t1 t2 t3 t4) = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname scope term@(Reorder t1 t2)    = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname scope term@(TProject t1 t2)    = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname scope term@(Arg x a b)        = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname scope term@(BBApply x a b)    = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))



---------------------------------------------------
-- recurring utilities



-------------
-- elaborating a lambda term
--

elaborateLambda :: ScopeVar -> Scope -> [Asgmt JuliaType] -> MutDMTerm -> MTC (DMTerm , ImmutType)
elaborateLambda scname scope args body = do
  -- First, backup the VA-Ctx to be able to restore those
  -- variables which have the same name as our arguments
  --
  -- See https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/148#issuecomment-1004950955
  --
  -- Then, mark all function arguments as "SingleRead"
  -- for the current scope.
  oldVaCtx <- use vactx
  mapM (overwriteTeVarAccess scname ReadSingle) [a | (Just a :- _) <- args]


  newVaCtx <- use vactx
  debug $ "---------------------------------------------"
  debug $ "[elaborateLambda]: Entering scope " <> show scname
  debug $ "old VACtx:\n" <> show oldVaCtx <> "\n"
  debug $ "new VACtx:\n" <> show newVaCtx <> "\n"


  {-
  -- Add args as vars to the scope
  --
  -- NOTE: we do not use `safeSetValue` here, because function
  --       arguments are allowed to have different types than
  --       their eventually preexisting same named variables
  --       outside of the function.
  --       Also, we do not trigger a variable access type error.
  let f (Just a :- _) = setValue a (Pure (SingleArg a))
      f (Nothing :- _) = \x -> x
  let scope' = foldr f -- (\(Just a :- _) -> setValue a (Pure (SingleArg a)))
                     scope
                     args
  -}

  --
  -- Create memory locations in `scname` for the arguments.
  --
  let f scope (a :- _) = overwriteTeVarMaybe scname a MemAny scope
  scope' <- foldM f scope args

  -- check the body
  (newBody,τ) <- elaborateMut scname scope' body

  -- read the memvars which belong to the args
  -- and get the VAType of their content
  let getVar :: (Asgmt JuliaType) -> MTC (Maybe (TeVar, IsMutated))
      getVar (Just tevar :- t) = do
        (mt,mut,_) <- metaExpectScopeValue tevar scope' >>= metaExpectMemCtxValue

        pure (Just (tevar , mut))
      getVar (Nothing :- t) = pure Nothing


  -----------
  -- Restore old VA state for all args
  -- (https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/148#issuecomment-1004950955)
  --
  vactxBeforeRestoration <- use vactx
  let restoreArg tevar = do
        case getValue tevar oldVaCtx of
          Nothing -> vactx %%= (\ctx -> ((), deleteValue tevar ctx))
          Just (oldva, oldscname) -> vactx %%= (\ctx -> ((), setValue tevar (oldva, oldscname) ctx))
  mapM restoreArg [a | (Just a :- _) <- args]
  --
  -----------


  {-
  -- restore the VA-Types of the arguments to this lambda from the backup'ed `oldVaCtx`
  -- and also get their new values
  let getVar :: (Asgmt JuliaType) -> MTC (Maybe (TeVar, IsMutated))
      getVar (Just a :- t) = do
        mut <- mutTypes %%= restoreValue oldVaCtx a
        case mut of
          Nothing              -> pure (Just (a , NotMutated))
          Just (WriteSingle _ _) -> pure (Just (a , Mutated))
          Just (WriteSingleFunction _ _) -> pure (Just (a , Mutated))
          Just _               -> pure (Just (a , NotMutated))
      getVar (Nothing :- t) = pure Nothing
  -}

  -- call this function on all args given in the signature
  -- and extract those vars that are mutated
  vars_mutationState <- mapM getVar args
  let mutVars = [v | Just (v , Mutated) <- vars_mutationState]
  let mutationsStates = [m | Just (_ , m) <- vars_mutationState]


  mc <- use memctx
  vac <- use vactx


  debug $ "----------------"
  debug $ "-- scope' is:\n" <> show scope' <> "\n"
  debug $ "----------------"
  debug $ "-- memctx is:\n" <> show mc <> "\n"
  debug $ "----------------"
  debug $ "-- after-body-vactx is:\n" <> show vactxBeforeRestoration <> "\n"
  debug $ "----------------"
  debug $ "-- restored vactx is:\n" <> show vac <> "\n"
  debug $ "----------------"
  debug $ "-- vars_mutationState are: " <> show vars_mutationState <> "\n"
  debug $ ""
  debug $ "-- Exited scope " <> show scname
  debug $ "---------------------------------------------"

  -- cleanup all memory locations of this scope
  cleanupMemoryLocations scname

  -- now, depending on whether we have a mutating lambda,
  -- do the following

  case τ of
    --
    -- case I : Mutating
    --
    -- check that the body is a mutation result
    -- and reorder the resulting tuple
    --
    -- VirtualMutated vars | [v | (v,NotLocalMutation) <- vars] /= [] -> do
    VirtualMutated vars | mutVars /= [] -> do

      -- get the permutation which tells us how to go
      -- from the order in which the vars are returned by the body
      -- to the order in which the lambda arguments are given
      --

      -- NOTE: WIP/test -v-
      -- we also check that there is not a mixture of local/nonlocal mutated variable
      {-
      let bothVars = [(v) | (v, NotLocalMutation) <- vars , (w,LocalMutation) <- vars, v == w]
      case bothVars of
        [] -> pure ()
        xs -> throwError (DemutationError $ "The variable names " <> show xs <> " are used for both locally mutated and not locally mutated things. This is not allowed. ")
      -}

      --
      -- NOTE: Simply using vars' in the next statement
      --       is probably wrong, and we need to make sure something
      --       about whether the variables switched "locality", which
      --       is not a primary concept anymore
      --
      let vars' = [v | (v , _) <- vars]
      -- let mutVars' = [(v , NotLocalMutation) | v <- mutVars]

      -- logForce $ "Found permutation " <> show vars <> " ↦ " <> show mutVars <>". It is: " <> show σ
      -- pure ((wrapReorder vars mutVars' newBody) , Pure (UserValue (RAnonymous (MemMutatingFun mutationsStates))))
      pure ((wrapReorder vars' mutVars newBody) , Pure (UserValue (RAnonymous (MemMutatingFun mutationsStates))))

    --
    -- case II : Not Mutating
    --
    Pure t | mutVars /= [] -> demutationError $ "Found a function which is mutating, and has a return value. This is not allowed.\n"
                                       <> "\nThe function is:\n" <> showPretty body <> "\n"
                                       <> "\nThe function type is: " <> show (Pure t) <> "\n"
                                       <> "\nThe mutated variables are: " <> show (mutVars) <> "\n"

    Pure _ -> pure (newBody , Pure (UserValue (RAnonymous MemPureFun)))

    --
    -- case III : locally mutating without return value
    --
    -- this is not allowed
    -- VirtualMutated vars | [v | (v,NotLocalMutation) <- vars] == []
    VirtualMutated vars | mutVars == []
      -> throwError (DemutationError $ "Found a function which is neither mutating, nor has a return value. This is not allowed."
                                       <> "\nThe function type is: " <> show (VirtualMutated vars)
                                       <> "\nThe function is:\n" <> showPretty body)

    wrongτ -> throwError (DemutationError $ "Expected the result of the body of a mutating lambda to be a virtual mutated value. But it was "
                          <> show wrongτ <> "\n where body is:\n" <> showPretty body)


-------------
-- elaborating a list of terms which are used in individually either mutating, or not mutating places
--

elaborateMutList :: String -> ScopeVar -> Scope -> [(IsMutated , MutDMTerm)] -> MTC ([DMTerm] , [(TeVar, MemVar)])
elaborateMutList f scname scope mutargs = do
  ---------
  -- NOTE: Because of #95, currently mutation is DISABLED,
  --       we simulate this by saying that all arguments are to be treated as non mutating
  -- NOTE: Reenabled for #142
  -- let mutargs = [(NotMutated,a) | (_ , a) <- mutargs']
  --
  -- NOTE END
  ---------

  -- function for typechecking a single argument
  let checkArg :: (IsMutated , RValue) -> MTC (Maybe (MemVar))
      checkArg (Mutated , arg) = do
        -- if the argument is given in a mutable position,
        -- it _must_ be a var
        case arg of
          RMem (mv) -> do
            applyMemVarAccess scname mv Mutated pure
            return (Just (mv))
          -- (Var (Just x :- a)) -> do
          --   -- get the type of this var from the scope
          --   -- this one needs to be a single arg
          --   case getValue x scope of
          --     Nothing -> logForce ("The scope is" <> show scope) >> throwError (DemutationDefinitionOrderError x)
          --     Just (Pure (SingleArg y)) | x == y -> do
          --       debug $ "[elaborateMutList]: The non-local variable " <> show y <> " is being mutated."
          --       loc <- markMutated scname NotLocalMutation y
          --       return (Var (Just x :- a) , Just (x, loc))
          --     Just (Pure (SingleArg y)) -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the variable " <> show x <> " as argument in a mutable-argument-position. It is bound to the function argument " <> show y <> ", but it is not allowed to use renamed function arguments in such a position.")
          --     Just (Pure _) -> do
          --       loc <- markMutated scname LocalMutation x
          --       return (Var (Just x :- a) , Just (x, loc))
          --     Just res -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the variable " <> show x <> " as argument in a mutable-argument-position. It has the type " <> show res <> ", which is not allowed here.")

          -- (Var (Nothing :- a)) -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the term " <> showPretty arg <> " as argument in a mutable-argument-position. Only named variables are allowed here.")

          -- if argument is not a var, throw error
          _ -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the type " <> show arg <> " as argument in a mutable-argument-position. Only variables are allowed here.")

      checkArg (NotMutated , τ) = do
        -- if the argument is given in an immutable position,
        -- we allow to use the full immut checking
        -- (arg' , τ) <- elaborateMut scname scope arg

        -- 
        -- get the memory type behind τ
        --
        mt <- case τ of
          (RAnonymous mt) -> return mt
          (RMem mv)       -> do
            (mt,_,_) <- metaExpectMemCtxValue mv
            return mt

        -- we require the argument to be of pure type
        case mt of
          ((MemMutatingFun _)) -> throwError (DemutationError $ "It is not allowed to pass mutating functions as arguments. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")
          ((MemPureBlackBox)) -> throwError (DemutationError $ "It is not allowed to pass black boxes as arguments. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")
          _ -> return ()
          -- Mutating _ -> throwError (DemutationError $ "It is not allowed to pass mutating functions as arguments. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")
          -- PureBlackBox -> throwError (DemutationError $ "It is not allowed to pass black boxes as arguments. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")

        return (Nothing)

  let processOneTerm (mut,term) = do
        (t2,ty2) <- elaborateMut scname scope term
        ty2' <- metaExpectRValue ty2
        mv <- checkArg (mut, ty2')
        return (t2, mv)

  -- elaborate terms
  newArgsWithMutTeVars <- mapM (processOneTerm) mutargs 

  -- check them
  -- newArgsWithMutTeVars <- mapM checkArg mutargs
  -- extract for return
  let newArgs = [te | (te , _) <- newArgsWithMutTeVars]

  let f memvar = do
        tevar <- reverseScopeLookup scope memvar
        applyTeVarAccess scname WriteSingle tevar
        return (tevar,memvar)

  mutVars <- mapM f [m | (_ , Just m) <- newArgsWithMutTeVars]


  {-
  --
  -- Make sure that all variables in mutated argument positions are unique
  -- For this, we count the occurences of every variable, simply
  -- by taking the free variables of the demutated terms.
  --
  -- See #95
  --

  -- let allVars = [t | (t, _) <- newArgsWithMutTeVars] >>= freeVarsDMTerm
  let allVars = [t | (t, _) <- mutVars]

  let addCount :: (DMTerm , Maybe (TeVar, IsLocalMutation)) -> Ctx TeVar Int -> Ctx TeVar Int
      addCount (_ , Just (var , _)) counts = case getValue var counts of
                                              Just a -> setValue var (a P.+ 1) counts
                                              Nothing -> setValue var 1 counts
      addCount (_ , Nothing) counts = counts

  -- number of occurences of all variables
  let varcounts = getAllKeyElemPairs $ foldr addCount def newArgsWithMutTeVars
  -- number of occurences of all variables, but only for variables which are mutated
  let mutvarcounts = filter (\(k,n) -> k `elem` (fst <$> mutVars)) varcounts
  -- number of occurences of all variables, but only for variables which are mutated, with occurence > 1
  let wrongVarCounts = filter (\(k,n) -> n > 1) mutvarcounts

  -- make sure that such variables do not occur
  case wrongVarCounts of
    [] -> return ()
    xs -> throwError $ DemutationError $ "The function '" <> f <> "' is called with the following vars in mutating positions:\n"
                                      <> show mutvarcounts <> "\n"
                                      <> "But it is not allowed to have the same variable occur multiple times "

  -}


  return (newArgs, mutVars)


------------------------------------------------------------
-- preprocessing a for loop body

runPreprocessLoopBody :: Scope -> Maybe TeVar -> MutDMTerm -> MTC (MutDMTerm, [TeVar])
runPreprocessLoopBody scope iter t = do
  (a,x) <- runWriterT (preprocessLoopBody scope iter t)
  return (a, nub x)

-- | Walks through the loop term and changes SLet's to `modify!`
--   calls if such a variable is already in scope.
--   Also makes sure that the iteration variable `iter` is not assigned,
--   and that no `FLet`s are found.
--   Returns the variables which were changed to `modify!`.
preprocessLoopBody :: Scope -> Maybe TeVar -> MutDMTerm -> WriterT [TeVar] MTC MutDMTerm

preprocessLoopBody scope iter (SLetBase ltype (v :- jt) term body) = do
  -- it is not allowed to change the iteration variable
  case (iter, v) of
    (Just iter, Just v) | iter == v
                          -> throwOriginalError (DemutationError $ "Inside for-loops the iteration variable (in this case '" <> show iter <> "') is not allowed to be mutated.")
    _ -> pure ()

  -- if an slet expression binds a variable which is already in scope,
  -- then this means we are actually mutating this variable.
  -- thus we update the term to be a mutlet and use the builtin modify!
  -- function for setting the variable
  -- if the variable has not been in scope, it is a local variable,
  -- and we do not change the term

  (term') <- preprocessLoopBody scope iter term
  (body') <- preprocessLoopBody scope iter body
  -- let newVars = nub (termVars <> bodyVars)

  case v of
    Just v -> case getValue v scope of
                Just _  -> tell [v] >> return (Extra (MutLet ltype (Extra (SModify (Just v :- jt) term')) (body')))
                Nothing -> return (SLetBase ltype (Just v :- jt) term' body')

    Nothing -> return (SLetBase ltype (v :- jt) term' body')


preprocessLoopBody scope iter (TLet (vs) term body) = do
  -- it is not allowed to change the iteration variable
  case (iter) of
    (Just iter) | (Just iter) `elem` (fstA <$> vs)
                          -> throwOriginalError (DemutationError $ "Inside for-loops the iteration variable (in this case '" <> show iter <> "') is not allowed to be mutated.")
    _ -> pure ()

  -- if an slet expression binds a variable which is already in scope,
  -- then this means we are actually mutating this variable.
  -- thus we update the term to be a mutlet and use the builtin modify!
  -- function for setting the variable
  -- if the variable has not been in scope, it is a local variable,
  -- and we do not change the term

  (term') <- preprocessLoopBody scope iter term
  (body') <- preprocessLoopBody scope iter body

  -- we collect those values of vs for which there is something in the scope
  let vs_in_scope = [v | (Just v :- _) <- vs, (Just _) <- [getValue v scope]]

  case vs_in_scope of
    [] -> return (TLet vs term' body')
    tv : tvs -> tell vs_in_scope >> return (Extra (MutLet PureLet (Extra (TModify (vs) term')) (body')))

preprocessLoopBody scope iter (FLet f _ _) = throwOriginalError (DemutationError $ "Function definition is not allowed in for loops. (Encountered definition of " <> show f <> ".)")
preprocessLoopBody scope iter (Ret t) = throwOriginalError (DemutationError $ "Return is not allowed in for loops. (Encountered " <> show (Ret t) <> ".)")

-- mutlets make us recurse
preprocessLoopBody scope iter (Extra (MutLet mtype t1 t2)) = do
  (t1') <- preprocessLoopBody scope iter t1
  (t2') <- preprocessLoopBody scope iter t2
  return (Extra (MutLet mtype t1' t2'))

-- for the rest we simply recurse
preprocessLoopBody scope iter t = do
  x <- recDMTermMSameExtension (preprocessLoopBody scope iter) t
  return x






--------------------------------------------------------
-- removing unnecessary tlets

--
-- | Walk through the tlet sequence in `term` until
--  the last 'in', and check if this returns `αs`
--  as a tuple. If it does, replace it by `replacement`
--  and return the new term.
--  Else, return nothing.
replaceTLetIn :: [Maybe TeVar] -> DMTerm -> DMTerm -> Maybe DMTerm

-- If we have found our final `in` term, check that the tuple
-- is correct
replaceTLetIn αs replacement (TLet βs t1 (Tup t2s)) =

  let isvar :: (Maybe TeVar, DMTerm) -> Bool
      isvar (v, Var (w :- _)) | v == w = True
      isvar _ = False

  in case and (isvar <$> zip αs t2s) of
    -- if it does fit our pattern, replace by a single TLet
    -- and recursively call ourselves again
    True -> Just (TLet βs t1 replacement)

    -- if this does not fit our pattern, recurse into term and body
    False -> Nothing

-- if we have a next tlet, continue with it
replaceTLetIn αs replacement (TLet βs t1 (TLet γs t2 t3)) = TLet βs t1 <$> rest
  where
    rest = replaceTLetIn αs replacement (TLet γs t2 t3)

-- if we have an intermiediate slet, also continue
replaceTLetIn αs replacement (SLet βs t1 (TLet γs t2 t3)) = SLet βs t1 <$> rest
  where
    rest = replaceTLetIn αs replacement (TLet γs t2 t3)

-- if we have an intermiediate flet, also continue
replaceTLetIn αs replacement (FLet βs t1 (TLet γs t2 t3)) = FLet βs t1 <$> rest
  where
    rest = replaceTLetIn αs replacement (TLet γs t2 t3)

-- if the term is different, we cannot do anything
replaceTLetIn αs replacement _ = Nothing




optimizeTLet :: DMTerm -> DMTerm
-- the interesting case
optimizeTLet (TLet (αs) (term) t3) =
  -- if we have two tlets inside each other, where
  -- one of them returns the exactly the variables
  -- captured by the other, i.e:
  --
  -- > tlet αs... = tlet βs = t1
  -- >              in (αs...)
  -- > in t3
  --
  -- then we can change it to
  --
  -- > tlet βs = t1
  -- > in t3
  --
  --
  -- But, there is one complication, namely:
  -- It could be that the tlet with `in (αs...)`
  -- is not directly inside of our term, but
  -- further nested inside a tlet sequence.
  -- Thus we do search for the `in` using `replaceTLetIn`.
  case replaceTLetIn (fstA <$> αs) t3 term of

    -- if we were successfull, we simply use the returned
    -- term (after recursing on it)
    Just replaced -> optimizeTLet replaced

    -- if not successfull, we recurse
    Nothing -> TLet (αs) (optimizeTLet term) (optimizeTLet t3)

-- the recursion case
optimizeTLet t      = recDMTermSameExtension (optimizeTLet) t






