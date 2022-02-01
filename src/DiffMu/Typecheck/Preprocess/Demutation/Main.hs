
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
import Test.QuickCheck.Property (Result(expect))
import DiffMu.Typecheck.Preprocess.Demutation.Definitions (cleanupMem)

import Control.Monad.Trans.Class



fst3 (a,b,c) = a

demutationError = throwError . DemutationError

--------------------------------------------------------------------------------------
-- Accessing the VA-Ctx in the MTC monad

markReassignedBase :: IsFLetDefined -> ScopeVar -> TeVar -> MTC ()
markReassignedBase fletdef scname tevar = do
  debug $ "[markReassignedBase]: called for " <> show tevar <> " in " <> show scname 

  -- make sure that we are still allowed to access this var
  -- memvar <- expectSingleMem =<< expectNotMoved tevar

  vaCtx %=~ (markReassignedInScope scname tevar)

  newvatype <- getValue tevar <$> use vaCtx

  -- extracting the new locality
  -- newloc <- case newvatype of
  --               Just (WriteSingleBase _ _ newloc) -> return newloc
  --               _ -> impossible "Expected the resulting locality after `markReassignedBase` to be a `WriteSingleBase`."

  return ()

    -- The actual updating function
    where 
      markReassignedInScope :: ScopeVar -> TeVar -> VarAccessCtx -> MTC VarAccessCtx 
      markReassignedInScope scname tevar ctx =
        case getValue tevar ctx of
          Nothing                      -> impossible $ "When demutating (MarkMutated), the variable "
                                                       <> show tevar <> " was not in the VA-Ctx."
          Just oldvatype -> do
            newvatype <- computeVarAccessType tevar oldvatype (scname, WriteSingleBase fletdef)
            debug $ "[markReassignedBase]: VA type for '" <> show tevar <> "' changes from " <> show oldvatype <> " to " <> show newvatype
            return (setValue tevar (scname, newvatype) ctx)

markReassignedFLet :: ScopeVar -> TeVar -> MTC ()
markReassignedFLet scname var = do
  log $ "Marking flet mutated for " <> show var
  markReassignedBase FLetDefined scname var

--
-- Apply a mutation of `loc` locality to the `var`.
-- This might or might not change `loc`, depending on whether this variable
-- is already local or not-local.
-- The resulting locality is returned.
--
markReassigned :: ScopeVar -> TeVar -> MTC ()
markReassigned scname var = do
  log $ "Marking simple mutated for " <> show var
  markReassignedBase NotFLetDefined scname var


markRead :: ScopeVar -> TeVar -> MTC ()
markRead scname tevar = do
   debug $ "[markRead]: called for tevar" <> show tevar <> " in " <> show scname 
  --  mvars <- getAllMemVars <$> expectNotMoved var -- we make sure that we are still allowed to use this variable
   let f v = vaCtx %=~ (markReadInScope scname v) 
        where 
          markReadInScope :: ScopeVar -> TeVar -> VarAccessCtx -> MTC VarAccessCtx 
          markReadInScope scname tevar ctx =
            case getValue tevar ctx of
              Nothing                      -> pure (setValue tevar (scname, ReadSingle) ctx)
              Just oldvatype -> do
                newvatype <- computeVarAccessType tevar oldvatype (scname, ReadSingle)
                return (setValue tevar (scname,newvatype) ctx)

   f tevar
   return ()

markReadMaybe :: ScopeVar -> Maybe TeVar -> MTC ()
markReadMaybe scname (Just x) = markRead scname x
markReadMaybe scname Nothing = pure ()

markReadOverwritePrevious :: ScopeVar -> TeVar -> MTC ()
markReadOverwritePrevious scname var = vaCtx %%= (\scope -> ((), setValue var (scname, ReadSingle) scope))

--------------------------------------------------------------------------------------

markMutated :: MemVar -> MTC ()
markMutated mv = do
  let f ctx = do
        case getValue mv ctx of
          Nothing -> impossible ""
          Just (scvar,_) -> return $ setValue mv (scvar, Mutated) ctx

  mutCtx %=~ f
  return ()


--------------------------------------------------------------------------------------


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

-- set the type of the variable in scope,
-- but do not allow to change that value afterwards.
safeSetValueBase :: IsFLetDefined -> ScopeVar -> Maybe TeVar -> ImmutType -> Scope -> MTC Scope
safeSetValueBase fletdef scname(Nothing) newType scope = pure scope
safeSetValueBase fletdef scname(Just var) newType scope =
  case getValue var scope of
    Nothing -> do
      debug $ "[safeSetValue]: Var " <> show var <> " not in scope " <> show scname <> ". Marking read."
      markRead scname var
      return (setValue var newType scope)
    (Just oldType) -> do
      debug $ "[safeSetValue]: Var " <> show var <> " is already in scope " <> show scname <> ". Marking as mutated."
      markReassignedBase fletdef scname var -- We say that we are changing this variable. This can throw an error.
      if immutTypeEq oldType newType
                      then pure scope
                      else throwError (DemutationError $ "Found a redefinition of the variable '" <> show var <> "', where the old type (" <> show oldType <> ") and the new type (" <> show newType <> ") differ. This is not allowed.")

safeSetValue = safeSetValueBase NotFLetDefined
safeSetValueAllowFLet = safeSetValueBase FLetDefined

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

--
-- This function marks variables as moved in the scope
-- For #172
--
moveGetMem :: ScopeVar -> MoveType -> MTC MemType
moveGetMem scname NoMove = SingleMem <$> allocateMem scname ""
moveGetMem scname (SingleMove a) = do
  memvar <- expectNotMoved a
  memCtx %= (setValue a (MemMoved))
  return memvar
moveGetMem scname (TupleMove as) = TupleMem <$> mapM (moveGetMem scname) as
moveGetMem scname (RefMove) = pure RefMem

setMemMaybe :: Maybe TeVar -> MemType -> MTC () 
setMemMaybe (Just x) mt = memCtx %= (setValue x (MemExists mt))
setMemMaybe (Nothing) _ = pure ()

setMemTuple :: ScopeVar -> [Maybe TeVar] -> MemType -> MTC ()
setMemTuple scname xs (SingleMem a) = do
  -- We are deconstructing a tuple value,
  -- need to create memory locations for all parts
  let f (Just x) = do
        mx <- allocateMem scname (T.pack $ show x)
        memCtx %= (setValue x (MemExists (SingleMem mx)))
      f Nothing = pure ()
  mapM_ f xs
setMemTuple scname xs (RefMem) = do
  mapM_ (\(x) -> setMemMaybe x (RefMem)) xs

setMemTuple scname xs (TupleMem as) | length xs == length as = do
  let xas = zip xs as
  mapM_ (\(x, a) -> setMemMaybe x a) xas

setMemTuple scname xs (TupleMem as) | otherwise = demutationError $ "Trying to assign a tuple where lengths do not match:\n"
                                                                    <> show xs <> " = " <> show as


expectNotMoved :: TeVar -> MTC MemType
expectNotMoved tevar = do
  mc <- use memCtx
  case getValue tevar mc of
    Nothing          -> demutationError $ "The variable " <> show tevar <> " is not assigned to anything.\n"
                                        <> "The memctx is:\n"
                                        <> show mc
    Just (MemMoved) -> throwError $ DemutationMovedVariableAccessError tevar
    Just (MemExists a) -> pure a

ensureNotMovedMaybe :: Maybe TeVar -> MTC () 
ensureNotMovedMaybe (Just a) = expectNotMoved a >> return ()
ensureNotMovedMaybe Nothing = return ()

getAllMemVars :: MemType -> [MemVar]
getAllMemVars (SingleMem a) = [a]
getAllMemVars (TupleMem a) = a >>= getAllMemVars
getAllMemVars (RefMem) = []

expectSingleMem :: MemType -> MTC MemVar
expectSingleMem mt = do
  case mt of
    (SingleMem a) -> pure a
    (mem) -> demutationError $ "The memory type " <> show mem <> " was expected to contain a single memory location."

reverseMemLookup :: MemVar -> MTC TeVar
reverseMemLookup wantedMem = do
  alltemems <- getAllKeyElemPairs <$> use memCtx
  let relevantTemems = [(t,m) | (t,MemExists m) <- alltemems, wantedMem `elem` getAllMemVars m]

  case relevantTemems of
    [] -> demutationError $ "When doing a reverse memory lookup for memory variable " <> show wantedMem <> ", no tevar was found."
    [(t,a)] -> case a of
                SingleMem a -> return t
                a  -> demutationError $ "When doing a reverse memory lookup for memory variable " <> show wantedMem <> ", expected it to have an individual name.\n"
                                      <> "but it was part of a compound type: " <> show a
    xs -> demutationError $ "When doing a reverse memory lookup for memory variable " <> show wantedMem <> ", multiple tevars were found: " <> show xs

  
-- checkIsNotMoved :: TeVar -> MTC ()
-- checkIsNotMoved var = undefined -- do
  -- mc <- use moveCtx
  -- case getValue var mc of
  --   Nothing          -> pure ()
  --   Just (Moved)     -> throwError $ DemutationMovedVariableAccessError var
  --   Just (NotMoved)  -> pure ()



rearrangePhi :: MutDMTerm -> MTC MutDMTerm
rearrangePhi term = recDMTermM rearrangePhi rearrangePhiExt term

-- make MutPhi into Phi by appending the tail to both branches.
rearrangePhiExt :: MutabilityExtension MutDMTerm -> MTC (MutDMTerm)
rearrangePhiExt (MutPhi condition branches tail) =
    case branches of
         [ifb] -> do
             rcond <- rearrangePhi condition
             rifb <- rearrangePhi ifb
             case tail of
                  (Extra DNothing) -> return (Phi condition rifb (Extra MutRet))
                  _ -> do
                         rtail <- rearrangePhi tail
                         return (Phi condition (Extra (MutLet PureLet rifb rtail)) rtail)
         [ifb, elseb] -> do
             rcond <- rearrangePhi condition
             rifb <- rearrangePhi ifb
             relseb <- rearrangePhi elseb
             case tail of
                  (Extra DNothing) -> return (Phi condition rifb relseb)
                  _ -> do
                         rtail <- rearrangePhi tail
                         return (Phi condition (Extra (MutLet PureLet rifb rtail)) (Extra (MutLet PureLet relseb rtail)))
         _ -> internalError $ "MutPhi has too many branches"
rearrangePhiExt term = do
  let x = (recDMTermM rearrangePhi rearrangePhiExt) <$> term
  x' <- sequence x
  return $ Extra x'


---
-- elaborating loops
-- not allowed:
-- - FLet
-- - JuliaReturn
-- - modify iteration variable

demutate :: MutDMTerm -> MTC (DMTerm)
demutate term = do
  logForce $ "Term before phi rearranging:\n" <> showPretty term

  term' <- rearrangePhi term

  logForce $ "-----------------------------------"
  logForce $ "Term before mutation elaboration:\n" <> showPretty term'

  topscname <- newScopeVar "toplevel"

  (res , _, _) <- elaborateMut topscname def term'
  logForce $ "-----------------------------------"
  logForce $ "Mutation elaborated term is:\n" <> showPretty res

  let optimized = optimizeTLet res
  logForce $ "-----------------------------------"
  logForce $ "TLet optimized term is:\n" <> showPretty optimized

  return optimized


elaborateNonmut :: ScopeVar -> Scope -> MutDMTerm -> MTC (DMTerm , ImmutType, MoveType)
elaborateNonmut scname scope term = do
  (resTerm , resType, mType) <- elaborateMut scname scope term

  -- get the context and make sure that all variables are not mutated
  -- Ctx (MonCom ctx) <- use vaCtx
  -- let ctxElems = H.toList ctx
  -- let somethingMutated = [a | (a , m) <- ctxElems, m == Mutated]

  -- case somethingMutated of
  --   [] -> pure ()
  --   xs -> throwError (DemutationError $ "expected that the term " <> show term <> " does not mutate anything, but it mutates the following variables: " <> show xs)

  -- make sure that the result is not a mutation result

  case resType of
    Pure _ -> pure ()
    VirtualMutated mutvars -> throwError (DemutationError $ "expected that the term " <> showPretty term <> " does not mutate anything, but it mutates the following variables: " <> show mutvars)
    Mutating _ -> pure ()
    PureBlackBox -> pure ()

  return (resTerm , resType, mType)

elaborateMut :: ScopeVar -> Scope -> MutDMTerm -> MTC (DMTerm , ImmutType, MoveType)

elaborateMut scname scope (Op op args) = do
  args' <- mapM (elaborateNonmut scname scope) args
  pure (Op op (fst3 <$> args') , Pure UserValue, NoMove)
elaborateMut scname scope (Sng η τ) = pure (Sng η τ , Pure UserValue, NoMove)
--elaborateMut scname scope (Rnd jt) = pure (Rnd jt , Pure UserValue)

elaborateMut scname scope (Var (x :- j)) = do
  let τ = getValueMaybe x scope
  case τ of
    Nothing -> logForce ("checking Var term, scope: " <> show scope) >> throwError (DemutationDefinitionOrderError x)
    Just τ  -> do
      markReadMaybe scname x
      ensureNotMovedMaybe x
      return (Var (x :- j), τ, singleMoveMaybe x)

elaborateMut scname scope (BBLet name args tail) = do

  -- write the black box into the scope with its type
  scope'  <- safeSetValue scname (Just name) PureBlackBox scope

  -- also write it into the memctx
  setMemMaybe (Just name) =<< SingleMem <$> allocateMem scname (T.pack $ show name)

  -- typecheck the body in this new scope
  (newBody , newBodyType, _) <- elaborateMut scname scope' tail

  return (BBLet name args newBody , consumeDefaultValue newBodyType, NoMove)

elaborateMut scname scope (SLetBase ltype (x :- τ) term body) = do

  (newTerm , newTermType, moveType) <- elaborateMut scname scope term

  case newTermType of
    Pure _ -> pure ()
    Mutating _ -> pure ()
    VirtualMutated _ -> throwError (DemutationError $ "Found an assignment " <> show x <> " = " <> showPretty term <> " where RHS is a mutating call. This is not allowed.")
    PureBlackBox     -> throwError (DemutationError $ "Found an assignment " <> show x <> " = " <> showPretty term <> " where RHS is a black box. This is not allowed.")



  -- move out of variables on the RHS
  -- and set memory locations for variables on the LHS
  mem <- moveGetMem scname moveType
  setMemMaybe x mem

  -- this has to happen after `setMemMaybe`
  -- because the variable has to exist in the `memCtx`
  scope'  <- safeSetValue scname x newTermType scope

  debug $ "[elaborateMut/SLetBase]: The variable " <> show x <> " is being assigned." 
  logmem <- use memCtx
  debug $ "The memctx is now:\n"
  debug $ show logmem

  (newBody , newBodyType, moveType) <- elaborateMut scname scope' body
  return (SLetBase ltype (x :- τ) newTerm newBody , consumeDefaultValue newBodyType, moveType)

elaborateMut scname scope fullterm@(TLetBase ltype vars term body) = do

  (newTerm , newTermType, moveType) <- elaborateMut scname scope term

  newElementTypes <- case newTermType of
    Pure (PureTuple as)    -> case length as == length vars of
                                True  -> pure as
                                False -> demutationError $ "Encountered tuple assignment where the number of entries does not match the number of variables\n"
                                                          <> "In the expression\n"
                                                          <> showPretty fullterm
    Pure (UserValue)       -> pure (repeat UserValue)
    Pure (SingleArg a)     -> pure (repeat $ SingleArgPart a)
    Pure (SingleArgPart a) -> pure (repeat $ SingleArgPart a)
    -- Pure (SingleRef)       -> pure (repeat $ SingleRef)
    Pure (DefaultValue)    -> pure (repeat $ UserValue)
    Mutating _             -> pure (repeat $ UserValue)
    VirtualMutated _ -> throwError (DemutationError $ "Found an assignment " <> show vars <> " = " <> showPretty term <> " where RHS is a mutating call. This is not allowed.")
    PureBlackBox     -> throwError (DemutationError $ "Found an assignment " <> show vars <> " = " <> showPretty term <> " where RHS is a black box. This is not allowed.")

  -- move out of variables and get memory locations
  mem <- moveGetMem scname moveType
  setMemTuple scname (fstA <$> vars) mem
  
  -- add all values as pure to the scope
  scope' <- foldrM (\((v :- _),newElType) s -> safeSetValue scname v (Pure newElType) s) scope (zip vars newElementTypes)
  (newBody , newBodyType, newMoveType) <- elaborateMut scname scope' body

  return (TLetBase ltype vars newTerm newBody , consumeDefaultValue newBodyType, newMoveType)

elaborateMut scname scope (LamStar args body) = do
  bodyscname <- newScopeVar "lamstar"
  (newBody, newBodyType) <- elaborateLambda bodyscname scope [(v :- x) | (v :- (x , _)) <- args] body
  return (LamStar args newBody, newBodyType, NoMove)

elaborateMut scname scope (Lam args body) = do
  bodyscname <- newScopeVar "lam"
  (newBody, newBodyType) <- elaborateLambda bodyscname scope args body
  return (Lam args newBody, newBodyType, NoMove)

elaborateMut scname scope (Apply f args) = do
  --
  -- The MoveType of function applications is always `NoMove`,
  -- because we make sure in typechecking that functions can
  -- never return objects which are aliased with some pre-existing
  -- variable (of a type which would contain mutable references)
  --
  -- Thus the return value of a function is always "at a fresh memory location"
  -- and we do not need to mark anything as moved.
  --
  -- See #171 / #172.
  --

  -- typecheck the function f
  (newF , τ, _) <- elaborateNonmut scname scope f

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
        return (Apply newF newArgs , retType muts, NoMove)
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

        return (BBApply newF newArgs glvars , Pure UserValue, NoMove)
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
  -- Alternatively it can be a pure black box call
  case τ of
        Pure _           -> applyMutating (take (length args) (repeat NotMutated)) (\_ -> Pure UserValue)
        Mutating muts    -> applyMutating muts VirtualMutated
        PureBlackBox     -> applyPureBlackBox
        VirtualMutated _ -> throwError (DemutationError $ "Trying to call the result of a mutating call " <> showPretty f <> ". This is not allowed.")





elaborateMut scname scope (FLet fname term body) = do
  --
  -- Regarding MoveType: it is not possible to have terms
  -- where an flet is followed by something movable, i.e.
  -- a variable. Because FLets are only generated when they
  -- are actually followed by an (anonymous) function definition.
  -- Which means that we do not have to mark anything as moved here.
  --

  -- check the term
  (newTerm, newTermType, moveType) <- elaborateNonmut scname scope term

  -- set the value in the memctx
  setMemMaybe (Just fname) =<< SingleMem <$> allocateMem scname (T.pack $ show fname)

  logmem <- use memCtx
  debug $ "[elaborateMut/FLet] For flet for " <> show fname <> " memctx is\n"
  debug $ show logmem
  debug $ ""

  -- get the current type for fname from the scope
  let ftype = getValue fname scope

  -- set the new scope with fname if not already existing
  -- (but only allow pure uservalue-functions, or single-definition mutating functions)
  scope' <- case ftype of
        Nothing -> safeSetValueAllowFLet scname (Just fname) newTermType scope
        Just (Pure UserValue) -> safeSetValueAllowFLet scname (Just fname) newTermType scope
        Just (Mutating _) -> throwError (DemutationError $ "We do not allow mutating functions to have multiple definitions")
        Just (Pure DefaultValue) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        Just (Pure (PureTuple _)) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        -- Just (Pure (SingleRef)) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        Just (Pure (SingleArg _)) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        Just (Pure (SingleArgPart _)) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        Just (VirtualMutated _) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        Just (PureBlackBox) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"


  -- check the body with this new scope
  (newBody, newBodyType, newMoveType) <- elaborateMut scname scope' body

  return (FLet fname newTerm newBody, consumeDefaultValue newBodyType, newMoveType)

elaborateMut scname scope (Extra DNothing) = undefined
elaborateMut scname scope (Extra (MutPhi _ _ _)) = internalError $ "MutPhi should have been resolved by rearrangePhi"
elaborateMut scname scope (Extra (MutLet ltype term1 term2)) = do

  --
  -- Regarding MoveType:
  -- As in mutlets no julia assignment is taking place,
  -- there is no move going on. Thus we do not need to move stuff.
  --
  -- TODO: Check the correctness of above explanation.
  --

  -- elaborate the first term and get its mutated variables
  (newTerm1, newTerm1Type, newTerm1MoveType) <- elaborateMut scname scope term1

  --
  -- Change the scope if the first term was virtually mutating,
  -- 
  case newTerm1Type of
        Pure pt -> do
          demutationError $ "Found a pure term in a place where it does not have any effects.\n"
                     <> "The full term is:\n"
                     <> "# ---------------------------\n"
                     <> "# type: " <> show (Pure pt) <> "\n"
                     <> showPretty term1 <> "\n"
                     <> "# ------------\n"
                     <> "# rest:\n"
                     <> showPretty term2 <> "\n"
                     <> "\n"
                     <> "This implies a misunderstanding of semantics, and is thus not allowed."
                    --  "It (the first, pure part) is thus ignored in the privacy analysis."
          -- elaborateMut scname scope term2
        VirtualMutated newScope -> do
          debug $ "[elaborateMut/MutLet]: After first term, have mutctx:"
          logmutctx <- use mutCtx
          debug $ show logmutctx <> "\n"


          let scope' = fromKeyElemPairs (getAllKeyElemPairs scope <> [(s, Pure UserValue) | s <- newScope])
          (newTerm2, newTerm2Type, newTerm2MoveType) <- elaborateMut scname scope' term2

          debug $ "[elaborateMut/MutLet]: After second term, have mutctx:"
          logmutctx <- use mutCtx
          debug $ show logmutctx <> "\n"

          case newScope of
            [] -> demutationError $ "Found a mutating term which does not mutate anything. This does not make sense.\n"
                                  <> "In the first branch of a mutlet, the full term is:"
                                  <> "# ---------------------------\n"
                                  <> "# type: " <> show (VirtualMutated newScope) <> "\n"
                                  <> showPretty term1 <> "\n"
                                  <> "# ------------\n"
                                  <> "# rest:\n"
                                  <> showPretty term2 <> "\n"
            [a] -> return (SLetBase ltype (Just a :- JTAny) newTerm1 newTerm2, newTerm2Type, newTerm2MoveType)
            newScope -> do
                          let ns1 = [Just n :- JTAny | n <- newScope]
                          return (TLetBase ltype ns1 newTerm1 newTerm2, newTerm2Type, newTerm2MoveType)

        mt -> demutationError $ "Unexpected type in first part of mutlet: " <> show mt




{-
  -- find out which variables have been locally modified,
  -- add these to the scope
  let locmutvars1 = case newTerm1Type of
        VirtualMutated xs -> [x | (x,LocalMutation) <- xs]
        _ -> []
  let scope' = foldr (\v s -> setValue v (Pure UserValue) s) scope (locmutvars1)


  -- elaborate the second term and get its mutated variables
  (newTerm2, newTerm2Type, _) <- elaborateMut scname scope' term2

  case (newTerm1Type , newTerm2Type) of

    -----------------------------------
    -- SINGLE GLOBAL, and irrelevant
    -- only term1 is mutating
    (VirtualMutated mutNames1, VirtualMutated []) -> do

      warn $ "Found a term which is not a mutating function call in a place where only such calls make sense.\n"
                     <> "The full term is:\n"
                     <> "---------------------------\n"
                     <> "-- type: " <> show (VirtualMutated mutNames1) <> "\n"
                     <> showPretty term1 <> "\n"
                     <> "------------\n"
                     <> "-- type: " <> show (VirtualMutated []) <> "\n"
                     <> showPretty term2 <> "\n"
                     <> "---------------------------\n"
                    --  <> " => It has the type " <> show (VirtualMutated []) <> "\n"
                    --  <> " => In the term:\n" <> parenIndent (showPretty (Extra (MutLet ltype term1 term2))) <> "\n"
                    --  <> " => Conclusion: It is ignored in the privacy analysis.")

      let ns1 = [Just n :- JTAny | (n, _) <- mutNames1]
          term = TLetBase ltype ns1 newTerm1
                (
                  Tup ((\(a, _) -> Var (Just a :- JTAny)) <$> mutNames1)
                )
      pure (term , VirtualMutated mutNames1, NoMove)


    -- only term2 is mutating
    (VirtualMutated [], VirtualMutated mutNames2) -> do

      warn $ "Found a term which is not a mutating function call in a place where only such calls make sense.\n"
                     <> "The full term is:\n"
                     <> "---------------------------\n"
                     <> "-- type: " <> show (VirtualMutated []) <> "\n"
                     <> showPretty term1 <> "\n"
                     <> "------------\n"
                     <> "-- type: " <> show (VirtualMutated mutNames2) <> "\n"
                     <> showPretty term2 <> "\n"
                     <> "---------------------------\n"
      -- warn ("Found the term " <> showPretty term1
      --                <> " which is not a mutating function call in a place where only such calls make sense.\n"
      --                <> " => It has the type " <> show (VirtualMutated []) <> "\n"
      --                <> " => In the term:\n" <> parenIndent (showPretty (Extra (MutLet ltype term1 term2))) <> "\n"
      --                <> " => Conclusion: It is ignored in the privacy analysis.")

      let ns2 = [Just n :- JTAny | (n, _) <- mutNames2]
          term = TLetBase ltype ns2 newTerm2
                (
                  Tup ((\(a, _) -> Var (Just a :- JTAny)) <$> mutNames2)
                )
      pure (term , VirtualMutated mutNames2, NoMove)

    -------------------------------------------
    -- DOUBLE GLOBAL
    -- both are mutating
    (VirtualMutated mutNames1, VirtualMutated mutNames2) ->
      let commonMutNames = nub (mutNames1 <> mutNames2)
          ns1 = [Just n :- JTAny | (n, _) <- mutNames1]
          ns2 = [Just n :- JTAny | (n, _) <- mutNames2]
          term = TLetBase ltype ns1 newTerm1
                (
                  newTerm2
                  -- TLetBase ltype ns2 newTerm2
                  -- (
                  --   Tup ((\(a, _) -> Var (Just a :- JTAny)) <$> commonMutNames)
                  -- )
                )
      -- we do not take the union here,
      -- because this already must have happened
      -- via tracking the mutated variables in the state
      in pure (term , VirtualMutated mutNames2, NoMove)

    -------------------------------------------
    -- ONLY LOCAL MUTATION
    --
    -- the first command has only locally mutated variables,
    -- and the second one is pure
    (VirtualMutated mutNames1', Pure (p))
      | onlyLocallyMutatedVariables mutNames1' -> do
      log $ "[MutLet] We are in the ONLY LOCAL MUTATION BRANCH"

      let mutNames1 = fst <$> mutNames1'
      let ns1 = [Just n :- JTAny | (n) <- mutNames1]

          valterm = TLetBase ltype ns1 newTerm1
                (
                  newTerm2
                )

      case p of
        UserValue -> pure (valterm , Pure UserValue, NoMove)
        PureTuple as -> pure (valterm , Pure (PureTuple as), NoMove)
        SingleRef -> pure (valterm , Pure (SingleRef), NoMove)
        SingleArg a -> pure (valterm , Pure (SingleArg a), NoMove)
        SingleArgPart x -> pure (valterm , Pure (SingleArgPart x), NoMove)
        -- UserValue -> throwError $ DemutationError $ "Found a local mutation followed by a pure value.\n"
        --                                           <> "This makes not much sense since only one of both can currently be processed.\n\n"
        --                                           <> "---- local mutation ----\n"
        --                                           <> showPretty term1 <> "\n\n"
        --                                           <> "---- pure value ----\n"
        --                                           <> showPretty term2 <> "\n"
        -- SingleArg _ -> throwError $ DemutationError $ "Found a local mutation followed by a pure value.\n"
        --                                           <> "This makes not much sense since only one of both can currently be processed.\n"
        --                                           <> "---- local mutation ----\n"
        --                                           <> showPretty term1 <> "\n\n"
        --                                           <> "---- pure value ----\n"
        --                                           <> showPretty term2 <> "\n"
        DefaultValue -> pure (newTerm1 , VirtualMutated mutNames1', NoMove)

    -- the first command has only locally mutated variables,
    -- and the second one is a single arg
    -- (VirtualMutated mutNames1', Pure (SingleArg _)) -> do
      -- -- | onlyLocallyMutatedVariables mutNames1' -> do

      -- let mutNames1 = [v | (v, LocalMutation) <- mutNames1']
      -- let ns1 = [n :- JTAny | (n) <- mutNames1]
      --     term = TLet ns1 newTerm1
      --           (
      --               newTerm2
      --           )
      -- pure (term , GloballyPure mutNames1)
      -- pure (newTerm1 , VirtualMutated mutNames1')

    ------------------------------------
    -- GLOBAL & PURE
    -- term1 is globally! mutating
    --
    -- this means that we cannot turn this into a pure term
    -- thus the second term has to be ignored
    (VirtualMutated mutNames1, Pure p) -> do

      case p of
        DefaultValue -> return ()
        _ ->  do warn $ "Found a term which is not a mutating function call in a place where only such calls make sense.\n"
                     <> "The full term is:\n"
                     <> "---------------------------\n"
                     <> "-- type: " <> show (VirtualMutated mutNames1) <> "\n"
                     <> showPretty term1 <> "\n"
                     <> "------------\n"
                     <> "-- type: " <> show (Pure p) <> "\n"
                     <> showPretty term2 <> "\n"
                     <> "---------------------------\n"
          
          
          -- warn ("Found the term " <> showPretty term2
          --            <> " which is not mutating in a place where only mutating terms make sense.\n"
          --            <> " => It has the type " <> show (Pure p) <> "\n"
          --            <> " => In the term:\n" <> parenIndent (showPretty (Extra (MutLet ltype term1 term2))) <> "\n"
          --            <> " => Conclusion: It is ignored in the privacy analysis.")

      -- let mutNames2 = [(v, LocalMutation) | v <- mutNames2']
      --     commonMutNames = nub (mutNames1 <> mutNames2)
      --     ns1 = [n :- JTAny | (n, _) <- mutNames1]

      --     term = TLet ns1 newTerm1
      --           (
      --             Tup ((\(a, _) -> Var (a :- JTAny)) <$> mutNames1)
      --           )
      pure (newTerm1 , VirtualMutated mutNames1, NoMove)

    ------------------------------------
    -- UNSUPPORTED
    -- neither term1 nor term2 are mutating
    (ty1, ty2) -> throwError (DemutationError $ "Encountered a MutLet where the two commands have the following types: " <> show (ty1, ty2)
                                                <> "\nThis is not supported."
                                                <> "\nIn the term:\n" <> showPretty (Extra (MutLet ltype term1 term2)))

                                                -}

elaborateMut scname scope (Extra (MutLoop iters iterVar body)) = do
  -- first, elaborate the iters
  (newIters , newItersType, _) <- elaborateNonmut scname scope iters

  -- now, preprocess the body,
  -- i.e., find out which variables are getting mutated
  -- and change their `SLet`s to `modify!` terms
  (preprocessedBody, modifyVars) <- runPreprocessLoopBody scope iterVar body

  logForce $ "Preprocessed loop body. The modified vars are: " <> show modifyVars
        <> "\nThe body is:\n" <> showPretty preprocessedBody

  -- add the iterator to the scope
  scope' <- safeSetValue scname iterVar (Pure UserValue) scope

  -- backup iter memory location, and create a new one
  oldIterMem <- getValueMaybe iterVar <$> use memCtx
  setMemMaybe iterVar =<< SingleMem <$> allocateMem scname "iter"

  --
  -- [VAR FILTERING/Begin]
  --
  vanames <- getAllKeys <$> use vaCtx
  --

  -- we can now elaborate the body, and thus get the actual list
  -- of modified variables
  (newBody, newBodyType, _) <- elaborateMut scname scope' preprocessedBody

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
  vaCtx %= (\ctx -> foldr (\k ctx -> deleteIfNotOld k ctx) ctx (getAllKeys ctx))
  --

  --
  -- restore old iter memory location,
  -- if there was something
  --
  case (iterVar, oldIterMem) of
    (Just v, Just a) -> memCtx %= (setValue v a)
    _ -> pure ()

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

      let globalMutVars = filter (inScope) mutvars

      let newBodyWithLet = case globalMutVars of
            [globalMutVar] -> SLet (Just globalMutVar :- JTAny) (Var (Just captureVar :- JTAny)) (wrapReorder mutvars globalMutVars newBody)
            globalMutVars -> TLet [(Just v :- JTAny) | v <- globalMutVars] (Var (Just captureVar :- JTAny)) (wrapReorder mutvars globalMutVars newBody)

      let newTerm = Loop newIters (globalMutVars) (iterVar , captureVar) newBodyWithLet

      return (newTerm , VirtualMutated globalMutVars, NoMove)

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


-- the loop-body-preprocessing creates these modify! terms
-- they get elaborated into tlet assignments again.
-- elaborateMut scname scope (Extra (SModify (Nothing :- _) t1)) = throwError (DemutationError $ "Found a nameless variable in a modify term.")
-- elaborateMut scname scope (Extra (SModify (Just v :- _) t1)) = do
--   (newT1, newT1Type, moveType) <- elaborateNonmut scname scope t1
--   return (newT1, VirtualMutated [(v)], SingleMove v)

-- -- We also have tuple modify
-- elaborateMut scname scope (Extra (TModify xs t1)) = do
--   let elabSingle (Just v :- _) = return (v)
--       elabSingle (Nothing :- _) = throwError (DemutationError $ "Found a nameless variable in a tuple modify term.")

--   allElab <- mapM elabSingle xs

--   (newT1, newT1Type, moveType) <- elaborateNonmut scname scope t1
--   -- markMoved moveType
--   return (newT1 , VirtualMutated allElab, NoMove)

elaborateMut scname scope (Extra (MutRet)) = do
  ---------
  -- get mutated variables from the (VA)context

  -- all accessed vars
  avars <- getAllKeyElemPairs <$> (use mutCtx)
  -- mutated memvars with their locality
  let mutMemVars = [(v) | (v, (_, Mutated)) <- avars ]
  mutTeVars <- mapM (reverseMemLookup) mutMemVars

  case mutTeVars of
    [mutTeVar] -> 
        -- a single var is returned as value, not as tuple
        return (Var (Just mutTeVar :- JTAny) , VirtualMutated mutTeVars, NoMove)
    mutTeVars -> 
        -- return all these vars
        return (Tup [Var (Just v :- JTAny) | v <- mutTeVars ] , VirtualMutated mutTeVars, NoMove)

elaborateMut scname scope (Extra (LoopRet xs)) = do
  ---------
  -- get mutated variables from the (VA)context

  -- all accessed vars
  avars <- getAllKeyElemPairs <$> (use mutCtx)
  -- mutated memvars with their locality
  let mutMemVars = [(v) | (v, (_, Mutated)) <- avars ]
  mutTeVars <- mapM (reverseMemLookup) mutMemVars

  let extraMutTeVars = nub $ xs <> mutTeVars

  case extraMutTeVars of
    [extraMutTeVar] -> 
        -- a single var is returned as value, not as tuple
        return (Var (Just extraMutTeVar :- JTAny) , VirtualMutated extraMutTeVars, NoMove)
    extraMutTeVars -> 
        -- return all these vars
        return (Tup [Var (Just v :- JTAny) | v <- extraMutTeVars ] , VirtualMutated extraMutTeVars, NoMove)

elaborateMut scname scope (LastTerm t) = do
  (newTerm, newType, moveType) <- elaborateMut scname scope t
  return (LastTerm (newTerm), newType, moveType)

elaborateMut scname scope (Extra (DefaultRet x)) = do
  (newX,newXType,moveType) <- elaborateNonmut scname scope x
  case newXType of
    -- if the term is pure, then we annotate
    -- it to say that it is default
    Pure a -> return (newX , Pure DefaultValue, moveType)

    -- if it is not pure, it makes not sense
    -- to say that it is default: we keep the actual type
    t -> return (newX , t, moveType)

elaborateMut scname scope term@(Phi cond t1 t2) = do
  --
  -- Concerning moves: We need to backup the MoveCtx,
  -- and run the elaboration on both branches with the same input, 
  -- and then we need to merge them. We further require that
  -- the movetypes of the branches are the same.
  -- (#172)
  --

  ---------
  -- elaborate all subterms

  -- 1st elaborate the condition
  -- (we do not expect any move here)
  (newCond , newCondType, _) <- elaborateNonmut scname scope cond

  -- backup
  originalMoves <- use memCtx

  -- 2nd a) elaborate branch 1
  (newT1 , newT1Type, moveType1) <- elaborateMut scname scope t1
  moves1 <- use memCtx

  -- 2nd b) elaborate branch 2
  memCtx %= (\_ -> originalMoves)
  (newT2 , newT2Type, moveType2) <- elaborateMut scname scope t2
  moves2 <- use memCtx

  -- 
  -- It is only correct to reset the memctx
  -- and not check the movetypes because
  -- phis are preprocessed and their is nothing
  -- after the phi - only the end of the function
  -- in which they are defined.
  -- And at the end of a function the memctx
  -- and movetypes do not play any role. Only 
  -- the mutCtx.

  let newMoves = originalMoves -- moves1 ⋆! moves2
  memCtx %= (\_ -> newMoves)
  -- case moveType1 == moveType2 of
  --   True -> return ()
  --   False -> demutationError $ "The two branches of an if expression do not have the same movetype.\n"
  --                             <> "(" <> show moveType1 <> " /= " <> show moveType2 <> ")\n"
  --                             <> "In the expression\n"
  --                             <> showPretty term

  -- End of move processing
  --
  --------------------------------------

  ----
  -- mutated if case
  let buildMutatedPhi :: [(TeVar)] -> [(TeVar)] -> MTC (DMTerm , ImmutType, MoveType)
      buildMutatedPhi m1 m2 = do
        let globalM1 = [v | (v) <- m1]
        let globalM2 = [v | (v) <- m2]

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
          _ ->     pure $ TLet [(Just v :- JTAny) | (v) <- m1] newT1 (Tup [Var (Just v :- JTAny) | (v) <- mutvars])

        unifiedT2 <- case globalM2 of
          [] -> do warn ("Found the term " <> showPretty t2
                         <> " which does not mutate any function arguments in the second branch of a mutating if expression.\n"
                         <> " => In the term:\n" <> parenIndent (showPretty term) <> "\n"
                         <> " => Conclusion: This computated value is not allowed to be used in the computation, \nand accordingly, it is ignored in the privacy analysis.")
                   pure $ (Tup [Var (Just v :- JTAny) | (v) <- mutvars])
          _ ->     pure $ TLet [(Just v :- JTAny) | (v) <- m2] newT2 (Tup [Var (Just v :- JTAny) | (v) <- mutvars])

        return (Phi newCond unifiedT1 unifiedT2 , VirtualMutated ([(v) | v <- mutvars]), moveType1)

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
    (_, _) -> return (Phi newCond newT1 newT2 , Pure UserValue, moveType1)

----
-- Demutation of vector / matrix likes
--
-- We return the type `SingleRef`, as that is not allowed
-- to be passed in mutating positions, which is important
-- since the results of these functions are aliased references
-- to matrices.
--
-- See #183.
--

elaborateMut scname scope (Index t1 t2 t3) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname scope t1
  (newT2, newT2Type, _) <- elaborateNonmut scname scope t2
  (newT3, newT3Type, _) <- elaborateNonmut scname scope t3
  return (Index newT1 newT2 newT3 , Pure UserValue, RefMove)
elaborateMut scname scope (VIndex t1 t2) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname scope t1
  (newT2, newT2Type, _) <- elaborateNonmut scname scope t2
  return (VIndex newT1 newT2 , Pure UserValue, RefMove)
elaborateMut scname scope (Row t1 t2) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname scope t1
  (newT2, newT2Type, _) <- elaborateNonmut scname scope t2
  return (Row newT1 newT2, Pure UserValue, RefMove)



----
-- the mutating builtin cases

elaborateMut scname scope (SubGrad t1 t2) = do
  (argTerms, mutVars) <- elaborateMutList "subgrad" scname scope [(Mutated , t1), (NotMutated , t2)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1, newT2] -> pure (SubGrad newT1 newT2, Pure UserValue)
    [newT1, newT2] -> pure (SubGrad newT1 newT2, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (ScaleGrad scalar grads) = do
  (argTerms, mutVars) <- elaborateMutList "scalegrad" scname scope [(NotMutated , scalar), (Mutated , grads)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1, newT2] -> pure (ScaleGrad newT1 newT2, Pure UserValue)
    [newT1, newT2] -> pure (ScaleGrad newT1 newT2, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (ClipM c t) = do
  (argTerms, mutVars) <- elaborateMutList "clip" scname scope [(Mutated , t)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT] -> pure (ClipM c newT, Pure UserValue)
    [newT] -> pure (ClipM c newT, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (MutGauss t1 t2 t3 t4) = do
  (argTerms, mutVars) <- elaborateMutList "gauss" scname scope [(NotMutated , t1), (NotMutated , t2), (NotMutated , t3), (Mutated , t4)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1, newT2, newT3, newT4] -> pure (Gauss newT1 newT2 newT3 newT4, Pure UserValue)
    [newT1, newT2, newT3, newT4] -> pure (Gauss newT1 newT2 newT3 newT4, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (MutLaplace t1 t2 t3) = do
  (argTerms, mutVars) <- elaborateMutList "laplace" scname scope [(NotMutated , t1), (NotMutated , t2), (Mutated , t3)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1, newT2, newT3] -> pure (Gauss newT1 newT2 newT3, Pure UserValue)
    [newT1, newT2, newT3] -> pure (Laplace newT1 newT2 newT3, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (ConvertM t1) = do
  (argTerms, mutVars) <- elaborateMutList "convert" scname scope [(Mutated , t1)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1] -> pure (ConvertM newT1, Pure UserValue)
    [newT1] -> pure (ConvertM newT1, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (Transpose t1) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname scope t1
  return (Transpose newT1 , Pure UserValue, NoMove)

-- the non mutating builtin cases
elaborateMut scname scope (Ret t1) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname scope t1
  return (Ret newT1 , Pure UserValue, NoMove)
elaborateMut scname scope (Tup t1s) = do
  results <- mapM (elaborateNonmut scname scope) t1s
  let makeSureIsPure (_,Pure b,_) = pure b
      makeSureIsPure (_,b,c)      = demutationError $ "Expected to have a pure term, but got the type " <> show b <> "instead"

  let terms = [t1 | (t1, _, _) <- results]
  let moves = [t3 | (_, _, t3) <- results]
  itypes <- mapM makeSureIsPure results 
  return (Tup terms , Pure (PureTuple itypes), TupleMove moves)

elaborateMut scname scope (MCreate t1 t2 t3 t4) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname scope t1
  (newT2, newT2Type, _) <- elaborateNonmut scname scope t2
  (newT4, newT4Type, _) <- elaborateNonmut scname scope t4
  return (MCreate newT1 newT2 t3 newT4 , Pure UserValue, NoMove)
elaborateMut scname scope (Size t1) = do
  (newT1, newT1Type, _) <- elaborateMut scname scope t1
  return (Size newT1, Pure UserValue, NoMove)
elaborateMut scname scope (Length t1) = do
  (newT1, newT1Type, _) <- elaborateMut scname scope t1
  return (Length newT1, Pure UserValue, NoMove)
elaborateMut scname scope (ZeroGrad t1) = do
  (newT1, newT1Type, _) <- elaborateMut scname scope t1
  return (ZeroGrad newT1, Pure UserValue, NoMove)
elaborateMut scname scope (SumGrads t1 t2) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname scope t1
  (newT2, newT2Type, _) <- elaborateNonmut scname scope t2
  return (SumGrads newT1 newT2, Pure UserValue, NoMove)
elaborateMut scname scope (Sample t1 t2 t3) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname scope t1
  (newT2, newT2Type, _) <- elaborateNonmut scname scope t2
  (newT3, newT3Type, _) <- elaborateNonmut scname scope t3
  return (Sample newT1 newT2 newT3 , Pure UserValue, NoMove)
elaborateMut scname scope (InternalExpectConst t1) = do
  (newT1, newT1Type, _) <- elaborateMut scname scope t1
  return (InternalExpectConst newT1, Pure UserValue, NoMove)
elaborateMut scname scope (DeepcopyValue t1) = do
  (newT1, newT1Type, _) <- elaborateMut scname scope t1
  return (DeepcopyValue newT1, Pure UserValue, NoMove)
elaborateMut scname scope (Gauss t1 t2 t3 t4) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname scope t1
  (newT2, newT2Type, _) <- elaborateNonmut scname scope t2
  (newT3, newT3Type, _) <- elaborateNonmut scname scope t3
  (newT4, newT4Type, _) <- elaborateNonmut scname scope t4
  return (Gauss newT1 newT2 newT3 newT4 , Pure UserValue, NoMove)
elaborateMut scname scope (Laplace t1 t2 t3) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname scope t1
  (newT2, newT2Type, _) <- elaborateNonmut scname scope t2
  (newT3, newT3Type, _) <- elaborateNonmut scname scope t3
  return (Laplace newT1 newT2 newT3 , Pure UserValue, NoMove)
elaborateMut scname scope (AboveThresh t1 t2 t3 t4) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname scope t1
  (newT2, newT2Type, _) <- elaborateNonmut scname scope t2
  (newT3, newT3Type, _) <- elaborateNonmut scname scope t3
  (newT4, newT4Type, _) <- elaborateNonmut scname scope t4
  return (AboveThresh newT1 newT2 newT3 newT4 , Pure UserValue, NoMove)

-- the unsupported terms
elaborateMut scname scope term@(Choice t1)        = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname scope term@(Loop t1 t2 t3 t4) = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname scope term@(Reorder t1 t2)    = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname scope term@(TProject t1 t2)   = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname scope term@(Arg x a b)        = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname scope term@(BBApply x a b)    = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))





---------------------------------------------------
-- recurring utilities



-------------
-- elaborating a lambda term
--

elaborateLambda :: ScopeVar -> Scope -> [Asgmt JuliaType] -> MutDMTerm -> MTC (DMTerm , ImmutType)
elaborateLambda scname scope args body = do
  --
  -- Regarding Movetypes: We do not need to do anything here
  -- about them, because we make sure in typechecking that
  -- the return value of a function needs to be copied,
  -- if it is of a type containing references.
  -- Thus the move type of the body is irrelevant.
  --
  -- See #171.
  --


  -- 
  -- NO. Different since #185.
  -- ## First, backup the VA-Ctx to be able to restore those
  -- ## variables which have the same name as our arguments
  -- ##
  -- ## See https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/148#issuecomment-1004950955
  -- ##
  -- ## Then, mark all function arguments as "SingleRead"
  -- ## for the current scope.
  oldVaCtx <- use vaCtx
  mapM (markReadOverwritePrevious scname) [a | (Just a :- _) <- args]
  -- ##
  -- END NO.
  --
  -- Allocate new memory for the arguments.
  let arghint (Just x :- _) = T.pack $ "arg_" <> show x
      arghint (_ :- _)      = T.pack $ "anon-arg"
  argMemVars <- mapM (allocateMem scname) (arghint <$> args)
  -- combine with var names
  let argsWithMemVars = zip args argMemVars
  -- assign memory to variables
  mapM (\(x :- _,a) -> setMemMaybe x (SingleMem a)) argsWithMemVars


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

  -- check the body
  (newBody,τ,moveType) <- elaborateMut scname scope' body

  -- get the context and check if some variables are now mutated
  ctx <- use vaCtx
  let ctxElems = getAllElems ctx
  -- let isMutatingFunction = or [True | WriteSingle _ <- ctxElems]

  -- restore the VA-Types of the arguments to this lambda from the backup'ed `oldVaCtx`
  -- and also get their new values
  let getVar :: (Asgmt JuliaType,MemVar) -> MTC (Maybe (TeVar, IsMutated))
      getVar (Just a :- t,memvar) = do
        mstate <- use mutCtx
        case getValue memvar mstate of
          Nothing              -> pure (Just (a , NotMutated))
          Just (_, Mutated) -> pure (Just (a , Mutated))
          Just _               -> pure (Just (a , NotMutated))
      getVar (Nothing :- t,_) = pure Nothing

  -- call this function on all args given in the signature
  -- and extract those vars that are mutated
  vars_mutationState <- mapM getVar argsWithMemVars
  let mutVars = [v | Just (v , Mutated) <- vars_mutationState]
  let mutationsStates = [m | Just (_ , m) <- vars_mutationState]

  --  
  -- delete all memory variables for this scope
  --
  cleanupMem scname

  -----------
  -- Restore old VA state for all args
  -- (https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/148#issuecomment-1004950955)
  --
  vactxBeforeRestoration <- use vaCtx
  let restoreArg tevar = do
        case getValue tevar oldVaCtx of
          Nothing -> vaCtx %%= (\ctx -> ((), deleteValue tevar ctx))
          Just (oldva, oldscname) -> vaCtx %%= (\ctx -> ((), setValue tevar (oldva, oldscname) ctx))
  mapM restoreArg [a | (Just a :- _) <- args]
  --
  -----------


  -- now, depending on whether we have a mutating lambda,
  -- do the following

  -- case isMutatingFunction of
    --
    -- case I : Mutating
    --
    -- True -> do
      -- assert that now the context is empty
      -- (i.e., no captures were used)
      -- vaCtx <- use vaCtx
      -- case isEmptyDict vaCtx of
      --   False -> throwError (DemutationDefinitionOrderError $ "The variables " <> show vaCtx <> " are not in scope.")
      --   True ->
          -- check that the body is a mutation result
          -- and reorder the resulting tuple
          --
  case (τ,mutVars) of
    (VirtualMutated returnedMutVars, expectedMutVars) | expectedMutVars /= [] -> do 
      -- [v | (v,NotLocalMutation) <- vars] /= [] -> do

      -- get the permutation which tells us how to go
      -- from the order in which the vars are returned by the body
      -- to the order in which the lambda arguments are given
      --

      -- NOTE: WIP/test -v-
      -- we also check that there is not a mixture of local/nonlocal mutated variable
      -- let bothVars = [(v) | (v, NotLocalMutation) <- vars , (w,LocalMutation) <- vars, v == w]
      -- case bothVars of
      --   [] -> pure ()
      --   xs -> throwError (DemutationError $ "The variable names " <> show xs <> " are used for both locally mutated and not locally mutated things. This is not allowed. ")

      -- NOTE: WIP/test -v-
      -- let vars' = [v | (v , NotLocalMutation) <- vars]
      let mutVars' = [(v , NotLocalMutation) | v <- mutVars]

      -- logForce $ "Found permutation " <> show vars <> " ↦ " <> show mutVars <>". It is: " <> show σ
      pure ((wrapReorder expectedMutVars returnedMutVars newBody) , Mutating mutationsStates)

    --
    -- case II : Not Mutating
    --
    -- simply say that this function is not mutating
    (Pure _,[]) -> pure (newBody , Pure UserValue)

    --
    -- case III : locally mutating without return value
    --
    -- this is not allowed
    -- (VirtualMutated vars, [])
    --   -> throwError (DemutationError $ "Found a function which is neither mutating, nor has a return value. This is not allowed."
    --                                    <> "\nThe function type is: " <> show (VirtualMutated vars)
    --                                    <> "\nThe function is:\n" <> showPretty body)

    wrongτ -> throwError (DemutationError $ "Expected the result of the body of a mutating lambda to be a virtual mutated value. But it was "
                          <> show wrongτ <> "\n where body is:\n" <> showPretty body)


-------------
-- elaborating a list of terms which are used in individually either mutating, or not mutating places
--

elaborateMutList :: String -> ScopeVar -> Scope -> [(IsMutated , MutDMTerm)] -> MTC ([DMTerm] , [TeVar])
elaborateMutList f scname scope mutargs = do
  ---------------------------------------
  -- Regarding MoveTypes (#171)
  --
  -- Since functions make sure that they do not reassign terms
  -- passed in at non-mutating argument positions, the movetype 
  -- of these terms is irrelevant.
  -- The "movetype" of terms in mutating argument positions is easy:
  -- It needs to be a SingleArg term, thus we do not really need
  -- to look into the official `MoveType`.
  --


  -- function for typechecking a single argument
  let checkArg :: (IsMutated , MutDMTerm) -> MTC (DMTerm , ImmutType, Maybe (TeVar))
      checkArg (Mutated , arg) = do
        -- if the argument is given in a mutable position,
        -- it _must_ be a var
        case arg of
          (Var (Just x :- a)) -> do 
            -- say that this variable is being reassigned (VAT)
            markReassigned scname x

            -- get the memvar of this tevar from the memctx
            -- and say that the memory location is
            -- mutated
            mt <- expectSingleMem =<< expectNotMoved x
            markMutated mt

            return (Var (Just x :- a), Pure (SingleArg x), Just x)
            -- this one needs to be a single arg
            {-
            -- get the type of this var from the scope
            -- this one needs to be a single arg
            case getValue x scope of
              Nothing -> logForce ("The scope is" <> show scope) >> throwError (DemutationDefinitionOrderError x)
              Just (Pure (SingleArg y)) | x == y -> do
                debug $ "[elaborateMutList]: The non-local variable " <> show y <> " is being mutated."
                loc <- markReassigned scname NotLocalMutation y
                return (Var (Just x :- a) , Pure (SingleArg x), Just (x, loc))
              Just (Pure (SingleArg y)) -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the variable " <> show x <> " as argument in a mutable-argument-position. It is bound to the function argument " <> show y <> ", but it is not allowed to use renamed function arguments in such a position.")
              Just (Pure (SingleArgPart y)) -> demutationError $ "When calling the mutating function " <> f <> " found the variable " <> show x <> " as argument in a mutable-argument-position. It is a (tuple-)part of the function argument "
                                                          <> show y <> ", and it is not allowed to mutate parts of arguments.\n"
                                                          <> "If you want to mutate " <> show x <> " you need to pass it in as a seperate argument to the function."
              Just (Pure (SingleRef)) -> demutationError $ "When calling the mutating function " <> f <> " found the variable " <> show x <> " as argument in a mutable-argument-position. It is a reference to a part of a vector or matrix."
                                                          <> "It is not allowed to mutate matrices or vectors.\n"
              Just (Pure _) -> do
                loc <- markReassigned scname LocalMutation x
                return (Var (Just x :- a) , Pure (SingleArg x), Just (x, loc))
              Just res -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the variable " <> show x <> " as argument in a mutable-argument-position. It has the type " <> show res <> ", which is not allowed here.")

          (Var (Nothing :- a)) -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the term " <> showPretty arg <> " as argument in a mutable-argument-position. Only named variables are allowed here.")
          -}

          -- if argument is not a var, throw error
          _ -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the term " <> showPretty arg <> " as argument in a mutable-argument-position. Only variables are allowed here.")

      checkArg (NotMutated , arg) = do
        -- if the argument is given in an immutable position,
        -- we allow to use the full immut checking
        (arg' , τ, _) <- elaborateMut scname scope arg

        -- we require the argument to be of pure type
        case τ of
          Pure _ -> pure ()
          Mutating _ -> throwError (DemutationError $ "It is not allowed to pass mutating functions as arguments. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")
          VirtualMutated _ -> throwError (DemutationError $ "It is not allowed to use the result of mutating functions as arguments in other mutating functions. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")
          PureBlackBox -> throwError (DemutationError $ "It is not allowed to pass black boxes as arguments. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")

        return (arg' , τ, Nothing)

  -- check them
  newArgsWithMutTeVars <- mapM checkArg mutargs

  ------------------------- 
  -- extract for return
  --
  -- these types of the arguments carry the contained "possibly aliased variable names"
  let newArgs = [te | (te , _, _) <- newArgsWithMutTeVars]
  let argTypes = [ty | (_ , Pure ty, _) <- newArgsWithMutTeVars]
  let mutVars = [m | (_ , _, Just m) <- newArgsWithMutTeVars]


  --
  -- Make sure that all variables in mutated argument positions are not aliased.
  -- For this we look at the types of the inputs.
  --
  -- See #95
  --
  let getPossiblyAliasedVars (SingleArg a) = [a]
      getPossiblyAliasedVars (SingleArgPart a) = [a]
      -- getPossiblyAliasedVars (SingleRef) = []
      getPossiblyAliasedVars (PureTuple as) = getPossiblyAliasedVars =<< as
      getPossiblyAliasedVars DefaultValue = []
      getPossiblyAliasedVars UserValue = []

  -- let allVars = [t | (t, _) <- newArgsWithMutTeVars] >>= freeVarsDMTerm
  let allVars = [t | (t) <- mutVars]

  -- Counting how many vars with a given name there are
  let addCount :: (TeVar) -> Ctx TeVar Int -> Ctx TeVar Int
      addCount var counts = case getValue var counts of
                              Just a -> setValue var (a P.+ 1) counts
                              Nothing -> setValue var 1 counts

  -- number of occurences of all variables
  let varcounts = getAllKeyElemPairs $ foldr addCount def (getPossiblyAliasedVars =<< argTypes)
  -- number of occurences of all variables, but only for variables which are mutated
  let mutvarcounts = filter (\(k,n) -> k `elem` (mutVars)) varcounts
  -- number of occurences of all variables, but only for variables which are mutated, with occurence > 1
  let wrongVarCounts = filter (\(k,n) -> n > 1) mutvarcounts

  -- make sure that such variables do not occur
  case wrongVarCounts of
    [] -> return ()
    xs -> throwError $ DemutationNonAliasedMutatingArgumentError
                     $ "The function '" <> f <> "' is called with the following vars in mutating positions:\n\n"
                        <> showvarcounts mutvarcounts <> "\n"
                        <> "But it is not allowed to have the same variable occur multiple times "
                        where showvarcounts ((name,count):rest) = " - variable `" <> show name <> "` occurs " <> show count <> " times." <> "\n"
                                                                  <> showvarcounts rest
                              showvarcounts [] = ""

  return (newArgs, mutVars)



------------------------------------------------------------
-- preprocessing a for loop body

runPreprocessLoopBody :: Scope -> Maybe TeVar -> MutDMTerm -> MTC (MutDMTerm, [TeVar])
runPreprocessLoopBody scope iter t = do
  (a,x) <- runStateT (preprocessLoopBody scope iter t) def
  return (a, nub x)

-- | Walks through the loop term and changes SLet's to `modify!`
--   calls if such a variable is already in scope.
--   Also makes sure that the iteration variable `iter` is not assigned,
--   and that no `FLet`s are found.
--   Returns the variables which were changed to `modify!`.
preprocessLoopBody :: Scope -> Maybe TeVar -> MutDMTerm -> StateT [TeVar] MTC MutDMTerm

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
  -- let newVars = nub (termVars <> bodyVars)

  case v of
    Just v -> case getValue v scope of
      Just _ -> state (\a -> ((), a <> [v])) 
      Nothing -> pure ()
    Nothing -> pure ()

  (body') <- preprocessLoopBody scope iter body
  return (SLetBase ltype (v :- jt) term' body')


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

  -- we collect those values of vs for which there is something in the scope
  let vs_in_scope = [v | (Just v :- _) <- vs, (Just _) <- [getValue v scope]]


  state (\a -> ((), a <> vs_in_scope))

  body' <- preprocessLoopBody scope iter body
  return (TLet vs term' body')

preprocessLoopBody scope iter (FLet f _ _) = throwOriginalError (DemutationError $ "Function definition is not allowed in for loops. (Encountered definition of " <> show f <> ".)")
preprocessLoopBody scope iter (Ret t) = throwOriginalError (DemutationError $ "Return is not allowed in for loops. (Encountered " <> show (Ret t) <> ".)")

-- mutlets make us recurse
preprocessLoopBody scope iter (Extra (MutLet mtype t1 t2)) = do
  (t1') <- preprocessLoopBody scope iter t1
  (t2') <- preprocessLoopBody scope iter t2
  return (Extra (MutLet mtype t1' t2'))

preprocessLoopBody scope iter (Extra (DefaultRet a)) = do
  captureVars <- get
  lift $ debug $ "[preprocessLoopBody]: default ret in loop, building loopret with captures: " <> show captureVars
  return $ Extra $ LoopRet captureVars

preprocessLoopBody scope iter (Extra (MutRet)) = do
  captureVars <- get
  lift $ debug $ "[preprocessLoopBody]: mutret in loop, building loopret with captures: " <> show captureVars
  return $ Extra $ LoopRet captureVars

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

-- If we have found our final `in` term (which is also allowed to be an slet),
-- check that the tuple is correct
replaceTLetIn αs replacement (SLet β t1 (Tup t2s)) =

  let isvar :: (Maybe TeVar, DMTerm) -> Bool
      isvar (v, Var (w :- _)) | v == w = True
      isvar _ = False

  in case and (isvar <$> zip αs t2s) of
    -- if it does fit our pattern, replace by a single TLet
    -- and recursively call ourselves again
    True -> Just (SLet β t1 replacement)

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






