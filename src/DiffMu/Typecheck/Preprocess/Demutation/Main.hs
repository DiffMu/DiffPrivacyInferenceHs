
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

import Control.Monad.Trans.Class
import qualified GHC.RTS.Flags as LHS
import Control.Exception (throw)




  
demutTLetStatement :: LetKind -> [ProcVar] -> DemutDMTerm -> TermType
demutTLetStatement ltype vars term =
  (Statement (Extra (DemutTLetBase ltype ([(procVarAsTeVar v) :- JTAny | v <- vars ]) term))
          (TupleMove [SingleMove v | v <- vars]))

---
-- elaborating loops
-- not allowed:
-- - FLet
-- - JuliaReturn
-- - modify iteration variable

demutate :: ProcDMTerm -> MTC (DemutDMTerm)
demutate term = do
  -- logForce $ "Term before phi rearranging:\n" <> showPretty term

  -- term' <- rearrangePhi term

  -- logForce $ "-----------------------------------"
  logForce $ "Term before mutation elaboration:\n" <> showPretty term

  topscname <- newScopeVar "toplevel"

  res <- elaborateTopLevel topscname term
  let resterm = termTypeAsTerm res
  logForce $ "-----------------------------------"
  logForce $ "Mutation elaborated term is:\n" <> showPretty resterm

  -- let optimized = optimizeTLet res
  -- logForce $ "-----------------------------------"
  -- logForce $ "TLet optimized term is:\n" <> showPretty optimized

  return resterm


elaborateValue :: ScopeVar -> ProcDMTerm -> MTC (ImmutType , MoveType)
elaborateValue scname te = do
  (te1type) <- elaborateMut scname te
  case te1type of
    Statement _ _ -> demutationError $ "Expected term to be a value, but it was a statement:\n" <> showPretty te
    Value it mt -> return (it , mt)
    MutatingFunctionEnd -> demutationError $ "Expected term to be a value, but it was a return."

elaboratePureValue :: ScopeVar -> ProcDMTerm -> MTC (MoveType)
elaboratePureValue scname te = do
  (te1type) <- elaborateMut scname te
  case te1type of
    Statement _ _   -> demutationError $ "Expected term to be a value, but it was a statement:\n" <> showPretty te
    MutatingFunctionEnd -> demutationError $ "Expected term to be a value, but it was a return."
    Value Pure mt -> return (mt)
    Value _ mt    -> demutationError $ "Expected term to be a pure value, but it has type: " <> show mt
                                    <> "The term is:\n"
                                    <> showPretty te



-- make sure there are no Value or MutatingFunctionEnd inside the blocks
-- reverse the block statements
-- concatenate Statements blocks
-- determine the correct LastTerm for the concatenation result
makeTermList :: [TermType] -> MTC (LastValue, [DemutDMTerm])

-- empty list
makeTermList [] = demutationError $ "Found an empty list of statements."

-- single element left
makeTermList (Value it mt : [])         = case it of
                                            Pure -> return (PureValue mt, [moveTypeAsTerm mt])
                                            _    -> demutationError $ "The last value of a block has the type " <> show it <> "\n"
                                                                    <> "Only pure values are allowed.\n"
                                                                    <> "The value is:\n"
                                                                    <> show mt
makeTermList (Statement term last : []) = return (PureValue last, [moveTypeAsTerm last, term])
makeTermList (MutatingFunctionEnd : []) = return (MutatingFunctionEndValue , [])

-- more than one element left
makeTermList (Value _ mt : ts)          = demutationError $ "Found a value term " <> show mt <> " inside a list of statements."
makeTermList (Statement term _ : ts)    = do (last, ts') <- makeTermList ts
                                             return (last, ts' <> [term])
makeTermList (MutatingFunctionEnd : ts) = demutationError $ "Found a MutatingFunctionEnd inside a list of statements."

  
-- 
-- Here we allow moving return types
--
elaborateTopLevel :: ScopeVar -> ProcDMTerm -> MTC (TermType)
elaborateTopLevel scname (Extra (Block ts)) = do
  ts' <- mapM (elaborateMut scname) ts
  (last_val, ts'') <- makeTermList ts'

  mt <- case last_val of
    PureValue mt -> return mt
    MutatingFunctionEndValue -> demutationError $ "Encountered a 'return' which is not the last statement of a function."

  -- case mt of
  --   NoMove pdt -> pure ()
  --   _ -> demutationError $ "Encountered a block which is not top level and not in a function, but has a move as return type. This is currently not allowed."

  return (Value Pure (NoMove (Extra (DemutBlock ts''))))

elaborateTopLevel scname t = elaborateMut scname t


-- 
-- The main elaboration function
--
elaborateMut :: ScopeVar -> ProcDMTerm -> MTC (TermType)

elaborateMut scname (Extra (Block ts)) = do
  ts' <- mapM (elaborateMut scname) ts
  (last_val, ts'') <- makeTermList ts'

  mt <- case last_val of
    PureValue mt -> return mt
    MutatingFunctionEndValue -> demutationError $ "Encountered a 'return' which is not the last statement of a function."

  case mt of
    NoMove pdt -> pure ()
    _ -> demutationError $ "Encountered a block which is not top level and not in a function, but has a move as return type. This is currently not allowed."

  return (Value Pure (NoMove (Extra (DemutBlock ts''))))
    
elaborateMut scname (Op op args) = do
  args' <- mapM (elaboratePureValue scname) args
  pure (Value Pure (NoMove (Op op (moveTypeAsTerm <$> args'))))

elaborateMut scname (Sng η τ) = do
  return (Value Pure (NoMove $ Sng η τ))

elaborateMut scname term@(Var _) = demutationError $ "Unsupported term: " <> showPretty term

elaborateMut scname (Extra (ProcVarTerm (x ::- j))) = do
  mx <- expectNotMoved x
  itype <- expectImmutType scname x

  return (Value itype (SingleMove x))

elaborateMut scname (Extra (ProcBBLet procx args)) = do

  -- write the black box into the scope with its type
  scope'  <- setImmutType scname procx PureBlackBox

  -- allocate a memory location
  memx <- allocateMem scname (Left procx)

  -- write it into the memctx
  setMem procx [(SingleMem memx)]

  let tevarx = procVarAsTeVar procx

  return (Statement (Extra (DemutBBLet tevarx args)) (SingleMove procx))


elaborateMut scname (Extra (ProcSLetBase ltype (x ::- τ) term)) = do

  (newTermType, moveType) <- elaborateValue scname term

  case newTermType of
    Pure -> pure ()
    Mutating _ -> pure ()
    PureBlackBox     -> throwError (DemutationError $ "Found an assignment " <> show x <> " = " <> showPretty term <> " where RHS is a black box. This is not allowed.")

  --
  -- move out of variables on the RHS, getting the memory
  -- locations, and the new allocations, then:
  --
  -- 1. set memory locations for variables on the LHS
  -- 2. generate terms for the memory allocations
  -- 
  (mem) <- moveGetMem scname moveType
  setMem x mem

  -- write the immut type into the scope
  setImmutType scname x newTermType

  -- log what happened
  debug $ "[elaborateMut/SLetBase]: The variable " <> show x <> " is being assigned." 
  logmem <- use memCtx
  debug $ "The memctx is now:\n"
  debug $ show logmem


  return (Statement (Extra (DemutSLetBase ltype ((procVarAsTeVar x) :- τ) (moveTypeAsTerm moveType)))
          (SingleMove x))



elaborateMut scname fullterm@(Extra (ProcTLetBase ltype vars term)) = do

  (newTermType, moveType) <- elaborateValue scname term

  --
  -- deal with itype
  --
  -- What we additionally assume is that elements of tuples
  -- are always pure. (TODO: We have to check this in tuple creation terms)
  --
  case newTermType of
    Pure -> pure ()
    Mutating ims -> throwError (DemutationError $ "Found a tuple assignment " <> show vars <> " = " <> showPretty term <> " where RHS is a mutating function. This is not allowed.")
    PureBlackBox -> throwError (DemutationError $ "Found an assignment " <> show vars <> " = " <> showPretty term <> " where RHS is a black box. This is not allowed.")
  --
  -- we set the immuttype of every element on the LHS to Pure
  --
  mapM (\(x ::- _) -> setImmutType scname x Pure) vars

  -- get memory of the RHS
  mem <- moveGetMem scname moveType

  -- write the list of possible memory types into the
  -- variables of the lhs
  setMemTupleInManyMems scname ([v | (v ::- _) <- vars]) mem

  return $ demutTLetStatement ltype [v | (v ::- _) <- vars] (moveTypeAsTerm moveType)



elaborateMut scname (Extra (ProcLamStar args body)) = do
  bodyscname <- newScopeVar "lamstar"
  (newBody, newBodyType) <- elaborateLambda bodyscname [(v ::- x) | (v ::- (x , _)) <- args] body
  return (Value newBodyType (NoMove (LamStar [(procVarAsTeVar v) :- x | (v ::- x) <- args] newBody)))

elaborateMut scname (Extra (ProcLam args body)) = do
  bodyscname <- newScopeVar "lam"
  (newBody, newBodyType) <- elaborateLambda bodyscname [(v ::- x) | (v ::- x) <- args] body
  return (Value newBodyType (NoMove (Lam [(procVarAsTeVar v) :- x | (v ::- x) <- args] newBody)))



elaborateMut scname (Extra (ProcFLet name term)) = do
  --
  -- Regarding MoveType: it is not possible to have terms
  -- where an flet is followed by something movable, i.e.
  -- a variable. Because FLets are only generated when they
  -- are actually followed by an (anonymous) function definition.
  -- Which means that we do not have to mark anything as moved here.
  --

  (newTermType, moveType) <- elaborateValue scname term

  case newTermType of
    Pure -> pure ()
    Mutating _ -> pure ()
    PureBlackBox     -> internalError $ "Found a BlackBox term inside a BlackBox term, this should not be possible."

  term' <- case moveType of
                NoMove t -> return t
                _ -> internalError $ "got a move from the FLet body, this should not happen"

  -- create memory location for function name
  mem <- allocateMem scname (Right "val")
  setMem name [(SingleMem mem)]

  -- write the immut type into the scope
  setImmutTypeFLetDefined scname name newTermType

  -- log what happened
  debug $ "[elaborateMut/FLetBase]: The function " <> show name <> " is being defined."
  logmem <- use memCtx
  debug $ "The memctx is now:\n"
  debug $ show logmem

  return (Statement (Extra (DemutFLet (procVarAsTeVar name) term')) (SingleMove name))

  

elaborateMut scname (Apply f args) = do
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
  (itype , movetype) <- elaborateValue scname f

  --------
  -- 2 cases
  --
  case itype of
    --
    -- case I : A mutating function call
    --
    Mutating muts -> do
        -- make sure that there are as many arguments as the function requires
        case length muts == length args of
          True -> pure ()
          False -> throwError (DemutationError $ "Trying to call the function '" <> showPretty f <> "' with a wrong number of arguments.")

        let mutargs = zip muts args
        (newArgs , muts) <- elaborateMutList (showPretty f) scname mutargs

        let funcallterm = (Apply (moveTypeAsTerm movetype) newArgs)

        -- the new term
        return $ demutTLetStatement PureLet muts funcallterm

    --
    -- case II : A pure function call
    --
    Pure -> do
        let mutargs = zip (repeat NotMutated) args
        (newArgs , muts) <- elaborateMutList (showPretty f) scname mutargs

        let funcallterm = (Apply (moveTypeAsTerm movetype) newArgs)

        -- the new term
        return $ Value Pure (NoMove funcallterm)

    --
    -- case III: A call to a pure black box
    --
    PureBlackBox -> do
        -- the global variables which are implicitly applied
        -- and need to be added to the `BBApply`
        glvars <- globalNames <$> (use topLevelInfo)

        -- since the box is pure, we say so to `elaborateMutList`
        let mutargs = zip (repeat NotMutated) args
        (newArgs , muts) <- elaborateMutList (showPretty f) scname mutargs

        return $ Value Pure (NoMove (BBApply (moveTypeAsTerm movetype) newArgs (procVarAsTeVar <$> glvars)))





elaborateMut scname (Extra (ProcPreLoop iters iterVar body)) = demutationError $ "Not implemented: loop." -- do
{-
  -- first, elaborate the iters
  (newIters , newItersType, _) <- elaborateNonmut scname iters

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
  (newBody, newBodyType, _) <- elaborateMut scname' preprocessedBody

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
-- elaborateMut scname (Extra (SModify (Nothing :- _) t1)) = throwError (DemutationError $ "Found a nameless variable in a modify term.")
-- elaborateMut scname (Extra (SModify (Just v :- _) t1)) = do
--   (newT1, newT1Type, moveType) <- elaborateNonmut scname t1
--   return (newT1, VirtualMutated [(v)], SingleMove v)

-- -- We also have tuple modify
-- elaborateMut scname (Extra (TModify xs t1)) = do
--   let elabSingle (Just v :- _) = return (v)
--       elabSingle (Nothing :- _) = throwError (DemutationError $ "Found a nameless variable in a tuple modify term.")

--   allElab <- mapM elabSingle xs

--   (newT1, newT1Type, moveType) <- elaborateNonmut scname t1
--   -- markMoved moveType
--   return (newT1 , VirtualMutated allElab, NoMove)

elaborateMut scname (Extra (MutRet)) = do
  ---------
  -- get mutated variables from the (VA)context

  -- all accessed vars
  avars <- getAllKeyElemPairs <$> (use mutCtx)
  -- mutated memvars with their locality
  let mutMemVars = [(v) | (v, (_, Mutated)) <- avars ]
  mutTeVars <- mapM (reverseMemLookup) mutMemVars

  -- a single var is returned as value, not as tuple
  return (buildCopyReturnValue mutTeVars, VirtualMutated mutTeVars, NoMove)

-}



elaborateMut scname (LastTerm t) = demutationError "not implemented: last term" -- do
  -- (newTerm, newType, moveType) <- elaborateMut scname t
  -- return (LastTerm (newTerm), newType, moveType)


elaborateMut scname term@(Extra (ProcPhi cond ts)) = demutationError "not implemented: phi" -- do
  {-
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
  (newCond , newCondType, _) <- elaborateNonmut scname cond

  -- backup
  originalMoves <- use memCtx

  -- 2nd a) elaborate branch 1
  (newT1 , newT1Type, moveType1) <- elaborateMut scname t1
  moves1 <- use memCtx

  -- 2nd b) elaborate branch 2
  memCtx %= (\_ -> originalMoves)
  (newT2 , newT2Type, moveType2) <- elaborateMut scname t2
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
                   pure $ buildReturnValue mutvars
          _ ->     pure $ case m1 of
                            [m1] -> SLet (Just m1 :- JTAny)            newT1 (buildReturnValue mutvars)
                            m1   -> TLet [(Just v :- JTAny) | v <- m1] newT1 (buildReturnValue mutvars)

        unifiedT2 <- case globalM2 of
          [] -> do warn ("Found the term " <> showPretty t2
                         <> " which does not mutate any function arguments in the second branch of a mutating if expression.\n"
                         <> " => In the term:\n" <> parenIndent (showPretty term) <> "\n"
                         <> " => Conclusion: This computated value is not allowed to be used in the computation, \nand accordingly, it is ignored in the privacy analysis.")
                   pure $ buildReturnValue mutvars
          _ ->     pure $ case m2 of
                            [m2] -> SLet (Just m2 :- JTAny)            newT2 (buildReturnValue mutvars)
                            m2   -> TLet [(Just v :- JTAny) | v <- m2] newT2 (buildReturnValue mutvars)

        return (Phi newCond unifiedT1 unifiedT2 , VirtualMutated ([v | v <- mutvars]), moveType1)

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

-}

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

{-
-- TODO: Reimplement for #190
elaborateMut scname (Index t1 t2 t3) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname t1
  (newT2, newT2Type, _) <- elaborateNonmut scname t2
  (newT3, newT3Type, _) <- elaborateNonmut scname t3
  return (Index newT1 newT2 newT3 , Pure UserValue, RefMove)
elaborateMut scname (VIndex t1 t2) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname t1
  (newT2, newT2Type, _) <- elaborateNonmut scname t2
  return (VIndex newT1 newT2 , Pure UserValue, RefMove)
elaborateMut scname (MMap t1 t2) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname t1
  (newT2, newT2Type, _) <- elaborateNonmut scname t2
  return (MMap newT1 newT2 , Pure UserValue, RefMove)
elaborateMut scname (Row t1 t2) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname t1
  (newT2, newT2Type, _) <- elaborateNonmut scname t2
  return (Row newT1 newT2, Pure UserValue, RefMove)
-}


----
-- the mutating builtin cases

{-
-- TODO: Reimplement for #190
--
elaborateMut scname (SubGrad t1 t2) = do
  (argTerms, mutVars) <- elaborateMutList "subgrad" scname scope [(Mutated , t1), (NotMutated , t2)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1, newT2] -> pure (SubGrad newT1 newT2, Pure UserValue)
    [newT1, newT2] -> pure (SubGrad newT1 newT2, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (ScaleGrad scalar grads) = do
  (argTerms, mutVars) <- elaborateMutList "scalegrad" scname scope [(NotMutated , scalar), (Mutated , grads)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1, newT2] -> pure (ScaleGrad newT1 newT2, Pure UserValue)
    [newT1, newT2] -> pure (ScaleGrad newT1 newT2, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (MutClipM c t) = do
  (argTerms, mutVars) <- elaborateMutList "clip" scname scope [(Mutated , t)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT] -> pure (ClipM c newT, Pure UserValue)
    [newT] -> pure (ClipM c newT, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (MutGauss t1 t2 t3 t4) = do
  (argTerms, mutVars) <- elaborateMutList "gauss" scname scope [(NotMutated , t1), (NotMutated , t2), (NotMutated , t3), (Mutated , t4)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1, newT2, newT3, newT4] -> pure (Gauss newT1 newT2 newT3 newT4, Pure UserValue)
    [newT1, newT2, newT3, newT4] -> pure (Gauss newT1 newT2 newT3 newT4, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (MutLaplace t1 t2 t3) = do
  (argTerms, mutVars) <- elaborateMutList "laplace" scname scope [(NotMutated , t1), (NotMutated , t2), (Mutated , t3)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1, newT2, newT3] -> pure (Gauss newT1 newT2 newT3, Pure UserValue)
    [newT1, newT2, newT3] -> pure (Laplace newT1 newT2 newT3, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (ConvertM t1) = do
  (argTerms, mutVars) <- elaborateMutList "convert" scname scope [(Mutated , t1)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    -- NOTE: Reenabled for #142
    -- [newT1] -> pure (ConvertM newT1, Pure UserValue)
    [newT1] -> pure (ConvertM newT1, VirtualMutated mutVars, NoMove)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Transpose t1) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname t1
  return (Transpose newT1 , Pure UserValue, NoMove)
  -}

-- the non mutating builtin cases

elaborateMut scname (Tup t1s) = do

  -- 
  -- We need to make sure that everything put into
  -- the tuple is pure, as this is expected when we
  -- take those things out of the tuple again.
  --
  results <- mapM (elaboratePureValue scname) t1s

  -- what we return is pure, and is a tuple move of the entries
  return $ Value Pure (TupleMove results)

{-
-- TODO: Reimplement for #190.
elaborateMut scname (MCreate t1 t2 t3 t4) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname t1
  (newT2, newT2Type, _) <- elaborateNonmut scname t2
  (newT4, newT4Type, _) <- elaborateNonmut scname t4
  return (MCreate newT1 newT2 t3 newT4 , Pure UserValue, NoMove)
elaborateMut scname (Size t1) = do
  (newT1, newT1Type, _) <- elaborateMut scname t1
  return (Size newT1, Pure UserValue, NoMove)
elaborateMut scname (Length t1) = do
  (newT1, newT1Type, _) <- elaborateMut scname t1
  return (Length newT1, Pure UserValue, NoMove)
elaborateMut scname (ZeroGrad t1) = do
  (newT1, newT1Type, _) <- elaborateMut scname t1
  return (ZeroGrad newT1, Pure UserValue, NoMove)
elaborateMut scname (SumGrads t1 t2) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname t1
  (newT2, newT2Type, _) <- elaborateNonmut scname t2
  return (SumGrads newT1 newT2, Pure UserValue, NoMove)
elaborateMut scname (Sample t1 t2 t3) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname t1
  (newT2, newT2Type, _) <- elaborateNonmut scname t2
  (newT3, newT3Type, _) <- elaborateNonmut scname t3
  return (Sample newT1 newT2 newT3 , Pure UserValue, NoMove)
elaborateMut scname (InternalExpectConst t1) = do
  (newT1, newT1Type, _) <- elaborateMut scname t1
  return (InternalExpectConst newT1, Pure UserValue, NoMove)
elaborateMut scname (DeepcopyValue t1) = do
  (newT1, newT1Type, _) <- elaborateMut scname t1
  return (DeepcopyValue newT1, Pure UserValue, NoMove)
elaborateMut scname (ClipM c t1) = do
  (newT1, newT1Type, _) <- elaborateMut scname t1
  return (ClipM c newT1, Pure UserValue, NoMove)
elaborateMut scname (Gauss t1 t2 t3 t4) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname t1
  (newT2, newT2Type, _) <- elaborateNonmut scname t2
  (newT3, newT3Type, _) <- elaborateNonmut scname t3
  (newT4, newT4Type, _) <- elaborateNonmut scname t4
  return (Gauss newT1 newT2 newT3 newT4 , Pure UserValue, NoMove)
elaborateMut scname (Laplace t1 t2 t3) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname t1
  (newT2, newT2Type, _) <- elaborateNonmut scname t2
  (newT3, newT3Type, _) <- elaborateNonmut scname t3
  return (Laplace newT1 newT2 newT3 , Pure UserValue, NoMove)
elaborateMut scname (AboveThresh t1 t2 t3 t4) = do
  (newT1, newT1Type, _) <- elaborateNonmut scname t1
  (newT2, newT2Type, _) <- elaborateNonmut scname t2
  (newT3, newT3Type, _) <- elaborateNonmut scname t3
  (newT4, newT4Type, _) <- elaborateNonmut scname t4
  return (AboveThresh newT1 newT2 newT3 newT4 , Pure UserValue, NoMove)

  -}

-- the unsupported terms
elaborateMut scname term@(Choice t1)        = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname term@(Loop t1 t2 t3 t4) = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname term@(Reorder t1 t2)    = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname term@(TProject t1 t2)   = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname term@(Arg x a b)        = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname term@(BBApply x a b)    = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname term@(Ret t1)           = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))

elaborateMut scname term@_    = throwError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))






elaborateAsList :: ScopeVar -> ProcDMTerm -> MTC (LastValue, [DemutDMTerm])
elaborateAsList scname (Extra (Block ts)) = do
  ts' <- mapM (elaborateMut scname) ts
  makeTermList ts'
elaborateAsList scname t = do
  t' <- elaborateMut scname t
  makeTermList [t']

---------------------------------------------------
-- recurring utilities


-------------
-- elaborating a lambda term
--

elaborateLambda :: ScopeVar -> [ProcAsgmt JuliaType] -> ProcDMTerm -> MTC (DemutDMTerm , ImmutType)
elaborateLambda scname args body = do
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
  -- ## Then, mark all function arguments as "SingleRead" and "Pure"
  -- ## for the current scope.
  oldVaCtx <- use vaCtx
  mapM (\x -> setImmutTypeOverwritePrevious scname x Pure) [a | (a ::- _) <- args]
  -- ##
  -- END NO.
  --
  -- Allocate new memory for the arguments.
  let arghint (x ::- _) = Left x
  argmvs <- mapM (allocateMem scname) (arghint <$> args)

  -- assign memory to variables
  mapM (\(x ::- _,a) -> setMem x [SingleMem a]) (zip args argmvs)



  --------------------
  --
  -- check the body
  --
  (lastValue, new_body_terms) <- elaborateAsList scname body
  --
  -- find out which mem vars have been mutated
  --
  (mutated_argmvs, mut_states) <- do
    muts <- mapM getMemVarMutationStatus argmvs
    let amvs = zip args muts
    return ([mv | (mv ::- _, Mutated) <- amvs], muts)

  --
  --------------------



  ------------------------------
  -- Compute the elaborated function body
  --
  --   For this we look at the mutated memvars and the last value of the body,
  --   and if required append a statement which either returns the default value,
  --   or returns the tuple of mutated args.
  --
  --   See #190.
  --
  --
  (itype, full_body) <- case (lastValue, mutated_argmvs) of
    --
    -- case I: a pure function
    --
    (PureValue a, []) -> do
      --
      -- We lookup the proc vars of the move,
      -- and check that they do not contain memory
      -- locations which are function inputs.
      --
      debug $ "[elaborateLambda] pure function. move type: " <> show a
      debug $ "   movedVars: " <> show (movedVarsOfMoveType a) <> ", mutated_argmvs: " <> show mutated_argmvs
      --
      memTypesOfMove <- mapM expectNotMoved (movedVarsOfMoveType a)
      let memVarsOfMove = join memTypesOfMove >>= getAllMemVars
      -- 
      case memVarsOfMove `intersect` argmvs of
        [] -> pure ()
        pvs ->   demutationError $ "Found a function which passes through a reference given as input. This is not allowed.\n"
                                      <> "The function body is:\n" <> showPretty body <> "\n"
                                      <> "The passed through memory references are: " <> show pvs

      return $ (Pure, Extra $ DemutBlock new_body_terms)


    --
    -- case II: not allowed
    --
    (PureValue a, xs) -> demutationError $ "Found a function which is mutating, but does not have a 'return'. This is not allowed."
                                        <> "\nThe function body is:\n" <> showPretty body
    --
    -- case III: not allowed
    --
    (MutatingFunctionEndValue, []) -> demutationError $ "Found a function which is not mutating, but has a 'return'. This is not allowed."
                                                    <> "\nThe function body is:\n" <> showPretty body

    --
    -- case IV: mutating function
    --
    (MutatingFunctionEndValue, mvs) -> do
      let last_tuple = TupleMove [SingleMove v | v <- mvs]
      return (Mutating mut_states, Extra (DemutBlock (moveTypeAsTerm last_tuple : new_body_terms)))



  ------------------------------
  -- Restoration of state
  --

  --  
  -- delete all memory variables for this scope
  --
  cleanupMem scname

  --
  -- Restore old VA state for all args
  -- (https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/148#issuecomment-1004950955)
  --
  vactxBeforeRestoration <- use vaCtx
  let restoreArg procvar = do
        case getValue procvar oldVaCtx of
          Nothing -> vaCtx %%= (\ctx -> ((), deleteValue procvar ctx))
          Just (oldvalue) -> vaCtx %%= (\ctx -> ((), setValue procvar (oldvalue) ctx))
  mapM restoreArg [a | (a ::- _) <- args]
  --
  -----------


  return (full_body, itype)

  

-------------
-- elaborating a list of terms which are used in individually either mutating, or not mutating places
--

elaborateMutList :: String -> ScopeVar -> [(IsMutated , ProcDMTerm)] -> MTC ([DemutDMTerm] , [ProcVar])
elaborateMutList f scname mutargs = do
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
  let checkArg :: (IsMutated , ProcDMTerm) -> MTC (DemutDMTerm , MoveType, Maybe (ProcVar))
      checkArg (Mutated , arg) = do
        -- if the argument is given in a mutable position,
        -- it _must_ be a var
        case arg of
          Extra (ProcVarTerm (x ::- a)) -> do 
            -- say that this variable is being reassigned (VAT)
            setImmutType scname (x) Pure

            -- get the memvar of this tevar from the memctx
            -- and say that the memory location is
            -- mutated
            mt <- expectSingleMem =<< expectNotMoved x
            markMutated mt

            return (Var ((procVarAsTeVar x) :- a), SingleMove x, Just x)

          -- if argument is not a var, throw error
          _ -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the term " <> showPretty arg <> " as argument in a mutable-argument-position. Only variables are allowed here.")

      checkArg (NotMutated , arg) = do
        -- if the argument is given in an immutable position,
        -- we allow to use the full immut checking
        (itype , movetype) <- elaborateValue scname arg

        -- we require the argument to be of pure type
        case itype of
          Pure -> pure ()
          Mutating _ -> demutationError $ "It is not allowed to pass mutating functions as arguments. "
                        <> "\nWhen checking " <> f <> "(" <> showPretty (fmap snd mutargs) <> ")"
          PureBlackBox -> demutationError $ "It is not allowed to pass black boxes as arguments. "
                        <> "\nWhen checking " <> f <> "(" <> showPretty (fmap snd mutargs) <> ")"

        return (moveTypeAsTerm movetype , movetype , Nothing)
      

  -- check them
  newArgsWithMutTeVars <- mapM checkArg mutargs

  ------------------------- 
  -- extract for return
  --
  -- these types of the arguments carry the contained "possibly aliased variable names"
  let newArgs = [te | (te , _ , _) <- newArgsWithMutTeVars]
  let argTypes = [ty | (_ , ty, _) <- newArgsWithMutTeVars]
  let mutVars = [m | (_ , _ , Just m) <- newArgsWithMutTeVars]


  --
  -- Make sure that all variables in mutated argument positions are not aliased.
  -- For this we look at the types of the inputs.
  --
  -- See #95
  --
  let getPossiblyAliasedVars a = freeVarsOfProcDMTerm a


  -- Counting how many vars with a given name there are
  let addCount :: (ProcVar) -> Ctx ProcVar Int -> Ctx ProcVar Int
      addCount var counts = case getValue var counts of
                              Just a -> setValue var (a P.+ 1) counts
                              Nothing -> setValue var 1 counts

  -- number of occurences of all variables
  let varcounts = getAllKeyElemPairs $ foldr addCount def (getPossiblyAliasedVars =<< (snd <$> mutargs))
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


{-
------------------------------------------------------------
-- preprocessing a for loop body

runPreprocessLoopBody :: Scope -> Maybe TeVar -> ProcDMTerm -> MTC (ProcDMTerm, [TeVar])
runPreprocessLoopBody scope iter t = do
  (a,x) <- runStateT (preprocessLoopBody scope iter t) def
  return (a, nub x)

-- | Walks through the loop term and changes SLet's to `modify!`
--   calls if such a variable is already in scope.
--   Also makes sure that the iteration variable `iter` is not assigned,
--   and that no `FLet`s are found.
--   Returns the variables which were changed to `modify!`.
preprocessLoopBody :: Scope -> Maybe TeVar -> ProcDMTerm -> StateT [TeVar] MTC ProcDMTerm

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




-}

