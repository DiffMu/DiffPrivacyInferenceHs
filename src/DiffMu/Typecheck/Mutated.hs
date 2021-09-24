
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Mutated where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Core.Logging
import DiffMu.Typecheck.Operations
import DiffMu.Core.DelayedScope
import DiffMu.Typecheck.JuliaType
import DiffMu.Typecheck.Constraint.IsFunctionArgument
import DiffMu.Typecheck.Constraint.IsJuliaEqual
import DiffMu.Typecheck.Constraint.CheapConstraints

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace


---------------------------------------------------------
-- The checking monad

data ImmutType = Pure | Mutating [IsMutated] | VirtualMutated [TeVar] | SingleArg TeVar
  deriving (Show)

-- type ImmutCtx = Ctx TeVar ()
type MutCtx = Ctx TeVar IsMutated

data MFull = MFull
  {
    -- _strongImmutTypes :: ImmutCtx
    _mutTypes :: MutCtx
  , _termVarsOfMut :: NameCtx
  }

instance Default MFull where
  def = MFull def def

newtype MTC a = MTC {runMTC :: ((StateT MFull (ExceptT DMException (Writer DMLogMessages))) a)}
  deriving (Functor, Applicative, Monad, MonadState MFull, MonadError DMException, MonadWriter DMLogMessages)

instance MonadInternalError MTC where
  internalError = throwError . InternalError

$(makeLenses ''MFull)

newTeVarOfMut :: (MonadState MFull m) => Text -> m (TeVar)
newTeVarOfMut hint = termVarsOfMut %%= (first GenTeVar . (newName hint))

-- the scope
type Scope = Ctx TeVar ImmutType

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


markMutated :: TeVar -> MTC ()
markMutated var = do
  let singl = setValue var Mutated emptyDict
  mutTypes %= (⋆! singl)

markRead :: TeVar -> MTC ()
markRead var = do
  let singl = setValue var NotMutated emptyDict
  mutTypes %= (⋆! singl)


---
-- elaborating loops
-- not allowed:
-- - FLet
-- - JuliaReturn
-- - modify iteration variable




elaborateNonmut :: Scope -> MutDMTerm -> MTC (DMTerm , ImmutType)
elaborateNonmut scope term = do
  res <- elaborateMut scope term

  -- get the context and make sure that all variables are not mutated
  Ctx (MonCom ctx) <- use mutTypes
  let ctxElems = H.toList ctx
  let somethingMutated = [a | (a , m) <- ctxElems, m == Mutated]

  case somethingMutated of
    [] -> pure ()
    xs -> throwError (DemutationError $ "expected that the term " <> show term <> " does not mutate anything, but it mutates the following variables: " <> show xs)

  return res

elaborateMut :: Scope -> MutDMTerm -> MTC (DMTerm , ImmutType)

elaborateMut scope (Op op args) = do
  args' <- mapM (elaborateNonmut scope) args
  pure (Op op (fst <$> args') , Pure)
elaborateMut scope (Sng η τ) = pure (Sng η τ , Pure)

elaborateMut scope (Arg x a b) = internalError "While demutating: encountered an arg term!"
  -- do
  -- markRead x
  -- return (Arg x a b , Pure)

elaborateMut scope (Var (x :- j)) = do
  let τ = getValue x scope
  case τ of
    Nothing -> throwError (VariableNotInScope x)
    Just τ  -> return (Var (x :- j), τ)

elaborateMut scope (SLet (x :- τ) term body) = do

  (newTerm , newTermType) <- elaborateMut scope term

  case newTermType of
    Pure -> pure ()
    Mutating _ -> pure ()
    VirtualMutated _ -> throwError (DemutationError $ "Found an assignment " <> show x <> " = " <> show term <> " where RHS is a mutating call. This is not allowed.")
    SingleArg _ -> pure ()

  let scope'  = setValue x newTermType scope
  (newBody , newBodyType) <- elaborateMut scope' body

  return (SLet (x :- τ) newTerm newBody , newBodyType)

elaborateMut scope (Lam args body) = do

  -- add args as vars to the scope
  let scope' = foldr (\(a :- _) -> setValue a (SingleArg a))
                     scope
                     args

  -- check the body
  (newBody,τ) <- elaborateMut scope' body

  -- get the context and check if some variables are now mutated
  ctx <- use mutTypes
  let ctxElems = getAllElems ctx
  let isMutatingFunction = or [a == Mutated | a <- ctxElems]

  -- remove the arguments to this lambda from the context
  let getVar :: (Asgmt JuliaType) -> MTC (IsMutated)
      getVar (a :- t) = do
        mut <- mutTypes %%= popValue a
        case mut of
          Nothing -> pure (NotMutated)
          Just mut -> pure (mut)

  -- call this function on all args given in the signature
  vars_mut <- mapM getVar args


  -- now, depending on whether we have a mutating lambda,
  -- do the following

  case isMutatingFunction of
    --
    -- case I : Mutating
    --
    True -> do
      -- assert that now the context is empty
      -- (i.e., no captures were used)
      mutTypes <- use mutTypes
      case isEmptyDict mutTypes of
        False -> throwError (VariableNotInScope $ "The variables " <> show mutTypes <> " are not in scope.")
        True ->
          -- check that the body is a mutation result
          -- and reorder the resulting tuple
          case τ of
            VirtualMutated vars -> pure (Lam args (Reorder [] newBody) , Mutating vars_mut)
            wrongτ -> throwError (DemutationError $ "Expected the result of the body of a mutating lambda to be a virtual mutated value. But it was "
                                  <> show wrongτ <> "\n where body is:\n" <> show body)

    --
    -- case II : Not Mutating
    --
    False -> do
      -- simply say that this function is not mutating
      pure (Lam args newBody , Pure)

elaborateMut scope (Apply f args) = do

  -- typecheck the function f
  (newF , τ) <- elaborateNonmut scope f

  -- get the type of `f`. if it is not a mutating function,
  -- we give it a type where all arguments are not mutated
  --
  -- also set the return type
  (muts , retType) <- case τ of
        Pure -> pure ((take (length args) (repeat NotMutated)) , \_ -> Pure)
        Mutating muts -> pure (muts , VirtualMutated)
        VirtualMutated _ -> throwError (DemutationError $ "Trying to call the result of a mutating call " <> show f <> ". This is not allowed.")

        -- for calls to arguments we assume that they are pure
        SingleArg _ -> pure ((take (length args) (repeat NotMutated)) , \_ -> Pure)

  -- make sure that there are as many arguments as the function requires
  case length muts == length args of
    True -> pure ()
    False -> throwError (DemutationError $ "Trying to call the function '" <> show f <> "' with a wrong number of arguments.")

  let mutargs = zip muts args
  (newArgs , muts) <- elaborateMutList (show f) scope mutargs

  -- the new term
  return (Apply newF newArgs , retType muts)


elaborateMut scope (FLet fname term body) = do

  -- check the term
  (newTerm, newTermType) <- elaborateNonmut scope term

  -- get the current type for fname from the scope
  let ftype = getValue fname scope

  -- set the new scope with fname if not already
  -- existing
  scope' <- case ftype of
        Nothing -> pure $ setValue fname newTermType scope
        Just Pure -> pure $ scope
        Just (Mutating _) -> throwError (DemutationError $ "")
        Just (SingleArg _) -> internalError $ "Encountered FLet which contains a non function (" <> show body <> ")"
        Just (VirtualMutated _) -> internalError $ "Encountered FLet which contains a non function (" <> show body <> ")"

  -- check the body with this new scope

  (newBody, newBodyType) <- elaborateMut scope' body

  return (FLet fname newTerm newBody, newBodyType)

elaborateMut scope (Extra (MutLet term1 term2)) = do

  -- elaborate the first term and get its mutated variables
  (newTerm1, newTerm1Type) <- elaborateMut scope term1

  mutNames1 <- case newTerm1Type of
    VirtualMutated mutNames1 -> pure mutNames1
    _ -> throwError (DemutationError $ "Found the term " <> show term1 <> " which is not a mutating function call in a place where only such calls make sense.")

  -- elaborate the second term and get its mutated variables
  (newTerm2, newTerm2Type) <- elaborateMut scope term2

  mutNames2 <- case newTerm2Type of
    VirtualMutated mutNames2 -> pure mutNames2
    _ -> throwError (DemutationError $ "Found the term " <> show term1 <> " which is not a mutating function call in a place where only such calls make sense.")


  -- build the result tuple
  let commonMutNames = nub (mutNames1 <> mutNames2)
  let resultTupleTerm = case commonMutNames of
        xs -> Tup ((\a -> Var (a :- JTAny)) <$> xs)

  -- build the let for the second (inner) term
  constructedInnerTerm <- case mutNames2 of
    xs  -> pure (TLet (ns) newTerm2 resultTupleTerm)
           where
             ns = [n :- JTAny | n <- xs]

  -- build the let for the first (outer) term
  case mutNames1 of
    xs  -> pure (TLet (ns) newTerm1 constructedInnerTerm , VirtualMutated commonMutNames)
           where
             ns = [n :- JTAny | n <- xs]

elaborateMut scope (Extra (MutLoop iters iterVar body)) = do
  -- first, elaborate the iters
  (newIters , newItersType) <- elaborateNonmut scope iters

  -- now, preprocess the body,
  -- i.e., find out which variables are getting mutated
  -- and change their `SLet`s to `modify!` terms
  preprocessedBody <- preprocessLoopBody scope iterVar body

  -- we can now elaborate the body, and thus get the actual list
  -- of modified variables
  (newBody, newBodyType) <- elaborateMut scope preprocessedBody

  -- we use them to build a tlet around the body,
  -- and return that new `Loop` term
  case newBodyType of
    VirtualMutated mutvars -> do
      -- the actual body term is going to look as follows:
      --
      --   let (c1...cn) = captureVar
      --   in term...
      --
      -- where `term` is made sure to return the captured tuple
      -- by the general demutation machinery
      captureVar <- newTeVarOfMut "loop_capture_"

      let newBodyWithLet = TLet [(v :- JTAny) | v <- mutvars] (Var (captureVar :- JTAny)) newBody
      let newTerm = Loop newIters mutvars (iterVar , captureVar) newBodyWithLet

      return (newTerm , VirtualMutated mutvars)

    -- if there was no mutation,
    -- throw error
    other -> throwError (DemutationError $ "Expected a loop body to be mutating, but it was of type " <> show other)


elaborateMut scope (SubGrad t1 t2) = do
  (argTerms, mutVars) <- elaborateMutList "subgrad" scope [(Mutated , t1), (NotMutated , t2)]
  case argTerms of
    [newT1, newT2] -> pure (SubGrad newT1 newT2, VirtualMutated mutVars)
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scope (ClipM c t) = do
  (argTerms, mutVars) <- elaborateMutList "clip" scope [(Mutated , t)]
  case argTerms of
    [newT] -> pure (ClipM c newT, VirtualMutated mutVars)
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scope (Gauss t1 t2 t3 t4) = do
  (argTerms, mutVars) <- elaborateMutList "gauss" scope [(NotMutated , t1), (NotMutated , t2), (NotMutated , t3), (Mutated , t4)]
  case argTerms of
    [newT1, newT2, newT3, newT4] -> pure (Gauss newT1 newT2 newT3 newT4, VirtualMutated mutVars)
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scope (ConvertM t1) = do
  (argTerms, mutVars) <- elaborateMutList "convert" scope [(Mutated , t1)]
  case argTerms of
    [newT1] -> pure (ConvertM newT1, VirtualMutated mutVars)
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scope (Extra (Modify (v) t1)) = do
  (argTerms, mutVars) <- elaborateMutList "internal_modify" scope [(Mutated , (Var v)) , (NotMutated , t1)]
  case argTerms of
    [Var (v :- jt), newT2] -> pure (newT2 , VirtualMutated mutVars)
    [_, newT2] -> internalError ("After elaboration of an internal_modify term result was not a variable.")
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scope t = throwError (UnsupportedError (show t))


---------------------------------------------------
-- recurring utilities

elaborateMutList :: String -> Scope -> [(IsMutated , MutDMTerm)] -> MTC ([DMTerm] , [TeVar])
elaborateMutList f scope mutargs = do

  -- function for typechecking a single argument
  let checkArg :: (IsMutated , MutDMTerm) -> MTC (DMTerm , Maybe TeVar)
      checkArg (Mutated , arg) = do
        -- if the argument is given in a mutable position,
        -- it _must_ be a var
        case arg of
          (Var (x :- a)) -> do
            -- get the type of this var from the scope
            -- this one needs to be a single arg
            case getValue x scope of
              Nothing -> throwError (VariableNotInScope x)
              Just (SingleArg y) | x == y -> do
                markMutated y
                return (Var (x :- a) , Just x)
              Just _ -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the variable " <> show x <> " as argument in a mutable-argument-position. This variable should be bound to a direct argument of the function, but it is not.")

          -- if argument is not a var, throw error
          _ -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the term " <> show arg <> " as argument in a mutable-argument-position. Only function arguments themselves are allowed here.")

      checkArg (NotMutated , arg) = do
        -- if the argument is given in an immutable position,
        -- we allow to use the full immut checking
        (arg' , τ) <- elaborateMut scope arg

        -- we require the argument to be of pure type
        case τ of
          Pure -> pure ()
          SingleArg _ -> pure ()
          Mutating _ -> throwError (DemutationError $ "It is not allowed to pass mutating functions as arguments. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")
          VirtualMutated _ -> throwError (DemutationError $ "It is not allowed to use the result of mutating functions as arguments in other mutating functions. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")

        return (arg' , Nothing)

  -- check them
  newArgsWithMutTeVars <- mapM checkArg mutargs
  let newArgs = [te | (te , _) <- newArgsWithMutTeVars]
  let muts = [m | (_ , Just m) <- newArgsWithMutTeVars]

  return (newArgs, muts)



------------------------------------------------------------
-- preprocessing a for loop body

preprocessLoopBody :: Scope -> TeVar -> MutDMTerm -> MTC (MutDMTerm)

preprocessLoopBody scope iter (SLet (v :- jt) term body) = do
  -- it is not allowed to change the iteration variable
  case iter == v of
    True -> throwError (DemutationError $ "Inside for-loops the iteration variable (in this case '" <> show iter <> "') is not allowed to be mutated.")
    False -> pure ()

  -- if an slet expression binds a variable which is already in scope,
  -- then this means we are actually mutating this variable.
  -- thus we update the term to be a mutlet and use the builtin modify!
  -- function for setting the variable
  -- if the variable has not been in scope, it is a local variable,
  -- and we do not change the term

  term' <- preprocessLoopBody scope iter term
  body' <- preprocessLoopBody scope iter body

  case getValue v scope of
    Just _  -> return (Extra (MutLet (Extra (Modify (v :- jt) term')) (body')))
    Nothing -> return (SLet (v :- jt) term' body')

preprocessLoopBody scope iter (FLet f _ _) = throwError (DemutationError $ "Function definition is not allowed in for loops. (Encountered definition of " <> show f <> ".)")

-- for these terms we do nothing special
preprocessLoopBody scope iter (Var a) = return (Var a)

-- the rest is currently not supported
preprocessLoopBody scope iter t = throwError (UnsupportedError (show t))







liftNewMTC :: MTC a -> TC a
liftNewMTC a =
  let s = runStateT (runMTC a) def
  in TCT (StateT (\t -> fmap (\(a,_) -> (a,def)) s))



  {-
--------------------------------------------------------
-- the elaboration

elaborateImmut :: MutDMTerm -> MTC (MutDMTerm , ImmutType)
elaborateImmut (MutLam vars body) = do

  -- typecheck/infer the body
  newBody <- elaborateMut body

  -- -- assert that the immutable gamma context has not been used
  -- immutTypes <- use strongImmutTypes
  -- case isEmptyDict immutTypes of
  --   True -> pure ()
  --   False -> throwError (DemutationError $ "Functions which are mutating (f!) are not allowed to use variables from outside.")

  -- construct the type, while at the same type
  -- removing the variables from the mutable context
  --
  -- this function does this for one variable
  let getVar :: (Asgmt JuliaType , Maybe IsMutated) -> MTC (Asgmt JuliaType , IsMutated)
      getVar (_ , Just _) = internalError "While demutating, did not except to encounter a mutation annotation already in the term"
      getVar (a :- t , Nothing) = do
        mut <- mutTypes %%= popValue a
        case mut of
          Nothing -> pure (a :- t , NotMutated)
          Just mut -> pure (a :- t , Mutated)

  -- call this function on all vars given in the signature
  vars_mut <- mapM getVar vars

  -- assert that now the mutable M context is empty
  -- (i.e., only defined variables where used)
  mutTypes <- use mutTypes
  case isEmptyDict mutTypes of
    True -> pure ()
    False -> throwError (VariableNotInScope $ "The variables " <> show mutTypes <> " are not in scope.")

  -- construct the type of this lambda term
  let typ = [m | (_ , m) <- vars_mut]

  -- construct the new lambda annotation
  let newAnnot = [(ann , Just m) | (ann , m) <- vars_mut]

  let newTerm = MutLam newAnnot newBody

  return (newTerm , Mutating typ)

elaborateImmut t = undefined



--------------------------
-- the mutating part

elaborateMut :: MutDMTerm -> MTC (MutDMTerm)

elaborateMut (MutLam vars body) = throwError (DemutationError $ "Mutating lambda are not allowed in mutated positions, when checking " <> show (MutLam vars body))

elaborateMut (MutApply f args) = do
  -- typecheck the function f
  (newF , τ) <- elaborateImmut f

  -- make sure that it is a mutating function, and get the type
  muts <- case τ of
    Pure -> throwError (DemutationError $ "Trying to call the pure function '" <> show f <> "' using a mutating call.")
    Mutating muts -> pure muts

  -- make sure that there are as many arguments as the function requires
  case length muts == length args of
    True -> pure ()
    False -> throwError (DemutationError $ "Trying to call the function '" <> show f <> "' with a wrong number of arguments.")

  -- function for typechecking a single argument
  let checkArg :: (IsMutated , MutDMTerm) -> MTC MutDMTerm
      checkArg (Mutated , arg) = do
        -- if the argument is given in a mutable position,
        -- it _must_ be a var
        case arg of
          -- mark this arg as mutated
          (Var x a) -> do
            markMutated x
            return (Var x a)

          -- if argument is not a var, throw error
          _ -> throwError (DemutationError $ "When calling the mutating function " <> show f <> " found the term " <> show arg <> " as argument in a mutable-argument-position. Only function arguments themselves are allowed here.")

      checkArg (NotMutated , arg) = do
        -- if the argument is given in an immutable position,
        -- we allow to use the full immut checking
        (arg' , τ) <- elaborateImmut arg

        -- we require the argument to be of pure type
        case τ of
          Pure -> pure ()
          _ -> throwError (DemutationError $ "It is not allowed to pass mutating functions as arguments. " <> "\nWhen checking '" <> show (MutApply f args) <> "'")

        return arg'

  -- the mutation status and the argument terms
  let mutargs = zip muts args

  -- check them
  newArgs <- mapM checkArg mutargs

  -- the new term
  return (MutApply newF newArgs)

-- all other terms we try to parse as not mutating
elaborateMut t = do
  (t' , τ) <- elaborateImmut t

  case τ of
    Pure -> pure t'
    (Mutating τ') -> internalError $ "Did not expect to get the mutating type " <> show τ'





-- elaborateMutated :: MutDMTerm -> (MutType , MutDMTerm)
-- elaborateMutated t = undefined


-- elaborateMutated :: MutDMTerm -> TC MutDMTerm

-- elaborateMutated (FLet var def rest) = do
--   let FindFLetsResult defs rest' = findFLets var rest
--       alldefs = (def:defs)

--   -- we derive the julia type from the term, appending the corresponding julia types to their definitions
--   allsigs <- mapM getJuliaSig alldefs
--   let alldefsWithJuliaSig = zip allsigs alldefs

--       -- we thread the elements through a hashmap => if we have terms with the same juliatype,
--       -- the second one overwrites the first one
--       alldefsWithJuliaSig' = H.elems (H.fromList alldefsWithJuliaSig)
--   debug $ "-----------------"
--   debug $ "for var " <> show var <> " found the signatures:"
--   debug $ show alldefsWithJuliaSig
--   debug $ "after removing duplicates, we have: "
--   debug $ show alldefsWithJuliaSig'

--   updatedAllDefs <- mapM elaborateMutated alldefsWithJuliaSig'
--   updatedRest <- elaborateMutated rest'
--   return $ expandFLets var updatedAllDefs updatedRest
-- elaborateMutated (SLet var def rest) = SLet var <$> (elaborateMutated def) <*> (elaborateMutated rest)
-- elaborateMutated (TLet var def rest) = TLet var <$> (elaborateMutated def) <*> (elaborateMutated rest)

-- elaborateMutated (Ret t)           = Ret <$> (elaborateMutated t)
-- elaborateMutated (Sng a t)         = pure $ Sng a t
-- elaborateMutated (Var a t)         = pure $ Var a t
-- elaborateMutated (Rnd t)           = pure $ Rnd t
-- elaborateMutated (Arg a b c)       = pure $ Arg a b c
-- elaborateMutated (Op o ts)         = Op o <$> (mapM elaborateMutated ts)
-- elaborateMutated (Phi a b c)       = Phi <$> (elaborateMutated a) <*> (elaborateMutated b) <*> (elaborateMutated c)
-- elaborateMutated (Lam a t)         = Lam a <$> (elaborateMutated t)
-- elaborateMutated (LamStar a t)     = LamStar a <$> (elaborateMutated t)
-- elaborateMutated (Apply t ts)      = Apply <$> (elaborateMutated t) <*> (mapM elaborateMutated ts)
-- elaborateMutated (Choice m)        = Choice <$> (mapM elaborateMutated m)
-- elaborateMutated (Tup ts)          = Tup <$> (mapM elaborateMutated ts)
-- elaborateMutated (Gauss a b c d)   = Gauss <$> (elaborateMutated a) <*> (elaborateMutated b) <*> (elaborateMutated c) <*> (elaborateMutated d)
-- elaborateMutated (MCreate a b x c) = MCreate <$> (elaborateMutated a) <*> (elaborateMutated b) <*> pure x <*> (elaborateMutated c)
-- elaborateMutated (Transpose a)     = Transpose <$> (elaborateMutated a)
-- elaborateMutated (Index a b c)     = Index <$> (elaborateMutated a) <*> (elaborateMutated b) <*> (elaborateMutated c)
-- elaborateMutated (ClipM x a)       = ClipM x <$> (elaborateMutated a)
-- elaborateMutated (Iter a b c)      = Iter <$> (elaborateMutated a) <*> (elaborateMutated b) <*> (elaborateMutated c)
-- elaborateMutated (Loop a b x c)    = Loop <$> (elaborateMutated a) <*> (elaborateMutated b) <*> pure x <*> (elaborateMutated c)



rewriteMut :: MutDMTerm -> MTC MutDMTerm
rewriteMut = undefined


-}



          -- let newType = Mutating [m | (_ , m) <- vars_mut]
          -- let mutatedvars = [a | (a , Mutated) <- vars_mut]
          -- newBodyWithLet <- case mutatedvars of
          --                 [] -> impossible "In this execution there should be existing mutated variables."
          --                 [n] -> pure (SLet (n :- JTAny) newBody _)
          --                 xs  -> pure (TLet (ns) newBody)
          --                           where
          --                             ns = [n :- JTAny | n <- xs]
