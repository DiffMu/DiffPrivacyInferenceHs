
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

-- type ImmutCtx = Ctx TeVar ()
type MutCtx = Ctx TeVar IsMutated

data MFull = MFull
  {
    -- _strongImmutTypes :: ImmutCtx
    _mutTypes :: MutCtx
  }

instance Default MFull where
  def = MFull def

newtype MTC a = MTC {runMTC :: ((StateT MFull (ExceptT DMException (Writer DMLogMessages))) a)}
  deriving (Functor, Applicative, Monad, MonadState MFull, MonadError DMException, MonadWriter DMLogMessages)

instance MonadInternalError MTC where
  internalError = throwError . InternalError

$(makeLenses ''MFull)

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


elaborateNonmut :: Scope -> DMTerm -> MTC (DMTerm , ImmutType)
elaborateNonmut = undefined

elaborateMut :: Scope -> DMTerm -> MTC (DMTerm , ImmutType)

elaborateMut scope (Op op args) = pure (Op op args , Pure)
elaborateMut scope (Sng η τ) = pure (Sng η τ , Pure)

elaborateMut scope (Arg x a b) = internalError "While demutating: encountered an arg term!"
  -- do
  -- markRead x
  -- return (Arg x a b , Pure)

elaborateMut scope (Var x j) = do
  let τ = getValue x scope
  case τ of
    Nothing -> throwError (VariableNotInScope x)
    Just τ  -> return (Var x j, τ)

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
  let scope' = undefined

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
      -- (i.e., no captures where used)
      mutTypes <- use mutTypes
      case isEmptyDict mutTypes of
        True -> pure (Lam args newBody , Mutating vars_mut)
        False -> throwError (VariableNotInScope $ "The variables " <> show mutTypes <> " are not in scope.")

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

  -- function for typechecking a single argument
  let checkArg :: (IsMutated , DMTerm) -> MTC (DMTerm , Maybe TeVar)
      checkArg (Mutated , arg) = do
        -- if the argument is given in a mutable position,
        -- it _must_ be a var
        case arg of
          (Var x a) -> do
            -- get the type of this var from the scope
            -- this one needs to be a single arg
            case getValue x scope of
              Nothing -> throwError (VariableNotInScope x)
              Just (SingleArg y) | x == y -> do
                markMutated y
                return (Var x a , Just x)
              Just _ -> throwError (DemutationError $ "When calling the mutating function " <> show f <> " found the variable " <> show x <> " as argument in a mutable-argument-position. This variable should be bound to a direct argument of the function, but it is not.")

          -- if argument is not a var, throw error
          _ -> throwError (DemutationError $ "When calling the mutating function " <> show f <> " found the term " <> show arg <> " as argument in a mutable-argument-position. Only function arguments themselves are allowed here.")

      checkArg (NotMutated , arg) = do
        -- if the argument is given in an immutable position,
        -- we allow to use the full immut checking
        (arg' , τ) <- elaborateNonmut scope arg

        -- we require the argument to be of pure type
        case τ of
          Pure -> pure ()
          _ -> throwError (DemutationError $ "It is not allowed to pass mutating functions as arguments. " <> "\nWhen checking '" <> show (Apply f args) <> "'")

        return (arg' , Nothing)

  -- the mutation status and the argument terms
  let mutargs = zip muts args

  -- check them
  newArgsWithMutTeVars <- mapM checkArg mutargs
  let newArgs = [te | (te , _) <- newArgsWithMutTeVars]
  let muts = [m | (_ , Just m) <- newArgsWithMutTeVars]

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

elaborateMut scope (MutLet term body) = do

  (newTerm, newTermType) <- elaborateMut scope term

  mutNames <- case newTermType of
    VirtualMutated mutNames -> pure mutNames
    _ -> throwError (DemutationError $ "Found the term " <> show term <> " which is not a mutating function call in a place where only such calls make sense.")

  (newBody, newBodyType) <- elaborateMut scope body

  case mutNames of
    [] -> throwError (DemutationError $ "Found the term " <> show term <> "which does not mutate anything.")
    [n] -> pure (SLet (n :- JTAny) newTerm newBody , newBodyType)
    xs  -> pure (TLet (ns) newTerm newBody , newBodyType)
           where
             ns = [n :- JTAny | n <- xs]

elaborateMut scope t = throwError (UnsupportedTermError t)



liftNewMTC :: MTC a -> TC a
liftNewMTC a =
  let s = runStateT (runMTC a) def
  in TCT (StateT (\t -> fmap (\(a,_) -> (a,def)) s))



  {-
--------------------------------------------------------
-- the elaboration

elaborateImmut :: DMTerm -> MTC (DMTerm , ImmutType)
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

elaborateMut :: DMTerm -> MTC (DMTerm)

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
  let checkArg :: (IsMutated , DMTerm) -> MTC DMTerm
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





-- elaborateMutated :: DMTerm -> (MutType , DMTerm)
-- elaborateMutated t = undefined


-- elaborateMutated :: DMTerm -> TC DMTerm

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



rewriteMut :: DMTerm -> MTC DMTerm
rewriteMut = undefined


-}