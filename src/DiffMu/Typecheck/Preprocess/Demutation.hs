
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.Demutation where

import DiffMu.Prelude
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


---------------------------------------------------------
-- The checking monad

data IsMutated = Mutated | NotMutated
  deriving (Generic, Show, Eq)

data IsLocalMutation = LocalMutation | NotLocalMutation
  deriving (Show, Eq)

data VarAccessType = ReadSingle ScopeVar | ReadMulti | WriteSingleBase IsFLetDefined ScopeVar
  deriving (Show,Eq,Ord)

data IsFLetDefined = FLetDefined | NotFLetDefined
  deriving (Show,Eq,Ord)

pattern WriteSingle v = WriteSingleBase NotFLetDefined v
pattern WriteSingleFunction v = WriteSingleBase FLetDefined v

onlyLocallyMutatedVariables :: [(TeVar,IsLocalMutation)] -> Bool
onlyLocallyMutatedVariables xs = [v | (v, NotLocalMutation) <- xs] == []

data PureType = UserValue | DefaultValue | SingleArg TeVar
  deriving (Show)

data ImmutType = Pure PureType | Mutating [IsMutated] | VirtualMutated [(TeVar , IsLocalMutation)] | PureBlackBox
  deriving (Show)

consumeDefaultValue :: ImmutType -> ImmutType
consumeDefaultValue (Pure DefaultValue) = Pure UserValue
consumeDefaultValue a = a

-- type ImVarAccessCtx = Ctx TeVar ()
type VarAccessCtx = Ctx TeVar VarAccessType

data MFull = MFull
  {
    _mutTypes :: VarAccessCtx
  , _termVarsOfMut :: NameCtx
  , _scopeNames :: NameCtx
  , _topLevelInfo :: TopLevelInformation
  }


type MTC = LightTC Location_PrePro_Demutation MFull

$(makeLenses ''MFull)


-- new variables
newTeVarOfMut :: (MonadState MFull m) => Text -> m (TeVar)
newTeVarOfMut hint = termVarsOfMut %%= (first GenTeVar . (newName hint))

newScopeVar :: (MonadState MFull m) => Text -> m (ScopeVar)
newScopeVar hint = scopeNames %%= (first ScopeVar . (newName hint))


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

-- data VarAccessType = ReadSingle ScopeVar | ReadMulti | WriteSingle ScopeVar | WriteSingleFunction ScopeVar

computeVarAccessType :: TeVar -> VarAccessType -> VarAccessType -> MTC VarAccessType
computeVarAccessType var a b = do
  let cur = sort [a,b]
  case cur of
    [ReadSingle a, ReadSingle b] | a == b   -> pure (ReadSingle a)
    [ReadSingle a, ReadSingle b] | a /= b   -> pure (ReadMulti)
    [ReadSingle a, ReadMulti]               -> pure (ReadMulti)
    [ReadSingle a, WriteSingle b] | a == b  -> pure (WriteSingle a)
    [ReadSingle a, WriteSingle b] | a /= b  -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                           <> "' is being mutated and read in two different scopes.\n"
                                                                           <> "This is not allowed."
    -- [ReadSingle a, WriteSingleFunction b] | a == b -> pure (WriteSingleFunction a)
    -- [ReadSingle a, WriteSingleFunction b] | a /= b -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
    --                                                                                <> "' is being mutated and read in two different scopes.\n"
    --                                                                                <> "This is not allowed."
    [ReadSingle a, WriteSingleFunction b]   -> pure (WriteSingleFunction b)
    [ReadMulti,ReadMulti]                   -> pure (ReadMulti)
    [ReadMulti,WriteSingle _]               -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                            <> "' is being mutated and read in two different scopes.\n"
                                                                            <> "This is not allowed."
    [ReadMulti,WriteSingleFunction a]       -> pure (WriteSingleFunction a) -- because of flet reordering it is allowed to mutate functions
    [WriteSingle a, WriteSingle b] | a == b -> pure (WriteSingle a)
    [WriteSingle a, WriteSingle b] | a /= b -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                            <> "' is being mutated in two different scopes.\n"
                                                                            <> "This is not allowed."
    [WriteSingle _, WriteSingleFunction _]  -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' is defined as function and as value."
                                                                            <> "This is not allowed."
    [WriteSingleFunction a, WriteSingleFunction b] | a == b -> pure (WriteSingleFunction a)
    [WriteSingleFunction a, WriteSingleFunction b] | a /= b -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                            <> "' is being mutated in two different scopes.\n"
                                                                            <> "This is not allowed."
    _ -> impossible "In demutation, while computing var access type. This branch should be inaccessible."

-- helpers
markMutatedBase :: IsFLetDefined -> ScopeVar -> TeVar -> MTC ()
markMutatedBase fletdef scname var = mutTypes %=~ (markMutatedInScope scname var)
    where 
      markMutatedInScope :: ScopeVar -> TeVar -> VarAccessCtx -> MTC VarAccessCtx 
      markMutatedInScope scname var ctx =
        case getValue var ctx of
          Nothing                      -> impossible $ "When demutating (MarkMutated), the variable "
                                                       <> show var <> " was not in the VA-Ctx."
          Just oldvatype -> do
            newvatype <- computeVarAccessType var oldvatype (WriteSingleBase fletdef scname)
            return (setValue var newvatype ctx)

markMutatedFLet :: ScopeVar -> TeVar -> MTC ()
markMutatedFLet scname var = do
  log $ "Marking flet mutated for " <> show var
  markMutatedBase FLetDefined scname var

markMutated :: ScopeVar -> TeVar -> MTC ()
markMutated scname var = do
  log $ "Marking simple mutated for " <> show var
  markMutatedBase NotFLetDefined scname var


markRead :: ScopeVar -> TeVar -> MTC ()
markRead scname var = mutTypes %=~ (markReadInScope scname var)
    where 
      markReadInScope :: ScopeVar -> TeVar -> VarAccessCtx -> MTC VarAccessCtx 
      markReadInScope scname var ctx =
        case getValue var ctx of
          Nothing                      -> pure (setValue var (ReadSingle scname) ctx)
          Just oldvatype -> do
            newvatype <- computeVarAccessType var oldvatype (ReadSingle scname)
            return (setValue var newvatype ctx)

markReadMaybe :: ScopeVar -> Maybe TeVar -> MTC ()
markReadMaybe scname (Just x) = markRead scname x
markReadMaybe scname Nothing = pure ()

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
safeSetValueBase fletdef scname (Nothing) newType scope = pure scope
safeSetValueBase fletdef scname (Just var) newType scope =
  case getValue var scope of
    Nothing -> do
      markRead scname var
      return (setValue var newType scope)
    (Just oldType) -> do
      markMutatedBase fletdef scname var -- We say that we are changing this variable. This can throw an error.
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
    Mutating _ -> pure ()
    PureBlackBox -> pure ()

  return (resTerm , resType)

elaborateMut :: ScopeVar -> Scope -> MutDMTerm -> MTC (DMTerm , ImmutType)

elaborateMut scname scope (Op op args) = do
  args' <- mapM (elaborateNonmut scname scope) args
  pure (Op op (fst <$> args') , Pure UserValue)
elaborateMut scname scope (Sng η τ) = pure (Sng η τ , Pure UserValue)
elaborateMut scname scope (Rnd jt) = pure (Rnd jt , Pure UserValue)

elaborateMut scname scope (Var (x :- j)) = do
  let τ = getValueMaybe x scope
  case τ of
    Nothing -> logForce ("checking Var term, scope: " <> show scope) >> throwError (DemutationDefinitionOrderError x)
    Just τ  -> do
      markReadMaybe scname x
      return (Var (x :- j), τ)

elaborateMut scname scope (BBLet name args tail) = do

  -- write the black box into the scope with its type
  scope'  <- safeSetValue scname (Just name) PureBlackBox scope

  -- typecheck the body in this new scope
  (newBody , newBodyType) <- elaborateMut scname scope' tail

  return (BBLet name args newBody , consumeDefaultValue newBodyType)

elaborateMut scname scope (SLetBase ltype (x :- τ) term body) = do

  (newTerm , newTermType) <- elaborateMut scname scope term

  case newTermType of
    Pure _ -> pure ()
    Mutating _ -> pure ()
    VirtualMutated _ -> throwError (DemutationError $ "Found an assignment " <> show x <> " = " <> showPretty term <> " where RHS is a mutating call. This is not allowed.")
    PureBlackBox     -> throwError (DemutationError $ "Found an assignment " <> show x <> " = " <> showPretty term <> " where RHS is a black box. This is not allowed.")

  scope'  <- safeSetValue scname x newTermType scope
  (newBody , newBodyType) <- elaborateMut scname scope' body

  return (SLetBase ltype (x :- τ) newTerm newBody , consumeDefaultValue newBodyType)

elaborateMut scname scope (TLetBase ltype vars term body) = do

  (newTerm , newTermType) <- elaborateMut scname scope term

  case newTermType of
    Pure _ -> pure ()
    Mutating _ -> pure ()
    VirtualMutated _ -> throwError (DemutationError $ "Found an assignment " <> show vars <> " = " <> showPretty term <> " where RHS is a mutating call. This is not allowed.")
    PureBlackBox     -> throwError (DemutationError $ "Found an assignment " <> show vars <> " = " <> showPretty term <> " where RHS is a black box. This is not allowed.")

  -- add all values as pure to the scope
  scope' <- foldrM (\(v :- _) s -> safeSetValue scname v (Pure UserValue) s) scope (vars)
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

        return (BBApply newF newArgs glvars , Pure UserValue)
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

  -- check the term
  (newTerm, newTermType) <- elaborateNonmut scname scope term

  -- get the current type for fname from the scope
  let ftype = getValue fname scope

  -- set the new scope with fname if not already existing
  -- (but only allow pure uservalue-functions, or single-definition mutating functions)
  scope' <- case ftype of
        Nothing -> safeSetValueAllowFLet scname (Just fname) newTermType scope
        Just (Pure UserValue) -> safeSetValueAllowFLet scname (Just fname) newTermType scope
        Just (Mutating _) -> throwError (DemutationError $ "We do not allow mutating functions to have multiple definitions")
        Just (Pure DefaultValue) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        Just (Pure (SingleArg _)) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        Just (VirtualMutated _) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"
        Just (PureBlackBox) -> internalError $ "Encountered FLet which contains a non function (" <> showPretty body <> ")"

  -- check the body with this new scope

  (newBody, newBodyType) <- elaborateMut scname scope' body

  return (FLet fname newTerm newBody, consumeDefaultValue newBodyType)

elaborateMut scname scope (Extra (MutLet ltype term1 term2)) = do

  -- elaborate the first term and get its mutated variables
  (newTerm1, newTerm1Type) <- elaborateMut scname scope term1

  -- find out which variables have been locally modified,
  -- add these to the scope
  let locmutvars1 = case newTerm1Type of
        VirtualMutated xs -> [x | (x,LocalMutation) <- xs]
        _ -> []
  let scope' = foldr (\v s -> setValue v (Pure UserValue) s) scope (locmutvars1)


  -- elaborate the second term and get its mutated variables
  (newTerm2, newTerm2Type) <- elaborateMut scname scope' term2

  case (newTerm1Type , newTerm2Type) of

    -----------------------------------
    -- SINGLE GLOBAL, and irrelevant
    -- only term1 is mutating
    (VirtualMutated mutNames1, VirtualMutated []) -> do

      warn ("Found the term " <> showPretty term2
                     <> " which is not a mutating function call in a place where only such calls make sense.\n"
                     <> " => It has the type " <> show (VirtualMutated []) <> "\n"
                     <> " => In the term:\n" <> parenIndent (showPretty (Extra (MutLet ltype term1 term2))) <> "\n"
                     <> " => Conclusion: It is ignored in the privacy analysis.")

      let ns1 = [Just n :- JTAny | (n, _) <- mutNames1]
          term = TLetBase ltype ns1 newTerm1
                (
                  Tup ((\(a, _) -> Var (Just a :- JTAny)) <$> mutNames1)
                )
      pure (term , VirtualMutated mutNames1)


    -- only term2 is mutating
    (VirtualMutated [], VirtualMutated mutNames2) -> do

      warn ("Found the term " <> showPretty term1
                     <> " which is not a mutating function call in a place where only such calls make sense.\n"
                     <> " => It has the type " <> show (VirtualMutated []) <> "\n"
                     <> " => In the term:\n" <> parenIndent (showPretty (Extra (MutLet ltype term1 term2))) <> "\n"
                     <> " => Conclusion: It is ignored in the privacy analysis.")

      let ns2 = [Just n :- JTAny | (n, _) <- mutNames2]
          term = TLetBase ltype ns2 newTerm2
                (
                  Tup ((\(a, _) -> Var (Just a :- JTAny)) <$> mutNames2)
                )
      pure (term , VirtualMutated mutNames2)

    -------------------------------------------
    -- DOUBLE GLOBAL
    -- both are mutating
    (VirtualMutated mutNames1, VirtualMutated mutNames2) ->
      let commonMutNames = nub (mutNames1 <> mutNames2)
          ns1 = [Just n :- JTAny | (n, _) <- mutNames1]
          ns2 = [Just n :- JTAny | (n, _) <- mutNames2]
          term = TLetBase ltype ns1 newTerm1
                (
                  TLetBase ltype ns2 newTerm2
                  (
                    Tup ((\(a, _) -> Var (Just a :- JTAny)) <$> commonMutNames)
                  )
                )
      in pure (term , VirtualMutated commonMutNames)

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
        UserValue -> pure (valterm , Pure UserValue)
        SingleArg _ -> pure (valterm , Pure UserValue)
        DefaultValue -> pure (newTerm1 , VirtualMutated mutNames1')

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
        _ -> warn ("Found the term " <> showPretty term2
                     <> " which is not mutating in a place where only mutating terms make sense.\n"
                     <> " => It has the type " <> show (Pure p) <> "\n"
                     <> " => In the term:\n" <> parenIndent (showPretty (Extra (MutLet ltype term1 term2))) <> "\n"
                     <> " => Conclusion: It is ignored in the privacy analysis.")

      -- let mutNames2 = [(v, LocalMutation) | v <- mutNames2']
      --     commonMutNames = nub (mutNames1 <> mutNames2)
      --     ns1 = [n :- JTAny | (n, _) <- mutNames1]

      --     term = TLet ns1 newTerm1
      --           (
      --             Tup ((\(a, _) -> Var (a :- JTAny)) <$> mutNames1)
      --           )
      pure (newTerm1 , VirtualMutated mutNames1)

    ------------------------------------
    -- UNSUPPORTED
    -- neither term1 nor term2 are mutating
    (ty1, ty2) -> throwError (DemutationError $ "Encountered a MutLet where the two commands have the following types: " <> show (ty1, ty2)
                                                <> "\nThis is not supported."
                                                <> "\nIn the term:\n" <> showPretty (Extra (MutLet ltype term1 term2)))

elaborateMut scname scope (Extra (MutLoop iters iterVar body)) = do
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
  scope' <- safeSetValue scname iterVar (Pure UserValue) scope

  -- we can now elaborate the body, and thus get the actual list
  -- of modified variables
  (newBody, newBodyType) <- elaborateMut scname scope' preprocessedBody

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



-- the loop-body-preprocessing creates these modify! terms
-- they get elaborated into tlet assignments again.
elaborateMut scname scope (Extra (SModify (Nothing :- _) t1)) = throwError (DemutationError $ "Found a nameless variable in a modify term.")
elaborateMut scname scope (Extra (SModify (Just v :- _) t1)) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  return (Tup [newT1], VirtualMutated [(v , LocalMutation)])

  -- (argTerms, mutVars) <- elaborateMutList "internal_modify" scope [(Mutated , (Var v)) , (NotMutated , t1)]
  -- case argTerms of
  --   [Var (v :- jt), newT2] -> pure (Tup [newT2] , VirtualMutated mutVars)
  --   [_, newT2] -> internalError ("After elaboration of an internal_modify term result was not a variable.")
  --   _ -> internalError ("Wrong number of terms after elaborateMutList")

-- We also have tuple modify
elaborateMut scname scope (Extra (TModify xs t1)) = do
  let elabSingle (Just v :- _) = return (v, LocalMutation)
      elabSingle (Nothing :- _) = throwError (DemutationError $ "Found a nameless variable in a tuple modify term.")

  allElab <- mapM elabSingle xs

  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  return (newT1 , VirtualMutated allElab)


elaborateMut scname scope (Extra (MutRet)) = do
  return (Tup [] , VirtualMutated [])

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

elaborateMut scname scope term@(Phi cond t1 t2) = do
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
    (_, _) -> return (Phi newCond newT1 newT2 , Pure UserValue)


----
-- the mutating builtin cases

elaborateMut scname scope (SubGrad t1 t2) = do
  (argTerms, mutVars) <- elaborateMutList "subgrad" scname scope [(Mutated , t1), (NotMutated , t2)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    --
    [newT1, newT2] -> pure (SubGrad newT1 newT2, Pure UserValue)
    -- [newT1, newT2] -> pure (SubGrad newT1 newT2, VirtualMutated mutVars)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (ScaleGrad scalar grads) = do
  (argTerms, mutVars) <- elaborateMutList "scalegrad" scname scope [(NotMutated , scalar), (Mutated , grads)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    --
    [newT1, newT2] -> pure (ScaleGrad newT1 newT2, Pure UserValue)
    -- [newT1, newT2] -> pure (ScaleGrad newT1 newT2, VirtualMutated mutVars)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (ClipM c t) = do
  (argTerms, mutVars) <- elaborateMutList "clip" scname scope [(Mutated , t)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    --
    [newT] -> pure (ClipM c newT, Pure UserValue)
    -- [newT] -> pure (ClipM c newT, VirtualMutated mutVars)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (Gauss t1 t2 t3 t4) = do
  (argTerms, mutVars) <- elaborateMutList "gauss" scname scope [(NotMutated , t1), (NotMutated , t2), (NotMutated , t3), (Mutated , t4)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    --
    [newT1, newT2, newT3, newT4] -> pure (Gauss newT1 newT2 newT3 newT4, Pure UserValue)
    -- [newT1, newT2, newT3, newT4] -> pure (Gauss newT1 newT2 newT3 newT4, VirtualMutated mutVars)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (ConvertM t1) = do
  (argTerms, mutVars) <- elaborateMutList "convert" scname scope [(Mutated , t1)]
  case argTerms of
    -- NOTE: Because of #95, we say that this function is pure
    --
    [newT1] -> pure (ConvertM newT1, Pure UserValue)
    -- [newT1] -> pure (ConvertM newT1, VirtualMutated mutVars)
    --
    -- END NOTE
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname scope (Transpose t1) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  return (Transpose newT1 , Pure UserValue)

-- the non mutating builtin cases
elaborateMut scname scope (Ret t1) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  return (Ret newT1 , Pure UserValue)
elaborateMut scname scope (Tup t1s) = do
  newT1s <- fmap fst <$> mapM (elaborateNonmut scname scope) t1s
  return (Tup newT1s , Pure UserValue)
elaborateMut scname scope (MCreate t1 t2 t3 t4) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  (newT2, newT2Type) <- elaborateNonmut scname scope t2
  (newT4, newT4Type) <- elaborateNonmut scname scope t4
  return (MCreate newT1 newT2 t3 newT4 , Pure UserValue)
elaborateMut scname scope (Index t1 t2 t3) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  (newT2, newT2Type) <- elaborateNonmut scname scope t2
  (newT3, newT3Type) <- elaborateNonmut scname scope t3
  return (Index newT1 newT2 newT3 , Pure UserValue)
elaborateMut scname scope (VIndex t1 t2) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  (newT2, newT2Type) <- elaborateNonmut scname scope t2
  return (VIndex newT1 newT2 , Pure UserValue)
elaborateMut scname scope (Row t1 t2) = do
  (newT1, newT1Type) <- elaborateNonmut scname scope t1
  (newT2, newT2Type) <- elaborateNonmut scname scope t2
  return (Row newT1 newT2, Pure UserValue)
elaborateMut scname scope (Size t1) = do
  (newT1, newT1Type) <- elaborateMut scname scope t1
  return (Size newT1, Pure UserValue)
elaborateMut scname scope (Length t1) = do
  (newT1, newT1Type) <- elaborateMut scname scope t1
  return (Length newT1, Pure UserValue)

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
  -- add args as vars to the scope
  --
  -- NOTE: we do not use `safeSetValue` here, because function
  --       arguments are allowed to have different types than
  --       their eventually preexisting same named variables
  --       outside of the function
  let f (Just a :- _) = setValue a (Pure (SingleArg a))
      f (Nothing :- _) = \x -> x
  let scope' = foldr f -- (\(Just a :- _) -> setValue a (Pure (SingleArg a)))
                     scope
                     args

  -- check the body
  (newBody,τ) <- elaborateMut scname scope' body

  -- get the context and check if some variables are now mutated
  ctx <- use mutTypes
  let ctxElems = getAllElems ctx
  let isMutatingFunction = or [True | WriteSingle _ <- ctxElems]

  -- remove the arguments to this lambda from the context
  let getVar :: (Asgmt JuliaType) -> MTC (Maybe (TeVar, IsMutated))
      getVar (Just a :- t) = do
        mut <- mutTypes %%= popValue a
        case mut of
          Nothing              -> pure (Just (a , NotMutated))
          Just (WriteSingle _) -> pure (Just (a , Mutated))
          Just _               -> pure (Just (a , NotMutated))
      getVar (Nothing :- t) = pure Nothing

  -- call this function on all args given in the signature
  -- and extract those vars that are mutated
  vars_mutationState <- mapM getVar args
  let mutVars = [v | Just (v , Mutated) <- vars_mutationState]
  let mutationsStates = [m | Just (_ , m) <- vars_mutationState]


  -- now, depending on whether we have a mutating lambda,
  -- do the following

  -- case isMutatingFunction of
    --
    -- case I : Mutating
    --
    -- True -> do
      -- assert that now the context is empty
      -- (i.e., no captures were used)
      -- mutTypes <- use mutTypes
      -- case isEmptyDict mutTypes of
      --   False -> throwError (DemutationDefinitionOrderError $ "The variables " <> show mutTypes <> " are not in scope.")
      --   True ->
          -- check that the body is a mutation result
          -- and reorder the resulting tuple
          --
  case τ of
    VirtualMutated vars | [v | (v,NotLocalMutation) <- vars] /= [] -> do

      -- Force the context to be empty
      mutTypes %= (\_ -> def)

      -- get the permutation which tells us how to go
      -- from the order in which the vars are returned by the body
      -- to the order in which the lambda arguments are given
      --
      -- EDIT: We first filter the vars for those which are
      -- actually bound in this lambda
      -- let vars' = [v | v <- vars , v `elem` mutVars]

      -- NOTE: WIP/test -v-
      -- we also check that there is not a mixture of local/nonlocal mutated variable
      let bothVars = [(v) | (v, NotLocalMutation) <- vars , (w,LocalMutation) <- vars, v == w]
      case bothVars of
        [] -> pure ()
        xs -> throwError (DemutationError $ "The variable names " <> show xs <> " are used for both locally mutated and not locally mutated things. This is not allowed. ")

      -- NOTE: WIP/test -v-
      -- let vars' = [v | (v , NotLocalMutation) <- vars]
      let mutVars' = [(v , NotLocalMutation) | v <- mutVars]

      -- logForce $ "Found permutation " <> show vars <> " ↦ " <> show mutVars <>". It is: " <> show σ
      pure ((wrapReorder vars mutVars' newBody) , Mutating mutationsStates)

    --
    -- case II : Not Mutating
    --
    -- simply say that this function is not mutating
    Pure _ -> pure (newBody , Pure UserValue)

    --
    -- case III : locally mutating without return value
    --
    -- this is not allowed
    VirtualMutated vars | [v | (v,NotLocalMutation) <- vars] == []
      -> throwError (DemutationError $ "Found a function which is neither mutating, nor has a return value. This is not allowed."
                                       <> "\nThe function type is: " <> show (VirtualMutated vars)
                                       <> "\nThe function is:\n" <> showPretty body)

    wrongτ -> throwError (DemutationError $ "Expected the result of the body of a mutating lambda to be a virtual mutated value. But it was "
                          <> show wrongτ <> "\n where body is:\n" <> showPretty body)


-------------
-- elaborating a list of terms which are used in individually either mutating, or not mutating places
--

elaborateMutList :: String -> ScopeVar -> Scope -> [(IsMutated , MutDMTerm)] -> MTC ([DMTerm] , [(TeVar, IsLocalMutation)])
elaborateMutList f scname scope mutargs' = do
  ---------
  -- NOTE: Because of #95, currently mutation is DISABLED,
  --       we simulate this by saying that all arguments are to be treated as non mutating
  --
  let mutargs = [(NotMutated,a) | (_ , a) <- mutargs']
  --
  -- NOTE END
  ---------

  -- function for typechecking a single argument
  let checkArg :: (IsMutated , MutDMTerm) -> MTC (DMTerm , Maybe (TeVar, IsLocalMutation))
      checkArg (Mutated , arg) = do
        -- if the argument is given in a mutable position,
        -- it _must_ be a var
        case arg of
          (Var (Just x :- a)) -> do
            -- get the type of this var from the scope
            -- this one needs to be a single arg
            case getValue x scope of
              Nothing -> logForce ("The scope is" <> show scope) >> throwError (DemutationDefinitionOrderError x)
              Just (Pure (SingleArg y)) | x == y -> do
                markMutated scname y
                return (Var (Just x :- a) , Just (x, NotLocalMutation))
              Just (Pure (SingleArg y)) -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the variable " <> show x <> " as argument in a mutable-argument-position. It is bound to the function argument " <> show y <> ", but it is not allowed to use renamed function arguments in such a position.")
              Just (Pure _) -> do
                markMutated scname x
                return (Var (Just x :- a) , Just (x, LocalMutation))
              Just res -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the variable " <> show x <> " as argument in a mutable-argument-position. It has the type " <> show res <> ", which is not allowed here.")

          (Var (Nothing :- a)) -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the term " <> showPretty arg <> " as argument in a mutable-argument-position. Only named variables are allowed here.")

          -- if argument is not a var, throw error
          _ -> throwError (DemutationError $ "When calling the mutating function " <> f <> " found the term " <> showPretty arg <> " as argument in a mutable-argument-position. Only variables are allowed here.")

      checkArg (NotMutated , arg) = do
        -- if the argument is given in an immutable position,
        -- we allow to use the full immut checking
        (arg' , τ) <- elaborateMut scname scope arg

        -- we require the argument to be of pure type
        case τ of
          Pure _ -> pure ()
          Mutating _ -> throwError (DemutationError $ "It is not allowed to pass mutating functions as arguments. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")
          VirtualMutated _ -> throwError (DemutationError $ "It is not allowed to use the result of mutating functions as arguments in other mutating functions. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")
          PureBlackBox -> throwError (DemutationError $ "It is not allowed to pass black boxes as arguments. " <> "\nWhen checking " <> f <> "(" <> show (fmap snd mutargs) <> ")")

        return (arg' , Nothing)

  -- check them
  newArgsWithMutTeVars <- mapM checkArg mutargs
  let newArgs = [te | (te , _) <- newArgsWithMutTeVars]
  let muts = [m | (_ , Just m) <- newArgsWithMutTeVars]

  return (newArgs, muts)



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
    False -> throwError (DemutationDefinitionOrderError $ "The variables " <> show mutTypes <> " are not in scope.")

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
    Pure _ -> throwError (DemutationError $ "Trying to call the pure function '" <> show f <> "' using a mutating call.")
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
          Pure _ -> pure ()
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
    Pure _ -> pure t'
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
