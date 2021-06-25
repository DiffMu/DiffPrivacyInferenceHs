
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Typecheck.Operations
import DiffMu.Core.Scope1
import DiffMu.Typecheck.JuliaType
import DiffMu.Typecheck.Constraint.IsFunctionArgument

import qualified Data.HashMap.Strict as H

import Debug.Trace

newtype DMScope = DMScope (Scope Symbol (DMDelayed))
  deriving Generic

instance DictLike Symbol (DMDelayed) (DMScope) where
  setValue v m (DMScope h) = DMScope (H.insert v m h)
  deleteValue v (DMScope h) = DMScope (H.delete v h)
  getValue k (DMScope h) = h H.!? k
  emptyDict = DMScope H.empty
  isEmptyDict (DMScope h) = isEmptyDict h
  getAllKeys (DMScope h) = getAllKeys h

instance Default (DMScope) where

throwDelayedError e = Done $ (throwError e)

-- pushChoice :: (MonadDMTC t) => DMScopes -> Symbol -> [JuliaType] -> DMTerm -> t DMScopes
-- pushChoice scope fname sign term = do
--    let (_, DMScope varscope) = scope
--    scope' <- case (H.lookup fname varscope) of
--                   Nothing -> pushDefinition scope fname (Choice (H.singleton sign term)) -- if there are no other methods just push
--                   Just (Choice d, _) -> do -- else append the method to the Choice term
--                                         (_, scope'') <- popDefinition scope fname
--                                         pushDefinition scope'' fname (Choice (H.insert sign term d))
--                   _ -> throwError (ImpossibleError "Invalid scope entry.")
--    return scope'

pushChoice :: Symbol -> (DMDelayed) -> DMScope -> DMScope
pushChoice name ma scope =
  let oldval = getValue name scope
      newval = case oldval of
        Nothing -> ma
        Just mb -> do
          a <- ma
          b <- mb
          return $ do
            a' <- a
            b' <- b
            return (a' :∧: b')
  in setValue name newval scope


type DMDelayed = Delayed DMScope (TC DMMain)
data Delayed x a = Done (a) | Later (x -> (Delayed x a))

-- type DelayedS = (Delayed TC (DMScope SensitivityK) DMSensitivity)
-- type DelayedP = (Delayed TC (DMScope PrivacyK) DMPrivacy)

-- type DMSensitivity = DMTypeOf (AnnotatedKind SensitivityK)
-- type DMPrivacy = DMTypeOf (AnnotatedKind PrivacyK)

-- getDelayed :: x -> Delayed x a -> a
-- getDelayed arg (Done a) = a
-- -- getDelayed arg (Later f) = f arg
-- getDelayed arg (Later f) = (f arg) >>= getDelayed arg

extractDelayed :: x -> Delayed x a -> a
extractDelayed x (Done a) = a
extractDelayed x (Later f) = extractDelayed x (f x)

applyDelayedLayer :: x -> Delayed x a -> Delayed x a
applyDelayedLayer x (Done a) = Done a
applyDelayedLayer x (Later f) = f x

instance Functor (Delayed x) where
  fmap f (Done a) = Done (f a)
  fmap f (Later g) = Later (\x -> fmap f (g x))

instance Applicative (Delayed x) where
  pure a = Done a
  (<*>) (Done g) (Done a) = Done (g a)    -- f (a -> b) -> f a -> f b
  (<*>) (Done g) (Later g') = Later (\x -> (Done g) <*> (g' x))
  (<*>) (Later g) (Done a) = Later (\x -> (g x) <*> (Done a))
  (<*>) (Later g) (Later g') = Later (\x -> (g x) <*> (g' x))

instance Monad (Delayed x) where
  return = Done
  x >>= f = insideDelayed x f

insideDelayed :: Delayed x a -> (a -> Delayed x b) -> (Delayed x b)
insideDelayed (Done a) f = (f a)
insideDelayed (Later g) f = Later (\x -> insideDelayed (g x) (\a -> applyDelayedLayer x (f a)))

-- insideDelayed (Done a) g = pure $ Done (a >>= g)
-- -- insideDelayed (Later f) g = pure $ Later (f >=> g)
-- insideDelayed (Later f) g = pure $ Later (\x -> f x >>= \y -> insideDelayed y g)

-- onlyDone :: Delayed TC x a -> TC a
-- onlyDone (Done a) = a
-- onlyDone (Later _) = error "Expected Done, but wasn't."

-- onlyLater :: Delayed TC x a -> (a -> TC b) -> Delayed TC x b
-- onlyLater (Done a) g = Later (\_ -> internalError "Expected Later, but wasn't.")
-- onlyLater (Later f) g = Later (\x -> f x >>= \y -> insideDelayed y g)

-- joinLater :: Delayed TC x DMSensitivity -> Delayed TC x DMSensitivity -> Delayed TC x DMSensitivity
-- joinLater (Later f) (Later g) = Later (\x -> do
--                                           (a,b) <- msumTup (f x, g x)

------------------------------------------------------------------------
-- The typechecking function
checkPriv :: DMTerm -> DMScope -> DMDelayed
checkPriv t scope = do
  -- Define the computation to do before checking
  let beforeCheck = do
       γ <- use types
       case γ of -- TODO prettify.
           Left (Ctx (MonCom c)) | H.null c -> return ()
           Right (Ctx (MonCom c)) | H.null c -> return ()
           _   -> throwError (ImpossibleError "Input context for checking must be empty.")
       types .= Right def -- cast to privacy context.

  -- Define the computation to do after checking
  let afterCheck = \res -> do
       γ <- use types
       case γ of
           Right γ -> return res
           Left γ -> error $ "checkPriv returned a sensitivity context!\n" <> "It is:\n" <> show γ <> "\nThe input term was:\n" <> show t

  -- get the delayed value of the sensititivty checking
  res <- checkPri' t scope

  -- combine with the pre/post compututations
  return (beforeCheck >> res >>= afterCheck)



checkSens :: DMTerm -> DMScope -> DMDelayed
checkSens t scope = do
  -- Define the computation to do before checking
  let beforeCheck = do
       γ <- use types
       case γ of -- TODO prettify.
           Left (Ctx (MonCom c)) | H.null c -> return ()
           Right (Ctx (MonCom c)) | H.null c -> return ()
           _   -> throwError (ImpossibleError "Input context for checking must be empty.")
       types .= Left def -- cast to sensitivity context.

  -- Define the computation to do after checking
  let afterCheck = \res -> do
       γ <- use types
       case γ of
           Left γ -> return res
           Right γ -> error $ "checkSens returned a privacy context!\n" <> "It is:\n" <> show γ <> "\nThe input term was:\n" <> show t

  -- get the delayed value of the sensititivty checking
  res <- checkSen' t scope

  -- combine with the pre/post compututations
  return (beforeCheck >> res >>= afterCheck)


--------------------
-- Sensitivity terms


checkSen' :: DMTerm -> DMScope -> DMDelayed

-- TODO: Here we assume that η really has type τ, and do not check it. Should maybe do that.
checkSen' (Sng η τ) scope = Done $ do
  res <- Numeric <$> (Const (constCoeff (Fin η)) <$> (createDMTypeNum τ))
  return (NoFun res)


-- typechecking an op
checkSen' (Op op args) scope = do
  argsdel :: [TC DMMain] <- mapM (\t -> checkSens t scope) args -- check all the args in the delayed monad
  Done $ do
     let handleOpArg (marg, (τ, s)) = do
                                     τ_arg <- marg
                                     unify (NoFun (Numeric τ)) τ_arg
                                     mscale (svar s)
                                     return τ_arg

     -- create a new typeop constraint for op
     -- res is resulting type of the operation when used on types in arg_sens
     -- arg_sens :: [(SMType, Sensitivity)]
     -- types are to be unified with the actual types of the args
     -- Sensitivities are scalars for the argument's context
     (res, arg_sens) <- makeTypeOp op (length args)

     -- make the appropriate unification and scaling, then sum the contexts.
     msumS (map handleOpArg (zip argsdel arg_sens))

     -- return the `res` type given by `makeTypeOp`
     return (NoFun (Numeric res))


-- a special term for function argument variables.
-- those get sensitivity 1, all other variables are var terms
checkSen' (Arg x dτ i) scope = Done $ do τ <- createDMType dτ -- TODO it's actually a subtype of dτ!
                                         setVarS x (WithRelev i (τ :@ SensitivityAnnotation oneId))
                                         return τ

checkSen' (Var x dτ) scope =  -- get the term that corresponds to this variable from the scope dict
   let delτ = getValue x scope
   in case delτ of
     Nothing -> Done $ throwError (VariableNotInScope x)
     Just delτ ->
         case dτ of
           JTAny -> delτ
           dτ -> do
              mτ <- delτ -- get the computation that will give us the type of x
              Done $ do
                 τ <- mτ -- extract the type of x
                 -- if the user has given an annotation
                 -- inferred type must be a subtype of the user annotation
                 dτd <- createDMType dτ
                 addConstraint (Solvable (IsLessEqual (τ, dτd) ))
                 return τ


checkSen' (Lam xτs body) scope =
  -- the body is checked in the toplevel scope, not the current variable scope.
  -- this reflects the julia behaviour
  Later $ \scope -> do
    -- put a special term to mark x as a function argument. those get special tratment
    -- because we're interested in their sensitivity
    let scope' = foldl (\sc -> (\(x :- τ) -> setValue x (checkSens (Arg x τ IsRelevant) scope) sc)) scope xτs

    τr <- checkSens body scope'
    let sign = (sndA <$> xτs)
    Done $ do
      restype <- τr
      xrτs <- getArgList @_ @SensitivityK xτs
      let xrτs' = [x :@ s | (x :@ SensitivityAnnotation s) <- xrτs]
      let τ = (xrτs' :->: restype)
      frees <- getActuallyFreeVars τ
      return (Fun [(ForAll frees τ :@ (Just sign))])


checkSen' (LamStar xτs body) scope =
  -- the body is checked in the toplevel scope, not the current variable scope.
  -- this reflects the julia behaviour
  Later $ \scope -> do
    -- put a special term to mark x as a function argument. those get special tratment
    -- because we're interested in their privacy. put the relevance given in the function signature, too.
    let scope' = foldl (\sc -> (\((x :- τ), rel) -> setValue x (checkSens (Arg x τ rel) scope) sc)) scope xτs

    -- check the function body
    τr <- checkPriv body scope'
    -- extract julia signature
    let sign = (sndA <$> fst <$> xτs)
    Done $ do
      restype <- τr
      -- get inferred types and privacies for the arguments
      xrτs <- getArgList @_ @PrivacyK (fst <$> xτs)
      -- truncate function context to infinity sensitivity
      mtruncateS inftyS
      -- build the type signature and proper ->* type
      let xrτs' = [x :@ p | (x :@ PrivacyAnnotation p) <- xrτs]
      let τ = (xrτs' :->*: restype)
      -- include free variables in a ForAll
      frees <- getActuallyFreeVars τ
      return (Fun [(ForAll frees τ :@ (Just sign))])


checkSen' (SLet (x :- dτ) term body) scope = do

  -- put the computation to check the term into the scope
   let scope' = setValue x (checkSens term scope) scope

   -- check body with that new scope
   result <- checkSens body scope'

   return $ do
     -- TODO
     case dτ of
        JTAny -> return dτ
        dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

     result' <- result
     removeVar @SensitivityK x
     return result'


checkSen' (Apply f args) scope =
  let
    -- check the argument in the given scope,
    -- and scale scope by new variable, return both
    checkArg :: DMTerm -> DMScope -> Delayed DMScope (TC (DMMain :& Sensitivity))
    checkArg arg scope = do
      τ <- checkSens arg scope
      let scaleContext :: TC (DMMain :& Sensitivity)
          scaleContext =
            do τ' <- τ
               s <- newVar
               mscale s
               return (τ' :@ s)
      return (scaleContext)

    sbranch_check mf margs = do
        (τ_sum :: DMMain, argτs) <- msumTup (mf , msumS margs) -- sum args and f's context
        τ_ret <- newVar -- a type var for the function return type
        addConstraint (Solvable (IsFunctionArgument (τ_sum, Fun [(ForAll [] (argτs :->: τ_ret)) :@ Nothing])))
        return τ_ret

    margs = (\arg -> (checkArg arg scope)) <$> args
    mf = checkSens f scope

  in do
    -- we typecheck the function, but `apply` our current layer on the Later computation
    -- i.e. "typecheck" means here "extracting" the result of the later computation
    res <- (applyDelayedLayer scope mf)

    -- we extract the result of the args computations
    args <- sequence margs

    -- we merge the different TC's into a single result TC
    return (sbranch_check res args)


checkSen' (FLet fname term body) scope = do

  -- make a Choice term to put in the scope
   let scope' = pushChoice fname (checkSens term scope) scope

   -- check body with that new scope. Choice terms will result in IsChoice constraints upon ivocation of fname
   result <- checkSens body scope'

   return $ do
     result' <- result
     removeVar @SensitivityK fname
     return result'


checkSen' (Choice d) scope = do
   delCs <- mapM (\t -> checkSens t scope) (snd <$> H.toList d)
   Done $ do
      choices <- msumS delCs
      let combined = foldl (:∧:) (Fun []) choices
      return combined


checkSen' (Phi cond ifbr elsebr) scope = do
   ifd <- checkSens ifbr scope
   elsed <- checkSens elsebr scope
   condd <- checkSens cond scope

   mcond <- Done $ do
        τ_cond <- condd
        mscale inftyS
        return τ_cond

   Done $ do
      τ_sum <- msumS [ifd, elsed, mcond]
      (τif, τelse) <- case τ_sum of
                           (τ1 : τ2 : _) -> return (τ1, τ2)
                           _ -> throwError (ImpossibleError "Sum cannot return empty.")
      τ <- newVar
      addConstraint (Solvable (IsSupremum (τif, τelse, τ)))
      return τ



checkSen' (Tup ts) scope = do
  τsd <- mapM (\t -> (checkSens t scope)) ts
  Done $ do
     -- check tuple entries and sum contexts
     τsum <- msumS τsd

     -- ensure nothing that is put in a tuple is a function
     let makeNoFun ty = do v <- newVar
                           unify (NoFun v) ty
                           return v
     τnf <- mapM makeNoFun τsum

     -- return the tuple.
     return (NoFun (DMTup τnf))


checkSen' (TLet xs term body) original_scope = do

  -- add all variables bound in the tuple let as args-checking-commands to the scope
  -- TODO: do we need to make sure that we have unique names here?
  let addarg scope (x :- τ) = setValue x (checkSens (Arg x τ NotRelevant) original_scope) scope
  let scope_with_args = foldl addarg original_scope xs

  -- check the body in the scope with the new args
  cbody <- checkSens body scope_with_args

  -- append the computation of removing the args from the context again, remembering their types
  -- and sensitivities
  let cbody' = do
        τ <- cbody
        xs_types_sens <- mapM (removeVar @SensitivityK) [x | (x :- _) <- xs]
        let xs_types_sens' = [ (ty,sens) | WithRelev _ (ty :@ SensitivityAnnotation sens) <- xs_types_sens ]
        return (τ,xs_types_sens')

  -- the computation for checking the term
  cterm <- checkSens term original_scope

  -- merging the computations and matching inferred types and sensitivities
  Done $ do
    -- create a new var for scaling the term context
    s <- newVar

    -- extract both TC computations
    -- (the computation for the term is scaled with s)
    ((τbody,xs_types_sens), τterm) <- msumTup (cbody', (cterm <* mscale s))

    -- split the sens/type pairs of the arguments
    let (xs_types , xs_sens) = unzip xs_types_sens

    -- helper function for making sure that type is a nofun, returning the nofun component
    let makeNoFun ty = do v <- newVar
                          unify (NoFun v) ty
                          return v

    -- here we use `makeNoFun`
    -- we make all tuple component types into nofuns
    xs_types' <- mapM makeNoFun xs_types

    -- and require that the type of the term is actually this tuple type
    τterm ==! NoFun (DMTup xs_types')

    -- finally we need make sure that our scaling factor `s` is the maximum of the tuple sensitivities
    s ==! maxS xs_sens

    -- and we return the type of the body
    return τbody


checkSen' (Loop it cs (xi, xc) body) scope = do
   niter <- case it of
                  Iter fs stp ls -> return (opCeil ((ls `opSub` (fs `opSub` (Sng 1 JTNumInt))) `opDiv` stp))
                  _ -> return (Arg xi JTNumInt NotRelevant) --throwDelayedError (ImpossibleError "Loop iterator must be an Iter term.") - TODO

   cniter <- checkSens niter scope
   ccs <- checkSens cs scope

   -- add iteration and capture variables as args-checking-commands to the scope
   -- TODO: do we need to make sure that we have unique names here?
   let scope' = setValue xi (checkSens (Arg xi JTNumInt NotRelevant) scope) scope
   let scope'' = setValue xc (checkSens (Arg xc JTAny IsRelevant) scope) scope'

   -- check body term in that new scope
   cbody <- checkSens body scope''

   -- append the computation of removing the args from the context again, remembering their types
   -- and sensitivities
   let cbody' = do
         τ <- cbody
         WithRelev _ (τi :@ si) <- removeVar @SensitivityK xi
         WithRelev _ (τc :@ sc) <- removeVar @SensitivityK xc
         return (τ, (τi, si), (τc, sc))

   Done $ do
      -- add scalars for iterator, capture and body context
      -- we compute their values once it is known if the number of iterations is const or not.
      sit <- newVar
      scs <- newVar
      sb <- newVar

      -- scale and sum contexts
      (τit, τcs, (τb, (τbit, sbit), (τbcs, sbcs))) <- msum3Tup (cniter <* mscale sit, ccs <* mscale scs, cbody' <* mscale sb)

      addConstraint (Solvable (IsLessEqual (τit, τbit))) -- number of iterations must match type requested by body
      addConstraint (Solvable (IsLessEqual (τcs, τbcs))) --  capture type must match type requested by body
      addConstraint (Solvable (IsLessEqual (τb, τbcs))) -- body output type must match body capture input type
      addConstraint (Solvable (IsLoopResult ((sit, scs, sb), sbcs, τit))) -- compute the right scalars once we know if τ_iter is const or not.

      return τb


checkSen' (MCreate n m (x1, x2) body) scope =
   let setDim :: TC DMMain -> Sensitivity -> TC DMMain
       setDim tm s = do
          τ <- tm -- check dimension term
          unify τ (NoFun (Numeric (Const s DMInt))) -- dimension must be const integral
          mscale zeroId
          return τ

       checkBody :: TC DMMain -> Sensitivity -> Sensitivity -> TC DMMain
       checkBody bm nv mv = do
          τ <- bm -- check body lambda

          mscale (nv ⋅! mv) -- scale with dimension penalty

          -- remove index variables from the scope, ignore their sensitivity
          WithRelev _ (x1τ :@ _) <- removeVar @SensitivityK x1
          WithRelev _ (x2τ :@ _) <- removeVar @SensitivityK x2

          -- input vars must be integer
          addConstraint (Solvable (IsLessEqual (x1τ, NoFun (Numeric (NonConst DMInt)))))
          addConstraint (Solvable (IsLessEqual (x2τ, NoFun (Numeric (NonConst DMInt)))))

          return τ
   in do

       mn <- checkSens n scope
       mm <- checkSens m scope
       mbody <- checkSens body scope

       Done $ do
          -- variables for matrix dimension
          nv <- newVar
          mv <- newVar

          (τbody, _, _) <- msum3Tup (checkBody mbody nv mv, setDim mn nv, setDim mm mv)

          -- matrix entries cannot be functions.
          τ <- newVar
          unify τbody (NoFun τ)

          nrm <- newVar -- variable for norm
          return (NoFun (DMMat nrm U nv mv τ))


checkSen' (ClipM c m) scope = do
   mb <- checkSens m scope -- check the matrix
   Done $ do
      τb <- mb

      -- variables for norm and clip parameters and dimension
      nrm <- newVar
      clp <- newVar
      n <- newVar
      m <- newVar

      -- set correct matrix type
      unify τb (NoFun (DMMat nrm clp n m (Numeric DMData)))

      -- change clip parameter to input
      return (NoFun (DMMat nrm c n m (Numeric DMData)))

-- Everything else is currently not supported.
checkSen' t scope = (throwDelayedError (UnsupportedTermError t))


--------------------------------------------------------------------------------
-- Privacy terms

checkPri' :: DMTerm -> DMScope -> DMDelayed

checkPri' (Ret t) scope = do
   mτ <- checkSens t scope
   Done $ do
      τ <- mτ
      mtruncateP inftyP
      return τ

-- TODO it is ambiguous if this is an application of a LamStar or an application of a Lam followed by Return.
-- we probably should resolve IsFunctionArgument ( T -> T, S ->* S) by setting S's privacies to infinity.
checkPri' (Apply f args) scope =
  let
    -- check the argument in the given scope,
    -- and scale scope by new variable, return both
    checkArg :: DMTerm -> DMScope -> Delayed DMScope (TC (DMMain :& Privacy))
    checkArg arg scope = do
      τ <- checkSens arg scope
      let restrictTruncateContext :: TC (DMMain :& Privacy)
          restrictTruncateContext =
            do τ' <- τ
               restrictAll oneId -- sensitivity of everything in context must be <= 1
               p <- newPVar
               mtruncateP p
               return (τ' :@ p)
      return (restrictTruncateContext)

    sbranch_check mf margs = do
        (τ_sum :: DMMain, argτs) <- msumTup (mf , msumP margs) -- sum args and f's context
        τ_ret <- newVar -- a type var for the function return type
        addConstraint (Solvable (IsFunctionArgument (τ_sum, Fun [(ForAll [] (argτs :->*: τ_ret)) :@ Nothing])))
        return τ_ret

    margs = (\arg -> (checkArg arg scope)) <$> args

    f_check :: Delayed DMScope (TC DMMain) = do
       -- we typecheck the function, but `apply` our current layer on the Later computation
       -- i.e. "typecheck" means here "extracting" the result of the later computation
       res <- (applyDelayedLayer scope (checkSens f scope))
       Done $ do
                r <- res
                mtruncateP inftyP -- truncate f's context to ∞
                return r

  in do
    -- extract result of f typechecking
    ff <- f_check

    -- we extract the result of the args computations
    args <- sequence margs

    -- we merge the different TC's into a single result TC
    return (sbranch_check ff args)


checkPri' (SLet (x :- dτ) term body) scope = do
  -- this is the bind rule.
  -- as it does not matter what sensitivity/privacy x has in the body, we put an Arg term in the scope
  -- and later discard its annotation.
   let scope' = setValue x (checkSens (Arg x dτ NotRelevant) scope) scope

   -- check body with that new scope
   dbody <- checkPriv body scope'
   mbody <- Done $ do
                   τ <- dbody
                   -- discard x from the context, never mind it's inferred annotation
                   removeVar @PrivacyK x
                   return τ

   -- check term with old scope
   dterm <- checkPriv term scope

   return $ do
     -- TODO
     case dτ of
        JTAny -> return dτ
        dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

     -- sum contexts
     (τbody, τterm) <- msumTup (mbody, dterm)

     -- make sure that τterm is not a functiontype
     -- this is necessary because elsewise it might be capturing variables
     -- which we do not track here. (We can only track that if we put the
     -- computation for checking the term itself into the scope, instead
     -- of an arg representing it. But this would not work with the bind rule.)
     -- See https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/18
     τnofun <- newVar
     unify τbody (NoFun τnofun)

     -- return the type of this bind expression
     return τbody



checkPri' (FLet fname term body) scope = do

  -- make a Choice term to put in the scope
  -- TODO checkPriv or checkSens?
   let scope' = pushChoice fname (checkSens term scope) scope

   -- check body with that new scope. Choice terms will result in IsChoice constraints upon ivocation of fname
   result <- checkPriv body scope'

   return $ do
     result' <- result
     removeVar @PrivacyK fname
     return result'

checkPri' (Gauss rp εp δp f) scope =
  let
   setParam :: TC DMMain -> Sensitivity -> TC ()
   setParam dt v = do -- parameters must be const numbers.
      τ <- dt
      τv <- newVar
      unify τ (NoFun (Numeric (Const v τv)))
      mtruncateP zeroId
      return ()

   setBody df (ε, δ) r = do
      -- extract f's type from the TC monad
      τf <- df
      -- interesting input variables must have sensitivity <= r
      restrictInteresting r
      -- interesting output variables are set to (ε, δ), the rest is truncated to ∞
      mtruncateP inftyP
      (ivars, itypes) <- getInteresting
      mapM (\(x, (τ :@ _)) -> setVarP x (WithRelev IsRelevant (τ :@ PrivacyAnnotation (ε, δ)))) (zip ivars itypes)
      -- return type is a privacy type.
      return τf
   in do
      -- check all the parameters and f, extract the TC monad from the Delayed monad.
      drp <- checkSens rp scope
      dεp <- checkSens εp scope
      dδp <- checkSens δp scope
      df <- checkSens f scope

      Done $ do
         -- create variables for the parameters
         v_ε :: Sensitivity <- newVar
         v_δ :: Sensitivity <- newVar
         v_r :: Sensitivity <- newVar

         -- restrict interesting variables in f's context to v_r
         let mf = setBody df (v_ε, v_δ) v_r

         let mr = setParam drp v_r
         let mε = setParam dεp v_ε
         let mδ = setParam dδp v_δ

         (τf, _) <- msumTup (mf, msum3Tup (mr, mε, mδ))

         τgauss <- newVar
         addConstraint (Solvable (IsGaussResult (τgauss, τf))) -- we decide later if its gauss or mgauss according to return type

         return τgauss

checkPri' t scope = checkPriv (Ret t) scope -- secretly return if the term has the wrong color.

{-
checkPri' (Loop it cs (xi, xc) b) scope = do
  undefined
  -- TODO: NEWANNOT
  {-
   niter <- case it of
                  Iter fs stp ls -> return (opCeil ((ls `opSub` (fs `opSub` (Sng 1 JTNumInt))) `opDiv` stp))
                  _ -> throwError (ImpossibleError "Loop iterator must be an Iter term.")

   let miter = do
          τ <- checkSens niter scope
          mtruncateP zeroId
          return τ
   let mcaps = do
          τ <- checkSens cs scope
          mtruncateP inftyP
          return τ

   let setInteresting :: ([Symbol],[DMType],[Privacy]) -> Sensitivity -> TC ()
       setInteresting (xs, τs, ps) n = do
          let ε = maxS (map fst ps)
          let δ = maxS (map snd ps)

          δn :: Sensitivity <- newVar -- we can choose this freely!
          addConstraint (Solvable (IsLessEqual (δn, oneId :: Sensitivity))) -- otherwise we get a negative ε...

          -- compute the new privacy for the xs according to the advanced composition theorem
          let two = oneId ⋆! oneId
          let newp = (two ⋅! (ε ⋅! (sqrt (two ⋅! (n ⋅! (minus (ln oneId) (ln δn)))))), δn ⋆! (n ⋅! δ)) -- TODO

          mapM (\(x, τ) -> setVarP x (WithRelev IsRelevant (τ :@ newp))) (zip xs τs)
          return ()

   let mbody = do
         scope' <- pushDefinition scope xi (Arg xi JTNumInt NotRelevant)
         scope'' <- pushDefinition scope' xc (Arg xc JTAny IsRelevant)
         τ <- checkPriv b scope''
         _ <- removeVar @PrivacyK xi -- TODO do something?
         _ <- removeVar @PrivacyK xc -- TODO unify with caps type?

         interesting <- getInteresting
         mtruncateP inftyP

         n <- newVar
         setInteresting interesting n
         return (τ, n)

   (τit, τcs, (τb, n)) <- msum3Tup (miter, mcaps, mbody)

   unify τit (Numeric (Const n DMInt)) -- number of iterations must be constant integer

   addConstraint (Solvable (IsLessEqual (τb, τcs))) -- body output type must match body capture input type

   return τb
   -}

-}
