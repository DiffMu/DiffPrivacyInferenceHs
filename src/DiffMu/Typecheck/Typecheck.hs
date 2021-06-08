
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

--------------------
-- Sensitivity terms

checkSen' :: DMTerm -> DMScope -> DMDelayed

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


-- TODO: Here we assume that η really has type τ, and do not check it. Should maybe do that.
checkSen' (Sng η τ) scope = Done $ do
  res <- Numeric <$> (Const (constCoeff (Fin η)) <$> (createDMTypeNum τ))
  return (NoFun res)

  {-


-- a special term for function argument variables.
-- those get sensitivity 1, all other variables are var terms

-- TODO!!!! Get interestingness flag!
checkSen' (Arg x dτ i) scope = do τ <- createDMType dτ -- TODO subtype!
                                  setVarS x (WithRelev i τ)
                                  return (Done τ)
                                  -- setVarS x (WithRelev i (NoFun (undefined :@ constCoeff (Fin 1)))) --(τ :@ constCoeff (Fin 1)))
                                  -- returnNoFun τ

checkSen' (Var x dτ) scope = do -- get the term that corresponds to this variable from the scope dict
                                let (τ) = getValue x scope
                                case τ of
                                  Nothing -> throwError (VariableNotInScope x)
                                  Just τ ->

                                -- check the term in the new, smaller scope'
                                -- τ <- checkSens vt scope'

                                    insideDelayed τ $ \τ ->
                                      case dτ of
                                        JTAny -> return τ
                                        dτ -> do
                                          -- if the user has given an annotation
                                          -- inferred type must be a subtype of the user annotation
                                          dτd <- createDMType dτ
                                          addConstraint (Solvable (IsLessEqual (τ, dτd) ))
                                          return ( τ)

-- typechecking an op
checkSen' (Op op args) scope =
  -- We create a helper function, which infers the type of arg, unifies it with the given τ
  -- and scales the current context by s.
  let checkOpArg (arg,(τ,s)) = do
        τ_arg <- checkSens arg scope >>= onlyDone
        unify (NoFun (Numeric τ :@ SensitivityAnnotation (svar s))) τ_arg
        -- mscale (svar s)
  in do
    -- We get create a new typeop constraint for op
    (res,arg_sens) <- makeTypeOp op (length args)

    -- We call our helper function `checkOpArg` on the argument-terms, zipped with the
    -- type(variables), sensitivities returned by `makeTypeOp`
    _ <- msumS ((checkOpArg <$> (zip args arg_sens)))

    -- We return the `res` type given by `makeTypeOp`
    returnNoFun (Numeric res)


checkSen' (Phi cond ifbr elsebr) scope =
   let mcond = do
        τ_cond <- checkSens cond scope >>= onlyDone
        mscale inftyS
        return τ_cond
   in do
      τ_sum <- msumS [(checkSens ifbr scope >>= onlyDone), (checkSens elsebr scope >>= onlyDone), mcond]
      (τif, τelse) <- case τ_sum of
                           (τ1 : τ2 : _) -> return (τ1, τ2)
                           _ -> throwError (ImpossibleError "Sum cannot return empty.")
      τ <- newVar
      addConstraint (Solvable (IsSupremum (τ, τif, τelse)))
      return (Done τ)

-}

checkSen' (Arg x dτ i) scope = Done $ do τ <- createDMType dτ -- TODO subtype!
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

{-
{-
checkSen' (LamStar xτs body) scope = do

  -- put a special term to mark x as a function argument. those get special tratment
  -- because we're interested in their sensitivity
  scope' <- foldM (\sc -> (\((x :- τ), i) -> pushDefinition sc x (Arg x τ i))) scope xτs

  -- the body is checked in the toplevel scope, not the current variable scope.
  -- this reflects the julia behaviour
  let (topscope, _) = scope'
  τr <- checkPriv body (topscope, topscope)


  xrτs <- getArgList (map fst xτs)

  -- TODO: As it currently stands the context which is returned here is something like 's ↷ | Γ |_∞', not wrong, but unnecessary?
  mtruncateS inftyS

  -- get the julia signature from xτs
  let sign = ((sndA . fst) <$> xτs)
  returnFun (Just sign) (xrτs :->*: τr)
-}

-}
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


{-
  let checkFArg :: DMTerm -> TC (DMSensitivity)
      checkFArg arg = do
          τ <- checkSens arg scope >>= getDelayed scope
          return τ
  let margs = checkFArg <$> args
  let mf = checkSens f scope >>= getDelayed scope
  τ_sum <- msumS (mf : margs) -- sum args and f's context
  (τ_lam, argτs) <- case τ_sum of
                          (τ : τs) -> return (τ, τs)
                          [] -> throwError (ImpossibleError "Sum cannot return empty list.")
  τ_ret <- newVar -- a type var for the function return type

  -- addConstraint (Solvable (IsLessEqual (τ_lam, Fun [(argτs :->: τ_ret) :@ (Nothing, oneId)])))

  addConstraint (Solvable (IsFunctionArgument (τ_lam, Fun [(ForAll [] (argτs :->: τ_ret)) :@ (Nothing, oneId)])))
  return (Done τ_ret)

  {-
  let
   -- check a single argument, scale its context with the corresponding sensitivity variable
   checkFArg :: DMTerm -> Sensitivity -> TC DMType
   checkFArg arg s = do
      τ <- checkSens arg scope
      mscale s
      return τ
   in do
      svars :: [Sensitivity] <- mapM (\x -> newVar) args -- create an svar for each argument
      let margs = zipWith checkFArg args svars -- check args and scale with their respective svar

      let mf = checkSens f scope -- check function term

      τ_sum <- msumS (mf : margs) -- sum args and f's context
      (τ_lam, argτs) <- case τ_sum of
                             (τ : τs) -> return (τ, (zipWith (:@) τs svars))
                             [] -> throwError (ImpossibleError "Sum cannot return empty list.")

      τ_ret <- newVar -- a type var for the function return type

      -- f's type must be subtype of a choice arrow with matching arg types.
      addConstraint (Solvable (IsLessEqual (τ_lam, DMChoice [(argτs :->: τ_ret) :@ (Nothing, oneId)])))
      return τ_ret

-}

-}
checkSen' (FLet fname sign term body) scope = do

  -- make a Choice term to put in the scope
   let scope' = pushChoice fname (checkSens term scope) scope
   -- sign term

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

{-

  {-
{-

checkSen' (Tup ts) scope = do
  undefined
   -- τs <- msumS (map (\t -> (checkSens t scope)) ts)
   -- return (DMTup τs)

checkSen' (TLet xs tu body) scope = do
          undefined
          -- TODO: NEWANNOT
         {-
   --TODO chekc uniqueness
   maxs <- newVar

   let mtup = do -- checn and scale
          τ <- checkSens tu scope
          mscale maxs
          return τ

   let mbody = do
          scope' <- foldM (\sc -> (\(x :- τ) -> pushDefinition sc x (Arg x τ IsRelevant))) scope xs
          let xnames = map fstA xs

          τb <- checkSens body scope'

          sτs <- mapM (removeVar @SensitivityK) xnames -- get inference result for xs

          let s = maxS (map sndAnnI sτs) -- set maxs to maximum of inferred sensitivites
          s ==! maxs

          return (τb, (map fstAnnI sτs))

   ((τb, τs), τt) <- msumTup (mbody, mtup)

   unify τt (DMTup τs) -- set correct tuple type

   return τb

checkSen' (Loop it cs (xi, xc) b) scope = do
   niter <- case it of
                  Iter fs stp ls -> return (opCeil ((ls `opSub` (fs `opSub` (Sng 1 JTNumInt))) `opDiv` stp))
                  _ -> throwError (ImpossibleError "Loop iterator must be an Iter term.")

   let checkScale :: DMTerm -> TC (DMSensitivity, Sensitivity)
       checkScale term = do
          τ <- checkSens term scope
          s <- newVar
          mscale s
          return (τ, s)

   let mbody = do
         scope' <- pushDefinition scope xi (Arg xi JTNumInt NotRelevant)
         scope'' <- pushDefinition scope' xc (Arg xc JTAny IsRelevant)
         τ <- checkSens b scope
         xii <- removeVar @SensitivityK xi
         xci <- removeVar @SensitivityK xc
         s <- newVar
         mscale s
         return (τ, s, xii, xci)

   ((τit, sit), (τcs, scs), (τb, sb, (WithRelev _ (τbit :@ sbit)), (WithRelev _ (τbcs :@ sbcs)))) <- msum3Tup (checkScale niter, checkScale cs, mbody)

   addConstraint (Solvable (IsLessEqual (τit, τbit))) -- number of iterations must match typer equested by body
   addConstraint (Solvable (IsLessEqual (τcs, τbcs))) --  capture type must match type requested by body
   addConstraint (Solvable (IsLessEqual (τb, τbcs))) -- body output type must match body capture input type
   addConstraint (Solvable (IsLoopResult ((sit, scs, sb), sbcs, τit))) -- compute the right scalars once we know if τ_iter is const or not.

   return τb

          -}


checkSen' (MCreate n m body) scope =
   let setDim :: DMTerm -> Sensitivity -> TC (DMSensitivity)
       setDim t s = do
          τ <- checkSens t scope -- check dimension term
          unify τ (NoFun (Numeric (Const s DMInt) :@ zeroId)) -- dimension must be integral
          -- mscale zeroId
          return τ

       checkBody :: Sensitivity -> Sensitivity -> TC (DMType)
       checkBody nv mv = do
          τ <- checkSens body scope -- check body lambda

          -- unify with expected type to set sensitivity (dimension penalty) and extract return type
          τbody <- newVar
          let τ_expected = Fun [(ForAll [] ([NoFun (Numeric (NonConst DMInt) :@ SensitivityAnnotation inftyS) , NoFun (Numeric (NonConst DMInt) :@ SensitivityAnnotation inftyS)] :->: (NoFun (τbody :@ SensitivityAnnotation oneId))) :@ (Nothing , (nv ⋅! mv)))]
          τ_expected ==! τ
          return τbody

          -- mscale (nv ⋅! mv) -- scale with dimension penalty

          -- τbody <- case τ of -- extract body lambda return type
          --               (Fun [xss :->: τret]) -> return τret
          --               _ -> throwError (ImpossibleError "MCreate term must have Arr argument.")

          -- -- body lambda input vars must be integer
          -- addConstraint (Solvable (IsLessEqual (τ, [((Numeric (NonConst DMInt)) :@ inftyS), ((Numeric (NonConst DMInt)) :@ inftyS)] :->: τbody)))

          -- return τbody
   in do
       -- variables for matrix dimension
       nv <- newVar
       mv <- newVar

       (τbody, _, _) <- msum3Tup (checkBody nv mv, setDim n nv, setDim m mv)

       -- τbody <- case sum of -- extract element type from constructing lambda
       --            (τ : _) -> return τ
       --            _ -> throwError (ImpossibleError "?!")

       nrm <- newVar -- variable for norm
       returnNoFun (DMMat nrm U nv mv τbody)

checkSen' (ClipM c m) scope = do
   τb <- checkSens m scope -- check the matrix

   -- variables for norm and clip parameters and dimension
   nrm <- newVar
   clp <- newVar
   n <- newVar
   m <- newVar

   -- set correct matrix type
   η <- newVar
   unify τb (NoFun (DMMat nrm clp n m (Numeric DMData) :@ SensitivityAnnotation η))

   -- change clip parameter to input
   return (NoFun (DMMat nrm c n m (Numeric DMData) :@ SensitivityAnnotation η))
-}

-}
-}
-- Everything else is currently not supported.
checkSen' t scope = (throwDelayedError (UnsupportedTermError t))


--------------------------------------------------------------------------------
-- Privacy terms

checkPri' :: DMTerm -> DMScope -> DMDelayed
checkPri' = undefined

  {-
checkPri' (Ret t) scope = do
   τ <- checkSens t scope
   mtruncateP inftyP
   return (Return τ)

checkPri' (Gauss rp εp δp f) scope =
  let
   setParam :: DMTerm -> Sensitivity -> TC ()
   setParam t v = do -- parameters must be const numbers.
      τ <- checkSens t scope
      sv :: Sensitivity <- newVar
      τv <- newVar
      unify τ (NoFun (Numeric (Const v τv) :@ SensitivityAnnotation sv))
      mtruncateP zeroId
      return ()
   checkBody (ε, δ) r = do
      τf <- checkSens f scope
      -- interesting input variables must have sensitivity <= r
      restrictInteresting r
      -- interesting output variables are set to (ε, δ), the rest is truncated to ∞
      mtruncateP inftyP
      (ivars, itypes) <- getInteresting
      mapM (\(x, τ) -> setVarP x (WithRelev IsRelevant (Trunc (PrivacyAnnotation (ε, δ)) τ))) (zip ivars itypes)
      -- return type is a privacy type.
      pv <- newPVar
      return (Trunc (PrivacyAnnotation (pv)) τf)
   in do
      v_ε :: Sensitivity <- newVar
      v_δ :: Sensitivity <- newVar
      v_r :: Sensitivity <- newVar

      let mf = checkBody (v_ε, v_δ) v_r

      let mr = setParam rp v_r
      let mε = setParam εp v_ε
      let mδ = setParam δp v_δ

      (τf, _) <- msumTup (mf, msum3Tup (mr, mε, mδ))

      τgauss <- newVar
      addConstraint (Solvable (IsGaussResult (τgauss, τf))) -- we decide later if its gauss or mgauss according to return type

      return τgauss



  {-
checkPri' (SLet (x :- dτ) term body) scope =
  -- push x to scope, check body, and discard x from the result context.
  -- this is the bind rule; as we expect the body to be a privacy term we don't need to worry about x's sensitivity
  let mbody = do
         scope' <- pushDefinition scope x (Arg x dτ IsRelevant)
         τ <- checkPriv body scope'
         _ <- removeVar @PrivacyK x
         return τ
  in do
     -- TODO this requires saving the annotation in the dict.
     case dτ of
          JTAny -> return dτ
          dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

     sum <- msumP [mbody, (checkPriv term scope)]
     res <- case sum of
                    [τ::DMType,_] -> return τ
                    _ -> throwError (ImpossibleError "?!")

     return res
-}

checkPri' (FLet fname sign term body) scope = do -- this is the same as with checkSens
  -- make a Choice term to put in the scope
   scope' <- pushChoice scope fname sign term

   -- check body with that new scope. Choice terms will result in IsChoice constraints upon ivocation of fname
   result <- checkPriv body scope'
   _ <- removeVar @PrivacyK fname
   return result


{-

checkPri' (Phi cond ifbr elsebr) scope = -- this is the same as with checkSens
   let mcond = do
        τ_cond <- checkSens cond scope -- this one must be a sensitivity term.
        mscale inftyS
        return τ_cond
   in do
      τ_sum <- msumP [(checkPriv ifbr scope), (checkPriv elsebr scope), mcond]
      (τif, τelse) <- case τ_sum of
                           (τ1 : τ2 : _) -> return (τ1, τ2)
                           _ -> throwError (ImpossibleError "Sum cannot return empty.")
      τ <- newVar
      addConstraint (Solvable (IsSupremum (τ, τif, τelse)))
      return τ

-}

checkPri' (Apply f args) scope = let
   -- check a single argument, scale its context with the corresponding sensitivity variable
   checkFArg :: DMTerm -> Privacy -> TC (DMTypeOf (AnnotatedKind PrivacyK))
   checkFArg arg p = do
      τ <- checkSens arg scope
      addConstraint (Solvable (SetMultiplier (τ, oneId::Sensitivity)))
      restrictAll oneId -- sensitivity of everything in context must be <= 1
      mtruncateP p -- truncate it's context to p
      return (Trunc (PrivacyAnnotation p) τ) -- also set it's type's annotation to p for putting it into the signature below

   checkF :: TC (DMSensitivity)
   checkF = do
      τ <- checkSens f scope
      mtruncateP inftyP
      return τ

   in do
      εvars :: [Sensitivity] <- mapM (\x -> newVar) args -- create privacy variables for all arguments
      δvars :: [Sensitivity] <- mapM (\x -> newVar) args
      let margs = zipWith checkFArg args (zip εvars δvars) -- check f and args and truncate with their respective pvar

      (τ_lam, argτs) <- msumTup (checkF, (msumP margs)) -- sum args and f's context

      τ_ret <- newVar -- a type var for the function return type

      addConstraint (Solvable (IsFunctionArgument (τ_lam, Fun [(ForAll [] (argτs :->*: τ_ret)) :@ (Nothing, oneId)])))
      return τ_ret
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

checkPri' t scope = checkPriv (Ret t) scope -- secretly return if the term has the wrong color.
-}
