
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
import qualified Prelude as P
import qualified Data.Text as T
import Debug.Trace

data Locked = IsLocked | NotLocked

newtype DMScope = DMScope (Scope Symbol (Locked, DMDelayed))
  deriving Generic

getFromScope :: Symbol -> DMScope -> Maybe DMDelayed
getFromScope k (DMScope h) = (snd <$> (h H.!? k))

setInScope :: MonadError DMException t => Symbol -> DMDelayed -> DMScope -> t DMScope
setInScope k v (DMScope h) = do
    let old = (h H.!? k)
    case old of
      Just (IsLocked,_) -> throwError (VariableMutationError (show k))
      _ -> pure ()
    return $ DMScope (H.insert k (NotLocked, v) h)



{-
instance (MonadError DMException t) => DictLikeM t Symbol (DMDelayed) DMScope where
  getValueM k (DMScope h) = pure $ (snd <$> (h H.!? k))
  setValueM k v (DMScope h) = do
    let old = (h H.!? k)
    case old of
      Just (IsLocked,_) -> throwError (VariableMutationError (show k))
      _ -> pure ()
    return $ DMScope (H.insert k (NotLocked, v) h)
  deleteValueM k (DMScope h) = do
    let old = (h H.!? k)
    case old of
      Just (IsLocked,_) -> throwError (VariableMutationError (show k))
      _ -> pure ()
    return $ DMScope (H.delete k h)
-}

-- instance DictLike Symbol (DMDelayed) (DMScope) where
--   setValue v m (DMScope h) = DMScope (H.insert v m h)
--   deleteValue v (DMScope h) = DMScope (H.delete v h)
--   getValue k (DMScope h) = h H.!? k
--   emptyDict = DMScope H.empty
--   isEmptyDict (DMScope h) = isEmptyDict h
--   getAllKeys (DMScope h) = getAllKeys h


instance Default (DMScope) where
instance Show (DMScope) where
  show (DMScope h) = show $ fst <$> H.toList h

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


lockVars :: [Symbol] -> DMScope -> DMScope
lockVars [] a = traceShow "Locking done" a
lockVars (v:vs) a = lockVar v (lockVars vs a)
  where
    lockVar :: Symbol -> DMScope -> DMScope
    lockVar k (DMScope h) = traceShow ("Locking variable " <> show k) (DMScope (H.insert k (IsLocked, err) h))
      where err = Done $ internalError $ "Trying to execute a computation behind the locked variable '" <> show k <> "'."

      -- let old = h H.!? k
      -- in case old of
      --   Nothing    -> undefined
        -- Just (_,a) -> undefined

--   setValue v m (DMScope h) = DMScope (H.insert v m h)
--   deleteValue v (DMScope h) = DMScope (H.delete v h)
--   getValue k (DMScope h) = h H.!? k


pushChoice :: MonadError DMException t => Symbol -> (DMDelayed) -> DMScope -> t DMScope
pushChoice name ma scope = do
  let oldval = getFromScope name scope
  let newval = case oldval of
        Nothing -> ma
        Just mb -> do
          a <- ma
          b <- mb
          return $ do
            a' <- a
            b' <- b
            return (a' :∧: b')
  setInScope name newval scope


type DMDelayed = Delayed DMException DMScope (TC DMMain)
data Delayed e x a = Done (a) | Later (x -> (Delayed e x a)) | Failed e

-- instance MonadError e (Delayed e x) where
--   throwError = Failed
--   catchError (Done a) handler = (Done a)
--   catchError (Later f) handler = Later f
--   catchError (Failed e) handler = handler e

-- type DelayedS = (Delayed TC (DMScope SensitivityK) DMSensitivity)
-- type DelayedP = (Delayed TC (DMScope PrivacyK) DMPrivacy)

-- type DMSensitivity = DMTypeOf (AnnotatedKind SensitivityK)
-- type DMPrivacy = DMTypeOf (AnnotatedKind PrivacyK)

-- getDelayed :: x -> Delayed x a -> a
-- getDelayed arg (Done a) = a
-- -- getDelayed arg (Later f) = f arg
-- getDelayed arg (Later f) = (f arg) >>= getDelayed arg

extractDelayed :: x -> Delayed e x a -> Either e a
extractDelayed x (Done a) = Right a
extractDelayed x (Later f) = extractDelayed x (f x)
extractDelayed x (Failed e) = Left e

applyDelayedLayerToAll :: x -> Delayed e x a -> Delayed e x a
applyDelayedLayerToAll x d = case extractDelayed x d of
  Left e -> Failed e
  Right x -> Done x

applyDelayedLayer :: x -> Delayed e x a -> Delayed e x a
applyDelayedLayer x (Done a) = Done a
applyDelayedLayer x (Later f) = f x
applyDelayedLayer x (Failed e) = Failed e

instance Functor (Delayed e x) where
  fmap f (Done a) = Done (f a)
  fmap f (Later g) = Later (\x -> fmap f (g x))
  fmap f (Failed e) = Failed e

instance Applicative (Delayed e x) where
  pure a = Done a
  (<*>) (Done g) (Done a) = Done (g a)    -- f (a -> b) -> f a -> f b
  (<*>) (Done g) (Later g') = Later (\x -> (Done g) <*> (g' x))
  (<*>) (Later g) (Done a) = Later (\x -> (g x) <*> (Done a))
  (<*>) (Later g) (Later g') = Later (\x -> (g x) <*> (g' x))
  (<*>) (Failed e) _ = Failed e
  (<*>) _ (Failed e) = Failed e

instance Monad (Delayed e x) where
  return = Done
  x >>= f = insideDelayed x f

insideDelayed :: Delayed e x a -> (a -> Delayed e x b) -> (Delayed e x b)
insideDelayed (Done a) f = (f a)
insideDelayed (Later g) f = Later (\x -> insideDelayed (g x) (\a -> applyDelayedLayer x (f a)))
insideDelayed (Failed e) f = Failed e

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
-- Locking of variables

-- computing free variables of dmterms
--
-- @delayedDepth: the number of Laters we are currently in
-- => `Lam "x". Lam "y". t` (t is in delayedDepth 2)
-- => `App f x` (f is in delayedDepth -1) (x is in delayedDepth 0)
delayedVarsImpl :: Int -> DMTerm -> [Symbol]
delayedVarsImpl d (Sng _ _) = []
delayedVarsImpl d (Apply f args) = delayedVarsImpl (d - 1) f <> mconcat (delayedVarsImpl d <$> args)
delayedVarsImpl d (Arg _ _ _) = error "Found an arg when searching for delayed vars in a user-given DMTerm."
delayedVarsImpl d (Var x _) | d <= 0 = []
delayedVarsImpl d (Var x _) | d > 0 = [x]
delayedVarsImpl d (Lam args body) =
  let delvars = delayedVarsImpl (d P.+ 1) body
  in delvars \\ [a | (a :- _) <- args]
delayedVarsImpl d (LamStar args body) =
  let delvars = delayedVarsImpl (d P.+ 1) body
  in delvars \\ [a | (a :- _, _) <- args]
delayedVarsImpl d (FLet name fun body) =
  let funvars  = delayedVarsImpl d fun
      bodyvars = delayedVarsImpl d body \\ [name]
  in funvars <> bodyvars
delayedVarsImpl d (SLet (name :- _) term body) =
  let termvars  = delayedVarsImpl d term
      bodyvars = delayedVarsImpl d body \\ [name]
  in termvars <> bodyvars

delayedVars :: DMTerm -> [Symbol]
delayedVars t = traceShow (Symbol $ ">>>>> computed delayed vars\n - for term: " <> T.pack (show t) <> "\n - res is: " <> T.pack (show res)) res
  where res = delayedVarsImpl 0 t




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

checkSen' (Var x dτ) scope = do  -- get the term that corresponds to this variable from the scope dict
   traceM ("My scope is: " <> show scope <> " and I want var: " <> show x)
   let delτ = getFromScope x scope
   case delτ of
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
    let scope' = foldM (\sc -> (\(x :- τ) -> setInScope x (checkSens (Arg x τ IsRelevant) scope) sc)) scope xτs
    case runExcept scope' of
      Left e -> Done $ throwError e

      Right scope' -> do
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
    let scope' = foldM (\sc -> (\((x :- τ), rel) -> setInScope x (checkSens (Arg x τ rel) scope) sc)) scope xτs

    case runExcept scope' of
      Left e -> Done $ throwError e

      Right scope' -> do

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
   let scope' = setInScope x (checkSens term scope) scope
   case runExcept scope' of
     Left e -> Done $ throwError e

     Right scope' -> do

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
    checkArg :: DMTerm -> DMScope -> Delayed DMException DMScope (TC (DMMain :& Sensitivity))
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

    -- we compute the variables which are delayed in the args
    varsToLock = mconcat (delayedVars <$> args)

    -- these are locked in the scope while checking f
    mf = checkSens f (lockVars varsToLock scope)

  in do
    -- we typecheck the function, but `apply` our current layer on the Later computation
    -- i.e. "typecheck" means here "extracting" the result of the later computation
    res <- (applyDelayedLayer scope mf)

    -- We do not delay the args, but fully apply the current context to them.
    -- that this gives the correct result should be guaranteed by the check
    -- that delayed & captured variables (of the args) may not be mutated in the function body.
    -- we extract the result of the args computations
    args <- sequence (applyDelayedLayerToAll scope <$> margs)

    -- we merge the different TC's into a single result TC
    return (sbranch_check res args)


checkSen' (FLet fname term body) scope = do

  -- make a Choice term to put in the scope
   let scope' = pushChoice fname (checkSens term scope) scope

   case runExcept scope' of
     Left e -> Done $ throwError e

     Right scope' -> do

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

{-

checkSen' (Tup ts) scope = do
  undefined
   -- τs <- msumS (map (\t -> (checkSens t scope)) ts)
   -- return (DMTup τs)

checkSen' (TLet xs tu body) scope = do
          undefined
          -- TODO: NEWANNOT
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
    checkArg :: DMTerm -> DMScope -> Delayed DMException DMScope (TC (DMMain :& Privacy))
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

    f_check :: Delayed DMException DMScope (TC DMMain) = do
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
   let scope' = setInScope x (checkSens (Arg x dτ NotRelevant) scope) scope

   case runExcept scope' of
     Left e -> Done $ throwError e

     Right scope' -> do

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
          (_, τbody) <- msumTup (mbody, dterm)
          return τbody



checkPri' (FLet fname term body) scope = do

  -- make a Choice term to put in the scope
  -- TODO checkPriv or checkSens?
   let scope' = pushChoice fname (checkSens term scope) scope

   case runExcept scope' of
     Left e -> Done $ throwError e

     Right scope' -> do

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
