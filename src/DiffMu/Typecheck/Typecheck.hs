
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Typecheck.Operations
import DiffMu.Core.DelayedScope
import DiffMu.Typecheck.JuliaType
import DiffMu.Typecheck.Constraint.IsFunctionArgument
import DiffMu.Typecheck.Constraint.IsJuliaEqual
import DiffMu.Typecheck.Constraint.CheapConstraints

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace

import Data.IORef
import System.IO.Unsafe



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
           ctx   -> impossible $ "Input context for checking must be empty. But I got:\n" <> show ctx
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
  return (beforeCheck >> withLogLocation "Check" res >>= afterCheck)



checkSens :: DMTerm -> DMScope -> DMDelayed
checkSens t scope = do
  -- Define the computation to do before checking
  let beforeCheck = do
       γ <- use types
       case γ of -- TODO prettify.
           Left (Ctx (MonCom c)) | H.null c -> return ()
           Right (Ctx (MonCom c)) | H.null c -> return ()
           ctx   -> impossible $ "Input context for checking must be empty. But I got:\n" <> show ctx <> "\nThe term is:\n" <> show t
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
  return (beforeCheck >> withLogLocation "Check" res >>= afterCheck)


--------------------
-- Sensitivity terms


checkSen' :: DMTerm -> DMScope -> DMDelayed

-- TODO: Here we assume that η really has type τ, and do not check it. Should maybe do that.
checkSen' (Sng η τ) scope = done $ do
  res <- Numeric <$> (Const (constCoeff (Fin η)) <$> (createDMTypeNum τ))
  return (NoFun res)


-- typechecking an op
checkSen' (Op op args) scope = do
  argsdel :: [TC DMMain] <- mapM (\t -> checkSens t scope) args -- check all the args in the delayed monad
  done $ do
     let handleOpArg (marg, (τ, s)) = do
                                     τ_arg <- marg
                                     unify (NoFun τ) τ_arg
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
     return (NoFun res)


-- a special term for function argument variables.
-- those get sensitivity 1, all other variables are var terms
checkSen' (Arg x dτ i) scope = done $ do
                                         -- the inferred type must be a subtype of the user annotation, if given.
                                         τs <- newVar
                                         τ <- case dτ of
                                             JuliaType "Any" -> return τs
                                             _ -> do τc <- createDMType dτ -- TODO it's actually a subtype of dτ!
                                                     addConstraint (Solvable (IsLessEqual (τs, τc)))
                                                     return τs


                                         -- put the variable in the Γ context with sensitivity 1
                                         setVarS x (WithRelev i (τ :@ SensitivityAnnotation oneId))
                                         return τ

checkSen' (Var (x :- dτ)) scope =  -- get the term that corresponds to this variable from the scope dict
   let delτ = getValue x scope
   in case delτ of
     Nothing -> done $ throwError (VariableNotInScope x)
     Just delτ ->
         case dτ of
           JTAny -> delτ
           dτ -> do
              mτ <- delτ -- get the computation that will give us the type of x
              done $ do
                 τ <- mτ -- extract the type of x
                 -- if the user has given an annotation
                 -- inferred type must be a subtype of the user annotation
                 dτd <- createDMType dτ
                 addConstraint (Solvable (IsLessEqual (τ, dτd)))
                 return τ

checkSen' (Lam xτs body) scope =
  -- the body is checked in the toplevel scope, not the current variable scope.
  -- this reflects the julia behaviour
  later $ \scope -> do
    -- put a special term to mark x as a function argument. those get special tratment
    -- because we're interested in their sensitivity
    let scope' = foldl (\sc -> (\(x :- τ) -> setValue x (checkSens (Arg x τ IsRelevant) scope) sc)) scope xτs

    τr <- checkSens body scope'
    let sign = (sndA <$> xτs)
    done $ do
      restype <- τr
      xrτs <- getArgList @_ @SensitivityK xτs
      let xrτs' = [x :@ s | (x :@ SensitivityAnnotation s) <- xrτs]
      let τ = (xrτs' :->: restype)
      -- frees <- getActuallyFreeVars τ
      let frees = []
      return (Fun [(ForAll frees τ :@ (Just sign))])


checkSen' (LamStar xτs body) scope =
  -- the body is checked in the toplevel scope, not the current variable scope.
  -- this reflects the julia behaviour
  later $ \scope -> do
    -- put a special term to mark x as a function argument. those get special tratment
    -- because we're interested in their privacy. put the relevance given in the function signature, too.
    let scope' = foldl (\sc -> (\(x :- (τ, rel)) -> setValue x (checkSens (Arg x τ rel) scope) sc)) scope xτs


    -- check the function body
    τr <- checkPriv body scope'
    -- extract julia signature
    let sign = (fst <$> sndA <$> xτs)
    done $ do
      restype <- τr
      -- get inferred types and privacies for the arguments
      xrτs <- getArgList @_ @PrivacyK [(x :- τ) | (x :- (τ, _)) <- xτs]

      -- variables that are annotated irrelevant can be made const in case they are
      -- numeric or tuples. that way we can express the result sensitivity/privacy
      -- in terms of the nonrelevant input variables
      let addC :: (DMMain :@ b, (a, Relevance)) -> TCT Identity ()
          addC ((τ :@ _), (_, i)) = do
                 _ <- case i of
                       IsRelevant -> pure ()
                       NotRelevant -> do
                                        addConstraint (Solvable (MakeConst τ))
                                        return ()
                 return ()

      mapM addC (zip xrτs (sndA <$> xτs))

      -- truncate function context to infinity sensitivity
      mtruncateS inftyS
      -- build the type signature and proper ->* type
      let xrτs' = [x :@ p | (x :@ PrivacyAnnotation p) <- xrτs]
      let τ = (xrτs' :->*: restype)
      -- include free variables in a ForAll
      -- frees <- getActuallyFreeVars τ
      let frees = []
      return (Fun [(ForAll frees τ :@ (Just sign))])


checkSen' (SLet (x :- dτ) term body) scope = do

   -- put the computation to check the term into the scope
   let scope' = setValue x (checkSens term scope) scope

   -- check body with that new scope
   result <- checkSens body scope'

   return $ do
     log $ "checking sensitivity SLet: " <> show (x :- dτ) <> " = " <> show term <> " in " <> show body
     -- TODO
     case dτ of
        JTAny -> return dτ
        dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

     result' <- result
     return result'


checkSen' (Apply f args) scope =
  let
    -- check the argument in the given scope,
    -- and scale scope by new variable, return both
    checkArg :: DMTerm -> DMScope -> DelayedT DMScope (State DelayedState) (TC (DMMain :@ Sensitivity))
    checkArg arg scope = do
      τ <- checkSens arg scope
      let scaleContext :: TC (DMMain :@ Sensitivity)
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
    --traceM $ "checking sens apply " <> show (f, args)
    -- we typecheck the function, but `apply` our current layer on the Later computation
    -- i.e. "typecheck" means here "extracting" the result of the later computation
    res <- (applyDelayedLayer scope mf)

    -- we apply the current scope to *ALL* (!) layers.
    -- i.e., all arguments are evaluated fully in the current scope
    -- this only makes sense because of the parsing rule
    -- restricting function to modify variables which are
    -- also modified on an outer level
    args <- applyAllDelayedLayers scope (sequence margs)

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
   done $ do
      choices <- msumS delCs
      let combined = foldl (:∧:) (Fun []) choices
      return combined


checkSen' (Phi cond ifbr elsebr) scope = do
   ifd <- checkSens ifbr scope
   elsed <- checkSens elsebr scope
   condd <- checkSens cond scope

   mcond <- done $ do
        τ_cond <- condd
        mscale inftyS
        return τ_cond

   done $ do
      τ_sum <- msumS [ifd, elsed, mcond]
      (τif, τelse) <- case τ_sum of
                           (τ1 : τ2 : _) -> return (τ1, τ2)
                           _ -> throwError (ImpossibleError "Sum cannot return empty.")

      -- the branches need to return types that are indistinguishable by julia dispatch,
      -- otherwise we cannot resolve dispatch because we don't know which branch is going
      -- to be chosen at runtime.
      addConstraint (Solvable (IsJuliaEqual (τif, τelse)))

      -- once we know they are julia-equal, we can safely make the Phi return their supremum.
      τ <- newVar
      addConstraint (Solvable (IsSupremum ((τif, τelse) :=: τ)))
      return τ



checkSen' (Tup ts) scope = do
  τsd <- mapM (\t -> (checkSens t scope)) ts
  done $ do

     -- check tuple entries and sum contexts
     τsum <- msumS τsd

     -- ensure nothing that is put in a tuple is a function
     let makeNoFun ty = do v <- newVar
                           unify (NoFun v) ty
                           return v
     τnf <- mapM makeNoFun τsum

     log $ "checking sens Tup: " <> show (Tup ts) <> ", type is " <> show (NoFun (DMTup τnf)) <> " when terms were " <> show τsum
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
  done $ do
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
    unify τterm (NoFun (DMTup xs_types'))

    -- finally we need make sure that our scaling factor `s` is the maximum of the tuple sensitivities
    s ==! maxS xs_sens

    log $ "checking sensitivities TLet: " <> show (xs) <> " = " <> show term <> " in " <> show body <> "\n ==> types are " <> show τbody <> " for term " <> show τterm
    -- and we return the type of the body
    return τbody


checkSen' (Loop niter cs' (xi, xc) body) scope = do
   cniter <- checkSens niter scope

   let scope_vars = getAllKeys scope

   -- build the tup of variables
   let cs = Tup ((\a -> Var (a :- JTAny)) <$> cs')
   -- check it
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

   done $ do

      --traceM $ "checking sens Loop: " <> show  (Loop niter cs (xi, xc) body)
      -- add scalars for iterator, capture and body context
      -- we compute their values once it is known if the number of iterations is const or not.
      sit <- newVar
      scs <- newVar
      sb <- newVar

      -- scale and sum contexts
      (τit, τcs, (τb, (τbit, sbit), (τbcs, sbcs))) <- msum3Tup (cniter <* mscale sit, ccs <* mscale scs, cbody' <* mscale sb)

      unify (NoFun (Numeric (NonConst DMInt))) τbit -- number of iterations must match type requested by body

      τcsnf <- newVar
      unify (NoFun τcsnf) τcs -- functions cannot be captured.

-- TODO make body non-const?
      τbnc <- newVar
      addConstraint (Solvable (IsNonConst (τb, τbnc)))
      -- addConstraint (Solvable (MakeNonConst (τbcs)))
      unify τbnc τbcs
      addConstraint (Solvable (IsLessEqual (τcs, τbcs)))
      addConstraint (Solvable (IsLoopResult ((sit, scs, sb), sbcs, τit))) -- compute the right scalars once we know if τ_iter is const or not.

      return τbnc


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

       done $ do
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
   done $ do
      τb <- mb

      -- variables for norm and clip parameters and dimension
      nrm <- newVar
      clp <- newVar
      n <- newVar

      -- set correct matrix type
      unify τb (NoFun (DMGrads nrm clp n (Numeric DMData)))

      -- change clip parameter to input
      return (NoFun (DMGrads nrm c n (Numeric DMData)))


--------------------
-- TODO
checkSen' (ConvertM m) scope = do
   mb <- checkSens m scope -- check the matrix
   done $ do
      τb <- mb

      -- variables for norm and clip parameters and dimension
      nrm <- newVar
      clp <- newVar -- this is a norm, because we do not accept
                    -- the unbounded clip value
      n <- newVar

      -- set correct matrix type
      unify τb (NoFun (DMGrads nrm (Clip clp) n (Numeric DMData)))

      -- move clip to the norm position,
      -- and forget about old `nrm`
      return (NoFun (DMGrads clp U n (Numeric (NonConst DMReal))))

--------------------


checkSen' (Transpose m) scope = do
   mb <- checkSens m scope -- check the matrix
   done $ do
      τb <- mb

      -- variables for norm and clip parameters and dimension
      τ <- newVar
      clp <- newVar
      n <- newVar
      m <- newVar

      -- set correct matrix type
      unify τb (NoFun (DMMat L1 clp n m (Numeric τ))) -- TODO actually mora than L1 would be possible if we had implicit fr-sens

      -- change clip parameter to input
      return (NoFun (DMMat L1 U m n (Numeric τ)))


checkSen' (Index m i j) scope = do

      -- check indicex and set their sensitivity to infinity
      di <- checkSens i scope
      dj <- checkSens j scope
      let dx = do
                   _ <- msumTup (di, dj)
                   mscale inftyS
                   return ()

      dm <- checkSens m scope -- check the matrix

      done $ do
         (τm, _) <- msumTup (dm, dx)

         -- variables for element type, norm and clip parameters and dimension
         τ <- newVar
         nrm <- newVar
         clp <- newVar
         n <- newVar
         m <- newVar

         -- set matrix type
         unify τm (NoFun (DMMat nrm clp n m (Numeric τ)))

         -- TODO maybe restrict index size?

         return (NoFun (Numeric τ))


checkSen' (SubGrad ps gs) scope = do
      -- check indicex and set their sensitivity to infinity
      dps <- checkSens ps scope
      dgs <- checkSens gs scope

      done $ do
         s1 <- newSVar "s1"
         s2 <- newSVar "s2"

         (ps, gs) <- msumTup ((dps <* mscale (svar s1)), (dgs <* mscale (svar s2)))

         -- variables for element types, norm and clip parameters and dimension
         τps <- newVar
         τgs <- newVar
         nrm <- newVar
         clp <- newVar
         m <- newVar

         -- set argument types
         unify ps (NoFun (DMParams m (Numeric τps)))
         unify gs (NoFun (DMGrads nrm clp m (Numeric τgs)))

         res <- TVar <$> newTVar "τr"
         addConstraint (Solvable (IsTypeOpResult (Binary DMOpSub ((Numeric τps):@s1, (Numeric τgs):@s2) res)))

         return (NoFun (DMParams m res))


-- Everything else is currently not supported.
checkSen' t scope = (throwDelayedError (UnsupportedTermError t))


--------------------------------------------------------------------------------
-- Privacy terms

checkPri' :: DMTerm -> DMScope -> DMDelayed

checkPri' (Ret t) scope = do
   mτ <- checkSens t scope
   done $ do
      τ <- mτ
      mtruncateP inftyP
      log $ "checking privacy " <> show (Ret t) <> ", type is " <> show τ
      return τ


checkPri' (Rnd t) scope = do
   done $ do
      τ <- (createDMTypeNum t)
      return (NoFun (Numeric (NonConst τ)))

-- TODO it is ambiguous if this is an application of a LamStar or an application of a Lam followed by Return.
-- we probably should resolve IsFunctionArgument ( T -> T, S ->* S) by setting S's privacies to infinity.
checkPri' (Apply f args) scope =
  let
    -- check the argument in the given scope,
    -- and scale scope by new variable, return both
    checkArg :: DMTerm -> DMScope -> DelayedT DMScope (State DelayedState) (TC (DMMain :@ Privacy))
    checkArg arg scope = do
      τ <- checkSens arg scope
      let restrictTruncateContext :: TC (DMMain :@ Privacy)
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

    f_check :: DelayedT DMScope (State DelayedState) (TC DMMain) = do
       -- we typecheck the function, but `apply` our current layer on the Later computation
       -- i.e. "typecheck" means here "extracting" the result of the later computation
       res <- (applyDelayedLayer scope (checkSens f scope))
       done $ do
                r <- res
                mtruncateP inftyP -- truncate f's context to ∞
                return r

  in do
    --traceM $ "checking priv apply " <> show (f, args)
    -- extract result of f typechecking
    ff <- f_check

    -- we extract the result of the args computations
    args <- applyAllDelayedLayers scope (sequence margs)

    -- we merge the different TC's into a single result TC
    return (sbranch_check ff args)




checkPri' (SLet (x :- dτ) term body) scope = do
   -- this is the bind rule.
   -- as it does not matter what sensitivity/privacy x has in the body, we put an Arg term in the scope
   -- and later discard its annotation. we use checkSens because there are no Vars in privacy terms so
   -- x will only ever be used in a sensitivity term.
   let scope' = setValue x (checkSens (Arg x dτ NotRelevant) scope) scope

   -- check body with that new scope
   dbody <- checkPriv body scope'
   mbody <- done $ do
                   τ <- dbody
                   -- discard x from the context, never mind it's inferred annotation
                   WithRelev _ (τx :@ _) <- removeVar @PrivacyK x
                   return (τ, τx)

   -- check term with old scope
   dterm <- checkPriv term scope

   return $ do
     -- TODO
     case dτ of
        JTAny -> return dτ
        dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

     -- sum contexts
     ((τbody, τx), τterm) <- msumTup (mbody, dterm)

     -- unify type of x in the body with inferred type of the assignee term
     unify τx τterm

     -- make sure that τterm is not a functiontype
     -- this is necessary because elsewise it might be capturing variables
     -- which we do not track here. (We can only track that if we put the
     -- computation for checking the term itself into the scope, instead
     -- of an arg representing it. But this would not work with the bind rule.)
     -- See https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/18
     τnofun <- newVar
     unify τbody (NoFun τnofun)

     log $ "checking privacy SLet: " <> show (x :- dτ) <> " = " <> show term <> " in " <> show body<> "\n ==> inferred type is " <> show τx <> ", term type is " <> show τterm <> ", body types is " <> show τbody
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

-- there are no privacy tuples. instead we transform the term:
-- (t1, t2)
-- becomes
--
-- slet x1 = t1
-- slet x2 = t2
-- in return (x1, x2)
--
-- this way if t1 and t2 are privacy terms, they can be checked in privcacy mode
-- but the tuple is still a sensitivity term.
-- TODO the names must be unique.
checkPri' (Tup ts) scope = do
   names <- mapM newTeVar [(T.pack ("x" <> (show i))) | i <- [1..(length ts)]]
   let body = Ret (Tup [Var (n :- JTAny) | n <- names])
   let t1 = foldl (\b -> \(x, t) -> SLet (x :- JTAny) t b) body (zip names ts)
      --traceM $ "privacy Tup checking term " <> show t1
   checkPriv t1 scope

-- there are no privacy tlets either. so here's what we do:
-- tlet (x1, x2) = t
-- in ...
-- becomes
--
-- tup = t
-- slet x1 = return { tlet (x1,_) = tup
--                    in x1 }
-- slet x2 = return { tlet (_,x2) = tup
--                   in x2 }
-- in ...
--
-- this way we can do the projections in sensitivity mode while the body can still be a privacy term.
-- TODO tup needs to be a unique name instead.
checkPri' (TLet xs term body) scope = do
   tupvar <- newTeVar "tup"
   let t1 = foldl (\t -> \(x :- τj) -> SLet (x :- τj) (Ret (TLet xs (Var (tupvar :- JTAny)) (Var (x :- τj)))) t) body xs
       t2 = SLet (tupvar :- (JTAny)) term t1
   checkPriv t2 scope

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

      done $ do
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


checkPri' (Loop niter cs' (xi, xc) body) scope =
   --let setInteresting :: ([Symbol],[DMMain :@ PrivacyAnnotation]) -> Sensitivity -> TC ()
   let setInteresting (xs, τps) n = do
          let τs = map fstAnn τps
          let ps = map sndAnn τps

          let ε = maxS (map (\(PrivacyAnnotation (εs, _)) -> εs) ps)
          let δ = maxS (map (\(PrivacyAnnotation (_, δs)) -> δs) ps)

          δn :: Sensitivity <- newVar -- we can choose this freely!
          addConstraint (Solvable (IsLessEqual (δn, oneId :: Sensitivity))) -- otherwise we get a negative ε...

          -- compute the new privacy for the xs according to the advanced composition theorem
          let two = oneId ⋆! oneId
          let newp = (two ⋅! (ε ⋅! (sqrt (two ⋅! (n ⋅! (minus (ln oneId) (ln δn)))))), δn ⋆! (n ⋅! δ)) -- TODO

          mapM (\(x, τ) -> setVarP x (WithRelev IsRelevant (τ :@ PrivacyAnnotation newp))) (zip xs τs)
          return ()

   in do
      --traceM $ "checking privacy Loop: " <> show  (Loop niter cs (xi, xc) body)
      cniter <- checkSens niter scope

      let cniter' = do
                   τ <- cniter
                   mtruncateP zeroId
                   return τ

      -- build the up of variables
      let cs = Tup ((\a -> Var (a :- JTAny)) <$> cs')

      -- check it
      mcaps <- checkSens cs  scope
      let mcaps' = do
                   τ <- mcaps
                   mtruncateP inftyP
                   return τ


      -- add iteration and capture variables as args-checking-commands to the scope
      -- capture variable is not relevant bc captures get ∞ privacy anyways
      -- TODO: do we need to make sure that we have unique names here?
      let scope' = setValue xi (checkSens (Arg xi JTNumInt NotRelevant) scope) scope
      let scope'' = setValue xc (checkSens (Arg xc JTAny NotRelevant) scope) scope'

      -- check body term in that new scope
      cbody <- checkPriv body scope''

      -- append the computation of removing the args from the context again, remembering their types
      -- and sensitivities
      let cbody' = do
            τ <- cbody
            WithRelev _ (τi :@ _) <- removeVar @PrivacyK xi
            WithRelev _ (τc :@ _) <- removeVar @PrivacyK xc -- unify with caps type?

            interesting <- getInteresting
            mtruncateP inftyP

            n <- newVar
            setInteresting interesting n
            return (τ, n, τi, τc)

      done $ do
         -- scale and sum contexts
         (τit, τcs, (τb, n, τbit, τbcs)) <- msum3Tup (cniter', mcaps', cbody')

         unify τit (NoFun (Numeric (Const n DMInt))) -- number of iterations must be constant integer
         unify (NoFun (Numeric (NonConst DMInt))) τbit -- number of iterations must match type requested by body

         τcsnf <- newVar
         unify (NoFun τcsnf) τcs -- functions cannot be captured.

   -- TODO make body non-const?
         τbnc <- newVar
         addConstraint (Solvable (IsNonConst (τb, τbnc)))
         -- addConstraint (Solvable (MakeNonConst (τbcs)))
         unify τbnc τbcs
         addConstraint (Solvable (IsLessEqual (τcs, τbcs)))

         return τbnc

checkPri' t scope = checkPriv (Ret t) scope -- secretly return if the term has the wrong color.
