
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Typecheck.Operations
import DiffMu.Core.Scope
import DiffMu.Abstract.Data.Permutation
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
checkPriv :: DMScope -> DMTerm -> TC DMMain
checkPriv scope t = do

  -- The computation to do before checking
  γ <- use types
  case γ of -- TODO prettify.
      Left (Ctx (MonCom c)) | H.null c -> return ()
      Right (Ctx (MonCom c)) | H.null c -> return ()
      ctx   -> impossible $ "Input context for checking must be empty. But I got:\n" <> show ctx
  types .= Right def -- cast to privacy context.

  -- The checking itself
  res <- withLogLocation "Check" $ checkPri' scope t

  -- The computation to do after checking
  γ <- use types
  case γ of
      Right γ -> return res
      Left γ -> error $ "checkPriv returned a sensitivity context!\n" <> "It is:\n" <> show γ <> "\nThe input term was:\n" <> show t




checkSens :: DMScope -> DMTerm -> TC DMMain
checkSens scope t = do
  -- The computation to do before checking
  γ <- use types
  case γ of -- TODO prettify.
      Left (Ctx (MonCom c)) | H.null c -> return ()
      Right (Ctx (MonCom c)) | H.null c -> return ()
      ctx   -> impossible $ "Input context for checking must be empty. But I got:\n" <> show ctx <> "\nThe term is:\n" <> show t
  types .= Left def -- cast to sensitivity context.


  -- get the delayed value of the sensititivty checking
  res <- withLogLocation "Check" $ checkSen' scope t

  -- The computation to do after checking
  γ <- use types
  case γ of
      Left γ -> return res
      Right γ -> error $ "checkSens returned a privacy context!\n" <> "It is:\n" <> show γ <> "\nThe input term was:\n" <> show t


--------------------
-- Sensitivity terms


checkSen' :: DMScope -> DMTerm -> TC DMMain

checkSen' scope DMTrue = return (NoFun DMBool)
checkSen' scope DMFalse = return (NoFun DMBool)

-- TODO: Here we assume that η really has type τ, and do not check it. Should maybe do that.
checkSen' scope (Sng η τ) = do
  res <- Numeric <$> (Num <$> (createDMTypeBaseNum τ) <*> pure (Const (constCoeff (Fin η))))
  return (NoFun res)

-- typechecking an op
checkSen' scope (Op op args) = do
  -- create a new typeop constraint for op
  -- res is resulting type of the operation when used on types in arg_sens
  -- arg_sens :: [(SMType, Sensitivity)]
  -- types are to be unified with the actual types of the args
  -- Sensitivities are scalars for the argument's context
  (res, arg_sens) <- makeTypeOp op (length args)

  -- typecheck, make the appropriate unification and scaling, then sum the contexts.
  let handleOpArg (t_arg, (τ, s)) = do
                                  τ_arg <- checkSens scope t_arg
                                  unify (NoFun τ) τ_arg
                                  mscale (svar s)
                                  return τ_arg
                                  
  msumS (map handleOpArg (zip args arg_sens))
  
  -- return the `res` type given by `makeTypeOp`
  return (NoFun res)


-- a special term for function argument variables.
-- those get sensitivity 1, all other variables are var terms
checkSen' scope (Arg x jτ i) = do
  τs <- newVar
  logForce $ "checking arg:" <> show (x :- jτ) <> ", dmtype is " <> show τs
  -- the inferred type must be a subtype of the user annotation, if given.
  addJuliaSubtypeConstraint τs jτ

  -- put the variable in the Γ context with sensitivity 1
  setVarS x (WithRelev i (τs :@ SensitivityAnnotation oneId))
  return τs




checkSen' scope (Var (x :- dτ)) =  -- get the term that corresponds to this variable from the scope dict
   let mτ = getValue x scope
   in case mτ of
     Nothing -> logForce ("[Var-Sens] Scope is:\n" <> show (getAllKeys scope)) >> throwError (VariableNotInScope x)
     Just jτ -> do
                     logForce ("[Var-Sens] Scope is:\n" <> show (getAllKeys scope))
                     τ <- jτ -- extract the type of x
                     -- if the user has given an annotation
                     -- inferred type must be a subtype of the user annotation
                     addJuliaSubtypeConstraint τ dτ
                     return τ

checkSen' scope (Lam xτs body) = do

    -- put a special term to mark x as a function argument. those get special treatment
    -- because we're interested in their privacy. put the relevance given in the function signature, too.
    let f s sc (x :- τ) = setValue x (checkSens s (Arg x τ IsRelevant)) sc
    let addArgs s = foldl (f s) s xτs
    let scope' = addArgs scope

    -- check the body in the modified scope
    btype <- checkSens scope' body

    -- extract julia signature
    let sign = (sndA <$> xτs)
        
    -- get inferred types and sensitivities for the arguments
    xrτs <- getArgList @_ @SensitivityK xτs
    let xrτs' = [x :@ s | (x :@ SensitivityAnnotation s) <- xrτs]
    logForce $ "Checking Lam, outer scope: " <> show (getAllKeys scope) <> " | inner: " <> show (getAllKeys scope')

    -- add constraints for making non-const if not resolvable
    let addC :: (DMMain :@ b, a) -> TCT Identity ()
        addC ((τ :@ _), _) = addConstraint (Solvable (MakeNonConst (τ, SolveAssumeWorst))) >> pure ()
    mapM addC (zip xrτs (sndA <$> xτs))

    -- make an arrow type.
    let τ = (xrτs' :->: btype)
    return (Fun [τ :@ (Just sign)])


checkSen' scope (LamStar xτs body) = do
    -- put a special term to mark x as a function argument. those get special treatment
    -- because we're interested in their sensitivity
    let f s sc (x :- (τ , rel)) = setValue x (checkSens s (Arg x τ rel)) sc
    let addArgs s = foldl (f s) s xτs
    let scope' = addArgs scope

    -- check the body in the modified scope
    btype <- checkPriv scope' body

    -- extract julia signature
    let sign = (fst <$> sndA <$> xτs)
        
    -- get inferred types and privacies for the arguments
    xrτs <- getArgList @_ @PrivacyK [(x :- τ) | (x :- (τ, _)) <- xτs]

    -- variables that are annotated irrelevant can be made const in case they are
    -- numeric or tuples. that way we can express the result sensitivity/privacy
    -- in terms of the nonrelevant input variables
    let addC :: (DMMain :@ b, (a, Relevance)) -> TCT Identity ()
        addC ((τ :@ _), (_, i)) = do
               _ <- case i of
                     IsRelevant -> addConstraint (Solvable (MakeNonConst (τ, SolveAssumeWorst))) >> pure ()
                     NotRelevant -> do
                                      addConstraint (Solvable (MakeConst τ))
                                      return ()
               return ()
    mapM addC (zip xrτs (sndA <$> xτs))

    -- truncate function context to infinity sensitivity
    mtruncateS inftyS
    
    -- build the type signature and proper ->* type
    let xrτs' = [x :@ p | (x :@ PrivacyAnnotation p) <- xrτs]

    -- functions can only return deepcopies of DMModel and DMGrads
    -- restype <- newVar
    -- addConstraint (Solvable (IsClone (btype, restype)))

    let τ = (xrτs' :->*: btype)
    return (Fun [τ :@ (Just sign)])


checkSen' scope (SLet (x :- dτ) term body) = do

   -- put the computation to check the term into the scope
   --  let scope' = setValue x (checkSens term scope) scope
   let scope' = setValue x (checkSens scope term) scope

   -- check body with that new scope
   result <- checkSens scope' body

   logForce $ "checking sensitivity SLet: " <> show (x :- dτ) <> " = " <> show term <> " in " <> show body
   -- TODO
   case dτ of
      JTAny -> return dτ
      dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

   return result


checkSen' scope (BBLet name jτs tail) = do

   -- the type of this is just a BlackBox, put it in the scope
   let scope' = setValue name (return (BlackBox jτs)) scope

   -- check tail with that new scope
   result <- checkSens scope' tail
   removeVar @SensitivityK name
   return result




checkSen' scope (BBApply app args cs k) =
  let
    checkArg arg = do
      let τ = checkSens scope arg
      τ' <- τ
      s <- newVar
      mscale s -- all args get infinite sensitivity
      return (τ', s)

    checkCap :: TeVar -> TC ()
    checkCap c =
       let delτ = getValue c scope -- see if the capture is in the current scope
       in case delτ of
         Nothing -> return () -- if no, we don't need to do anything as it was not defined yet during this application
         Just delτ -> do      -- if yes, we need to make sure it gets infinite sensitivity in the result context.
                               τ <- newVar -- we achieve this by putting it into the context with some type var and inf annotation
                               setVarS c (WithRelev NotRelevant (τ :@ SensitivityAnnotation inftyS))
                               return ()

    margs = checkArg <$> args
    mf = checkSens scope app

  in do
    -- we merge the different TC's into a single result TC
    let caps = checkCap <$> cs
    (τ_box :: DMMain, argτs, _, τ_ret) <- msum4Tup (mf , msumS margs, msumS caps, checkBBKind scope k) -- sum args and f's context
    -- the return type is constructed from the bbkind
    -- τ_ret <- checkBBKind scope k
    logForce $ "blackbox return tyoe is " <> show τ_ret

    addConstraint (Solvable (IsBlackBox (τ_box, fst <$> argτs))) -- constraint makes sure the signature matches the args
    mapM (\s -> addConstraint (Solvable (IsBlackBoxReturn (τ_ret, s)))) argτs -- constraint sets the sensitivity to the right thing
    return τ_ret
    

checkSen' scope (Apply f args) =
  let
    -- check the argument in the given scope,
    -- and scale scope by new variable, return both
    checkArg :: DMScope -> DMTerm -> (TC (DMMain :@ Sensitivity))
    checkArg scope arg = do
      τ' <- checkSens scope arg
      s <- newVar
      mscale s
      return (τ' :@ s)

    margs = checkArg scope <$> args
    mf = checkSens scope f

  in do
    logForce ("[Apply-Sens]Scope is:\n" <> show (getAllKeys scope))
    (τ_sum :: DMMain, argτs) <- msumTup (mf , msumS margs) -- sum args and f's context
    τ_ret <- newVar -- a type var for the function return type
    addConstraint (Solvable (IsFunctionArgument (τ_sum, Fun [(argτs :->: τ_ret) :@ Nothing])))
    return τ_ret


checkSen' scope (MMap f m) = do
    s <- newVar
    mv <- newVar
    mr <- newVar
    let mm = checkSens scope m <* mscale s
    let mf = checkSens scope f <* mscale mv <* mscale mr
    (τf :: DMMain, τm) <- msumTup (mf, mm) -- sum args and f's context

    τ_in <- newVar -- a type var for the function input / matrix element type
    τ_out <- newVar -- a type var for the function output type
    nrm <- newVar -- variable for norm
    clp <- newVar -- variable for clip
    k <- newVar -- variable for container kind
    unify τm (NoFun (DMContainer k nrm clp mv τ_in))

    -- only matrices or vectors (not gradients) are allowed.
    addConstraint (Solvable (IsVecOrMat (k, mr)))

    -- dispatch is not allowed for map, hence unification with a one-choice ->
    unify τf (Fun [([τ_in :@ s] :->: τ_out) :@ Just [JTAny]])

    return (NoFun (DMContainer k nrm U mv τ_out))


checkSen' scope (FLet fname term body) = do

  -- make a Choice term to put in the scope
  let scope' = pushChoice fname (checkSens scope term) scope

  -- check body with that new scope. Choice terms will result in IsChoice constraints upon ivocation of fname

  logForce ("[FLet-Sens] for '" <> show fname <> "', scope is: " <> show (getAllKeys scope))
  result' <- checkSens scope' body
  removeVar @SensitivityK fname
  return result'



checkSen' scope (Choice d) = do
  let delCs = checkSens scope <$> (snd <$> H.toList d)
  choices <- msumS delCs
  let combined = foldl (:∧:) (Fun []) choices
  return combined



checkSen' scope (Phi cond ifbr elsebr) = do
  let ifd   = checkSens scope ifbr
  let elsed = checkSens scope elsebr
  let condd = checkSens scope cond <* mscale inftyS

  τ_sum <- msumS [ifd, elsed, condd]
  (τif, τelse, τcond) <- case τ_sum of
                       [τ1 , τ2 , τ3]  -> return (τ1, τ2, τ3)
                       _ -> throwError (ImpossibleError "Sum cannot return empty.")

  -- the branches need to return types that are indistinguishable by julia dispatch,
  -- otherwise we cannot resolve dispatch because we don't know which branch is going
  -- to be chosen at runtime.
  addConstraint (Solvable (IsJuliaEqual (τif, τelse)))

  unify τcond (NoFun DMBool)

  -- once we know they are julia-equal, we can safely make the Phi return their supremum.
  τ <- newVar
  addConstraint (Solvable (IsSupremum ((τif, τelse) :=: τ)))
  return τ



checkSen' scope (Tup ts) = do

  -- check tuple entries and sum contexts
  τsum <- msumS (checkSens scope <$> ts)

  -- ensure nothing that is put in a tuple is a function
  let makeNoFun ty = do v <- newVar
                        unify (NoFun v) ty
                        return v
  τnf <- mapM makeNoFun τsum

  log $ "checking sens Tup: " <> show (Tup ts) <> ", type is " <> show (NoFun (DMTup τnf)) <> " when terms were " <> show τsum
  -- return the tuple.
  return (NoFun (DMTup τnf))



checkSen' original_scope (TLet xs term body) = do

  -- add all variables bound in the tuple let as args-checking-commands to the scope
  -- TODO: do we need to make sure that we have unique names here?
  let addarg scope (x :- τ) = setValue x (checkSens original_scope (Arg x τ NotRelevant)) scope
  let scope_with_args = foldl addarg original_scope xs

  -- check the body in the scope with the new args
  let cbody = checkSens scope_with_args body

  -- append the computation of removing the args from the context again, remembering their types
  -- and sensitivities
  let cbody' = do
        τ <- cbody
        xs_types_sens <- mapM (removeVar @SensitivityK) [x | (x :- _) <- xs]
        let xs_types_sens' = [ (ty,sens) | WithRelev _ (ty :@ SensitivityAnnotation sens) <- xs_types_sens ]
        return (τ,xs_types_sens')

  -- the computation for checking the term
  let cterm = checkSens original_scope term

  -- merging the computations and matching inferred types and sensitivities
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

checkSen' scope (Loop niter cs' (xi, xc) body) = do
  let cniter = checkSens scope niter

  let scope_vars = getAllKeys scope

  -- build the tup of variables
  let cs = Tup ((\a -> Var (a :- JTAny)) <$> cs')

  -- check it
  let ccs = checkSens scope cs

  -- add iteration and capture variables as args-checking-commands to the scope
  -- TODO: do we need to make sure that we have unique names here?
  let scope' = setValue xi (checkSens scope (Arg xi JTInt NotRelevant)) scope
  let scope'' = setValue xc (checkSens scope (Arg xc JTAny IsRelevant)) scope'

  -- check body term in that new scope
  let cbody = checkSens scope'' body

  -- append the computation of removing the args from the context again, remembering their types
  -- and sensitivities
  let cbody' = do
        τ <- cbody
        WithRelev _ (τi :@ si) <- removeVar @SensitivityK xi
        WithRelev _ (τc :@ sc) <- removeVar @SensitivityK xc
        return (τ, (τi, si), (τc, sc))


  --traceM $ "checking sens Loop: " <> show  (Loop niter cs (xi, xc) body)
  -- add scalars for iterator, capture and body context
  -- we compute their values once it is known if the number of iterations is const or not.
  sit <- newVar
  scs <- newVar
  sb <- newVar

  -- scale and sum contexts
  -- τit = type of the iterator (i.e. the term describung the number of iterations)
  -- τcs = type of the capture input tuple
  -- τb = inferred type of the body
  -- τbit = type of the iterator variable xi inferred in the body
  -- τbcs = type of the capture variable xc inferred in the body
  (τit, τloop_in, (τbody_out, (τbit, sbit), (τbody_in, sbcs))) <- msum3Tup (cniter <* mscale sit, ccs <* mscale scs, cbody' <* mscale sb)

  unify (NoFun (Numeric (Num DMInt NonConst))) τbit -- number of iterations must match type requested by body

  τcsnf <- newVar
  unify (NoFun τcsnf) τloop_in -- functions cannot be captured.

  addConstraint (Solvable (IsLoopResult ((sit, scs, sb), sbcs, τit))) -- compute the right scalars once we know if τ_iter is const or not.

{-
      -- TODO loops with Const captures/output don't work yet.
      -- the inferred capture type should be the same as the non-const version of the inferred body type
      -- so we can loop properly by plugging the loop result into the loop in again
      -- the inferred type for xc must be non-const, as we cannot assume that it will be the same in each
      -- iteration.
      addConstraint (Solvable (IsNonConst (τb, τbcs)))

      -- also the given capture that we start iteration with should fit into the expected capture
      addConstraint (Solvable (IsNonConst (τcs, τbcs)))
-}

      -- the types of body, input captures and captures as used in the body must all be equal
      -- (except Const-ness, actually. we'll figure that out at some point)
  -- unify τb τbcs
  -- unify τcs τbcs

  addConstraint (Solvable (IsNonConst (τbody_out, τbody_in)))
  addConstraint (Solvable (UnifyWithConstSubtype (τloop_in, τbody_out)))
  addConstraint (Solvable (IsLoopResult ((sit, scs, sb), sbcs, τit))) -- compute the right scalars once we know if τ_iter is const or not.

  return τbody_in


checkSen' scope (MCreate n m (x1, x2) body) =
   let setDim :: TC DMMain -> Sensitivity -> TC DMMain
       setDim tm s = do
          τ <- tm -- check dimension term
          unify τ (NoFun (Numeric (Num DMInt (Const s)))) -- dimension must be const integral
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
          addConstraint (Solvable (IsLessEqual (x1τ, NoFun (Numeric (Num DMInt NonConst)))))
          addConstraint (Solvable (IsLessEqual (x2τ, NoFun (Numeric (Num DMInt NonConst)))))

          return τ
   in do

      let mn    = checkSens scope n
      let mm    = checkSens scope m
      let mbody = checkSens scope body

      -- variables for matrix dimension
      nv <- newVar
      mv <- newVar

      (τbody, _, _) <- msum3Tup (checkBody mbody nv mv, setDim mn nv, setDim mm mv)

      nrm <- newVar -- variable for norm
      return (NoFun (DMMat nrm U nv mv τbody))

checkSen' scope (Size m) = do
  mt <- checkSens scope m
  
  -- variables for matrix dimension
  nv <- newVar
  mv <- newVar

  -- and matrix entries
  τ <- newVar

  nrm <- newVar -- variable for norm
  clp <- newVar -- variable for clip
  unify mt (NoFun (DMMat nrm clp nv mv τ))

  mscale zeroId

  return (NoFun (DMTup [Numeric (Num DMInt (Const nv)), Numeric (Num DMInt (Const mv))]))

checkSen' scope (Length m) = do
  mt <- checkSens scope m
  
  -- variables for vector dimension and entries
  nv <- newVar
  τ <- newVar

  nrm <- newVar -- variable for norm
  clp <- newVar -- variable for clip
  unify mt (NoFun (DMVec nrm clp nv τ))

  mscale zeroId

  return (NoFun (Numeric (Num DMInt (Const nv))))


checkSen' scope (MutClipM c m) = checkSens scope (ClipM c m)
checkSen' scope (ClipM c m) = do
  τb <- checkSens scope m -- check the matrix

  -- variables for norm and clip parameters and dimension
  clp <- newVar
  n <- newVar

  -- variable for vector kind
  k <- newVar

  -- only 1-d things are allowed here (vec, grad or 1-d matrix)
  addConstraint (Solvable (IsVecLike k))

  -- set correct matrix type
  unify τb (NoFun (DMContainer k LInf clp n (NoFun (Numeric DMData))))

  -- change clip parameter to input
  return (NoFun (DMContainer k LInf c n (NoFun (Numeric DMData))))
checkSen' scope (ClipN value upper lower) = do
  τv <- checkSens scope value
  τu <- checkSens scope upper
  τl <- checkSens scope lower

  tv <- newVar
  tu <- newVar
  tl <- newVar
  tr <- newVar

  addConstraint (Solvable (IsLessEqual (τv, (NoFun (Numeric (Num tv NonConst))))))
  unify τu (NoFun (Numeric (Num tv (Const tu))))
  unify τl (NoFun (Numeric (Num tv (Const tl))))

  addConstraint (Solvable (IsLessEqual (tr, tu)))
  addConstraint (Solvable (IsLessEqual (tl, tr)))

  mscale (minus tu tl)

  return (NoFun (Numeric (Num tv (Const tr))))


checkSen' scope (Count f m) = let
    mf = checkSens scope f <* mscale inftyS -- inf-sensitive in the function
    mm = checkSens scope m -- 1-sensitive in the matrix
  in do
    (tf, tm) <- msumTup (mf, mm)

    
    cl <- newVar
    r <- newVar
    s <- newVar
        
    unify tm (NoFun (DMVec L1 cl r (NoFun (Numeric DMData))))
    unify tf (Fun [[(NoFun (Numeric DMData)) :@ s] :->: (NoFun DMBool) :@ (Just [JTAny])])
    
    return (NoFun (Numeric (Num DMInt NonConst)))

  
  

--------------------
-- NOTE this is different from what is in the paper, as we scale the result context by 2 not by 1
-- a proof that this is correct is in the matrixnorm pdf, and the authors told me it's correct too
checkSen' scope (ConvertM m) = do
  τb <- checkSens scope m -- check the matrix

  -- variables for norm and clip parameters and dimension
  nrm <- newVar
  clp <- newVar -- this is a norm, because we do not accept
                -- the unbounded clip value
  n <- newVar
  
  -- variable for vector kind (i.e. vector or grads)
  k <- newVar

  -- set correct matrix type
  unify τb (NoFun (DMContainer k nrm (Clip clp) n (NoFun (Numeric DMData))))

  -- we have to scale by two unlike in the paper...see the matrixnorms pdf in julia docs
  mscale (oneId ⋆! oneId)

  -- move clip to the norm position,
  -- and forget about old `nrm
  -- technically the clipping parameter does not change, but we set it to U so it fits with the rest...
  -- see issue 
--  return (NoFun (DMGrads clp (Clip clp) n (Numeric (Num DMReal NonConst))))
  return (NoFun (DMContainer k clp U n (NoFun (Numeric (Num DMReal NonConst)))))

--------------------

{- TODO check issue #78
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
-}
checkSen' scope  (Index m i j) = do

      -- check indices and set their sensitivity to infinity
      let di = checkSens scope i
      let dj = checkSens scope j
      let dx = do
                   _ <- msumTup (di, dj)
                   mscale inftyS
                   return ()

      let dm = checkSens scope m -- check the matrix

      (τm, _) <- msumTup (dm, dx)

      -- variables for element type, norm and clip parameters and dimension
      τ <- newVar
      nrm <- newVar
      clp <- newVar
      n <- newVar
      m <- newVar

      -- set matrix type
      unify τm (NoFun (DMMat nrm clp n m τ))

      -- we don't restrict matrix dimension or index size, but leave that to the runtime errors...

      return τ


checkSen' scope (VIndex v i)  = do

      -- check index and set the sensitivity to infinity
      let di = checkSens scope i
      let dx = do
                   _ <- di
                   mscale inftyS
                   return ()

      let dv = checkSens scope v -- check the vector

      (τv, _) <- msumTup (dv, dx)

      -- variables for element type, norm and clip parameters and dimension
      τ <- newVar
      nrm <- newVar
      clp <- newVar
      n <- newVar

      -- set vector type
      unify τv (NoFun (DMVec nrm clp n τ))

      -- we don't restrict vector dimension or index size, but leave that to the runtime errors...

      return τ

checkSen' scope (Row m i) = do
          -- check index and set their sensitivity to infinity
      let di = checkSens scope i
      let dx = do
                   _ <- di
                   mscale zeroId
                   return ()

      let dm = checkSens scope m -- check the matrix

      (τm, _) <- msumTup (dm, dx)

      -- variables for element type, norm and clip parameters and dimension
      τ <- newVar
      nrm <- newVar
      clp <- newVar
      n <- newVar
      m <- newVar

      -- set matrix type
      unify τm (NoFun (DMMat nrm clp n m τ))

      -- we don't restrict matrix dimension or index size, but leave that to the runtime errors...

      return (NoFun (DMVec nrm clp m τ)) -- returns Vector type to accomodate julia behaviour

checkSen' scope (SubGrad ps gs) = do
      -- check model and gradient
      let dps = checkSens scope ps
      let dgs = checkSens scope gs

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
      unify ps (NoFun (DMModel m τps))
      unify gs (NoFun (DMGrads nrm clp m (NoFun (Numeric τgs))))

      res <- TVar <$> newTVar "τr"
      addConstraint (Solvable (IsTypeOpResult (Binary DMOpSub ((Numeric τps):@s1, (Numeric τgs):@s2) (Numeric res))))

      return (NoFun (DMModel m res))

checkSen' scope term@(ScaleGrad scalar grad) = do

  let makeNumeric t = do
          tn <- newVar
          unify t (Numeric tn)

  let dscalar = checkSens scope scalar
  let dgrad = checkSens scope grad

  -- Create sensitivity / type variables for the multiplication
  (τres , types_sens) <- makeTypeOp (IsBinary DMOpMul) 2

  ((τ1,s1),(τ2,s2)) <- case types_sens of
    [(τ1,s1),(τ2,s2)] -> pure ((τ1,s1),(τ2,s2))
    _ -> impossible $ "Wrong array return size of makeTypeOp in " <> showPretty term

  -- Create variables for the matrix type
  -- (norm and clip parameters and dimension)
  nrm <- newVar
  clp <- newVar
  m <- newVar

  -- infer the types of the scalar and the gradient
  -- we get
  -- `Γ₁ ⋅ s₁ + Γ₂ ⋅ s₂`
  --   where (s₁,s₂) ⩯ tscalar ⋅ tgrad
  (tscalar, tgrad) <- msumTup ((dscalar <* mscale (svar s1)), (dgrad <* mscale (svar s2)))

  -- set τ1 to the actual type of the scalar
  makeNumeric τ1
  unify tscalar (NoFun τ1)

  -- and τ2 to the actual content type of the dmgrads
  -- (we allow any kind of annotation on the dmgrads here)
  makeNumeric τ2
  unify tgrad (NoFun (DMGrads nrm clp m (NoFun τ2)))

  -- the return type is the same matrix, but
  -- the clipping is now changed to unbounded
  -- and the content type is the result of the multiplication
  τresnum <- newVar
  unify (Numeric τresnum) τres
  return (NoFun (DMGrads nrm U m (NoFun τres)))

checkSen' scope (Reorder σ t) = do
  τ <- checkSens scope t
  ρ <- newVar
  addConstraint (Solvable (IsReorderedTuple ((σ , τ) :=: ρ)))
  return ρ

checkSen' scope (TProject i t) = do
  τ <- checkSens scope t
  ρ <- newVar
  addConstraint (Solvable (IsTProject ((i , τ) :=: ρ)))
  return ρ

checkSen' scope (ZeroGrad m) = do
   -- check model
   tm <- checkSens scope m

   -- variables for element type, dimension, result norm and clip parameters
   τps <- newVar
   n <- newVar
   nrm <- newVar
   clp <- newVar -- actually variable, as all entries are zero

   -- input must be a model
   unify tm (NoFun (DMModel n τps))

   return (NoFun (DMGrads nrm clp n (NoFun (Numeric τps))))


checkSen' scope term@(SumGrads g1 g2) = do

  -- Create sensitivity / type variables for the addition
  (τres , types_sens) <- makeTypeOp (IsBinary DMOpAdd) 2

  ((τ1,s1),(τ2,s2)) <- case types_sens of
    [(τ1,s1),(τ2,s2)] -> pure ((τ1,s1),(τ2,s2))
    _ -> impossible $ "Wrong array return size of makeTypeOp in " <> showPretty term

  -- Create variables for the gradient type
  -- (norm and clip parameters and dimension)
  nrm <- newVar
  clp1 <- newVar
  clp2 <- newVar
  m <- newVar

  -- infer the types of the scalar and the gradient
  let dg1 = checkSens scope g1
  let dg2 = checkSens scope g2

  -- sum contexts and scale with corresponding op sensitivities
  (tg1, tg2) <- msumTup ((dg1 <* mscale (svar s1)), (dg2 <* mscale (svar s2)))

  -- set types to the actual content type of the dmgrads
  -- (we allow any kind of annotation on the dmgrads here but they gotta match)
  τ1num <- newVar
  τ2num <- newVar
  unify τ1 (Numeric τ1num)
  unify τ2 (Numeric τ2num)
  unify tg1 (NoFun (DMGrads nrm clp1 m (NoFun τ1)))
  unify tg2 (NoFun (DMGrads nrm clp2 m (NoFun τ2)))

  -- the return type is the same matrix, but
  -- the clipping is now changed to unbounded
  -- and the content type is the result type of the addition
  τresnum <- newVar
  return (NoFun (DMGrads nrm U m (NoFun (Numeric τresnum))))


checkSen' scope term@(SBind x a b) = do
  throwError (TypeMismatchError $ "Found the term\n" <> showPretty term <> "\nwhich is a privacy term because of the bind in a place where a sensitivity term was expected.")


checkSen' scope term@(InternalExpectConst a) = do
  res <- checkSens scope a
  sa <- newVar
  ta <- newVar
  res' <- unify res (NoFun (Numeric (Num ta (Const sa))))

  return res'

-- 
-- The user can explicitly copy return values.
--
checkSen' scope term@(Clone t) = checkSen' scope t -- do
  -- res <- checkSens scope t

  -- ta <- newVar
  -- res' <- unify res (NoFun (ta))

  -- return (NoFun (ta))



-- Everything else is currently not supported.
checkSen' scope t = throwError (TermColorError SensitivityK t)

--------------------------------------------------------------------------------
-- Privacy terms

checkPri' :: DMScope -> DMTerm -> TC DMMain
checkPri' scope (Ret t) = do
   τ <- checkSens scope t
   mtruncateP inftyP
   log $ "checking privacy " <> show (Ret t) <> ", type is " <> show τ
   return τ

{-
checkPri' scope (Rnd t) = do
  τ <- (createDMTypeBaseNum t)
  return (NoFun (Numeric (NonConst τ)))
-}

checkPri' scope (Apply f args) =
  let
    -- check the argument in the given scope,
    -- and scale scope by new variable, return both
    checkArg :: DMScope -> DMTerm -> (TC (DMMain :@ Privacy))
    checkArg scope arg = do
      τ <- checkSens scope arg
      restrictAll oneId -- sensitivity of everything in context must be <= 1
      p <- newPVar
      mtruncateP p
      return (τ :@ p)

    margs = (\arg -> (checkArg scope arg)) <$> args

    f_check :: (TC DMMain) = do
       -- we typecheck the function, but `apply` our current layer on the Later computation
       -- i.e. "typecheck" means here "extracting" the result of the later computation
       res <- (checkSens scope f)
       logForce ("[Apply-Priv]Scope is:\n" <> show (getAllKeys scope))
       mtruncateP inftyP -- truncate f's context to ∞
       return res

  in do
    (τ_sum :: DMMain, argτs) <- msumTup (f_check , msumP margs) -- sum args and f's context
    τ_ret <- newVar -- a type var for the function return type
    addConstraint (Solvable (IsFunctionArgument (τ_sum, Fun [(argτs :->*: τ_ret) :@ Nothing])))

    return τ_ret


checkPri' scope (SLet (x :- dτ) term body) = do

  -- put the computation to check the term into the scope
  --  let scope' = setValue x (checkSens term scope) scope
  let scope' = setValue x (checkSens scope term) scope

  -- check body with that new scope
  result <- checkPriv scope' body

  log $ "checking (transparent) privacy SLet: " <> show (x :- dτ) <> " = " <> show term <> " in " <> show body
  case dτ of
    JTAny -> return dτ
    dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

  return result

checkPri' scope (SBind (x :- dτ) term body) = do
  -- this is the bind rule.
  -- as it does not matter what sensitivity/privacy x has in the body, we put an Arg term in the scope
  -- and later discard its annotation. we use checkSens because there are no Vars in privacy terms so
  -- x will only ever be used in a sensitivity term.
  let scope' = setValue x (checkSens scope (Arg x dτ NotRelevant)) scope

  -- check body with that new scope
  let dbody = checkPriv scope' body 
  let mbody = do
             τ <- dbody
             -- discard x from the context, never mind it's inferred annotation
             WithRelev _ (τx :@ _) <- removeVar @PrivacyK x
             return (τ, τx)

  -- check term with old scope
  let dterm = checkPriv scope term

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

checkPri' scope (FLet fname term body) = do

  -- make a Choice term to put in the scope
  let scope' = pushChoice fname (checkSens scope term) scope

  -- check body with that new scope. Choice terms will result in IsChoice constraints upon ivocation of fname
  result <- checkPriv scope' body 

  removeVar @PrivacyK fname
  return result


-----------------------------------
-- "transparent" privacy tlets

checkPri' original_scope curterm@(TLet xs term body) = do

  -- put the computations to check the terms into the scope
  -- (in privacy terms we use projections here, making this a "transparent" tlet)

  let addarg scope (x :- _, i) = setValue x (checkSens original_scope (TProject i term)) scope
  let scope_with_args = foldl addarg original_scope (xs `zip` [0..])

  -- -- check body with that new scope
  result <- checkPriv scope_with_args body

  log $ "checking (transparent) privacy SLet: " <> show xs <> " = " <> show term <> " in " <> show body
  case and [True | (_ :- JTAny) <- xs] of
      True  -> return ()
      False -> throwError (ImpossibleError $ "Type annotations on variables not yet supported\n when checking " <> showPretty curterm)

  return result
checkPri' original_scope curterm@(TBind xs term body) = do
  a <- newTeVar "tbind_var"
  -- we check the term
  -- ```
  --  sbind a <- term
  --  tlet (xs...) = a
  --  body
  -- ```
  checkPri' original_scope (SBind (a :- JTAny) term
                   (TLet xs (Var (a :- JTAny))
                         body))


-----------------------------------
-- PRIVACY TUPLE HACK
--
{-
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
checkPri' (Tup ts) scope = do
   names <- mapM newTeVar [(T.pack ("x" <> (show i))) | i <- [1..(length ts)]] -- make unique new names for the elements.
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
checkPri' (TLet xs term body) scope = do
   tupvar <- newTeVar "tup" -- make a new unique name for the tup
   let t1 = foldl (\t -> \(x :- τj) -> SLet (x :- τj) (Ret (TLet xs (Var (tupvar :- JTAny)) (Var (x :- τj)))) t) body xs
       t2 = SLet (tupvar :- (JTAny)) term t1
   checkPriv t2 scope
-}

checkPri' scope (MutGauss rp εp δp f) = checkPri' scope (Gauss rp εp δp f)
checkPri' scope (Gauss rp εp δp f) =
  let
   setParam :: TC DMMain -> Sensitivity -> TC ()
   setParam dt v = do -- parameters must be const numbers.
      τ <- dt
      τv <- newVar
      unify τ (NoFun (Numeric (Num τv (Const v))))
      mtruncateP zeroId
      return ()

   setBody df (ε, δ) r = do
      -- extract f's type from the TC monad
      τf <- df
      -- interesting input variables must have sensitivity <= r
      restrictInteresting r
      -- interesting output variables are set to (ε, δ), the rest is truncated to ∞
      ctxBeforeTrunc <- use types
      logForce $ "[Gauss] Before truncation, context is:\n" <> show ctxBeforeTrunc
      mtruncateP inftyP
      ctxAfterTrunc <- use types
      logForce $ "[Gauss] After truncation, context is:\n" <> show ctxAfterTrunc
      (ivars, itypes) <- getInteresting
      mapM (\(x, (τ :@ _)) -> setVarP x (WithRelev IsRelevant (τ :@ PrivacyAnnotation (ε, δ)))) (zip ivars itypes)
      -- return type is a privacy type.
      return τf
   in do
      -- check all the parameters and f, extract the TC monad from the Delayed monad.
      let drp = checkSens scope rp
      let dεp = checkSens scope εp
      let dδp = checkSens scope δp
      let df  = checkSens scope f

      -- create variables for the parameters
      v_ε :: Sensitivity <- newVar
      v_δ :: Sensitivity <- newVar
      v_r :: Sensitivity <- newVar

      -- parameters must be in (0,1) for gauss to be DP
      addConstraint (Solvable (IsLess (v_ε, oneId :: Sensitivity)))
      addConstraint (Solvable (IsLess (v_δ, oneId :: Sensitivity)))
      addConstraint (Solvable (IsLess (zeroId :: Sensitivity, v_ε)))
      addConstraint (Solvable (IsLess (zeroId :: Sensitivity, v_δ)))

      -- restrict interesting variables in f's context to v_r
      let mf = setBody df (v_ε, v_δ) v_r

      let mr = setParam drp v_r
      let mε = setParam dεp v_ε
      let mδ = setParam dδp v_δ

      (τf, _) <- msumTup (mf, msum3Tup (mr, mε, mδ))

      τgauss <- newVar
      addConstraint (Solvable (IsAdditiveNoiseResult ((NoFun τgauss), τf))) -- we decide later if its gauss or mgauss according to return type
 
      return (NoFun (τgauss))


checkPri' scope (MutLaplace rp εp f) = checkPri' scope (Laplace rp εp f)
checkPri' scope (Laplace rp εp f) =
  let
   setParam :: TC DMMain -> Sensitivity -> TC ()
   setParam dt v = do -- parameters must be const numbers.
      τ <- dt
      τv <- newVar
      unify τ (NoFun (Numeric (Num τv (Const v))))
      mtruncateP zeroId
      return ()

   setBody df ε r = do
      -- extract f's type from the TC monad
      τf <- df
      -- interesting input variables must have sensitivity <= r
      restrictInteresting r
      -- interesting output variables are set to (ε, δ), the rest is truncated to ∞
      mtruncateP inftyP
      (ivars, itypes) <- getInteresting
      mapM (\(x, (τ :@ _)) -> setVarP x (WithRelev IsRelevant (τ :@ PrivacyAnnotation (ε, zeroId)))) (zip ivars itypes)
      -- return type is a privacy type.
      return τf
   in do
      -- check all the parameters and f, extract the TC monad from the Delayed monad.
      let drp = checkSens scope rp
      let dεp = checkSens scope εp
      let df  = checkSens scope f

      -- create variables for the parameters
      v_ε :: Sensitivity <- newVar
      v_r :: Sensitivity <- newVar

      -- eps parameter must be > 0 for scaling factor to be well-defined
      addConstraint (Solvable (IsLess (zeroId :: Sensitivity, v_ε)))

      -- sensitivity parameter must be > 0 for laplace distribution to be well-defined
      addConstraint (Solvable (IsLess (zeroId :: Sensitivity, v_r)))

      -- restrict interesting variables in f's context to v_r
      let mf = setBody df v_ε v_r

      let mr = setParam drp v_r
      let mε = setParam dεp v_ε

      (τf, _) <- msumTup (mf, msumTup (mr, mε))

      τlap <- newVar
      addConstraint (Solvable (IsAdditiveNoiseResult ((NoFun τlap), τf))) -- we decide later if its lap or mlap according to return type
 
      return (NoFun (τlap))


checkPri' scope (AboveThresh qs e d t) = do
      eps <- newVar

      let mqs = checkSens scope qs <* mtruncateP inftyP
      let me = checkSens scope e   <* mtruncateP (zeroId, zeroId)
      let md  = checkSens scope d  <* mtruncateP (eps, zeroId)
      let mt  = checkSens scope t  <* mtruncateP inftyP

      n <- newVar -- number of queries
      nrm <- newVar -- norm of query vector
      clp <- newVar -- clip of query vector

      (τqs, (τe, τd, τt)) <- msumTup (mqs, msum3Tup (me, md, mt))

      unify τqs (NoFun (DMVec nrm clp n (Fun [([τd :@ (oneId :: Sensitivity)] :->: (NoFun (Numeric (Num DMReal NonConst)))) :@ Just [JTAny]])))
      addConstraint (Solvable (IsLessEqual (τe, (NoFun (Numeric (Num DMReal (Const eps)))))))
      addConstraint (Solvable (IsLessEqual (τt, (NoFun (Numeric (Num DMReal NonConst))))))

      return (NoFun (Numeric (Num DMInt NonConst)))


checkPri' scope (Loop niter cs' (xi, xc) body) =
   --let setInteresting :: ([Symbol],[DMMain :@ PrivacyAnnotation]) -> Sensitivity -> TC ()
   let setInteresting (xs, τps) n = do
          let τs = map fstAnn τps
          let ps = map sndAnn τps

          let ε = maxS (map (\(PrivacyAnnotation (εs, _)) -> εs) ps)
          let δ = maxS (map (\(PrivacyAnnotation (_, δs)) -> δs) ps)

          δn :: Sensitivity <- newVar -- we can choose this freely!
          addConstraint (Solvable (IsLessEqual (δn, oneId :: Sensitivity))) -- otherwise we get a negative ε...
          addConstraint (Solvable (IsLess (zeroId :: Sensitivity, δn))) -- otherwise we get an infinite ε...

          -- compute the new privacy for the xs according to the advanced composition theorem
          let two = oneId ⋆! oneId
          let newp = (two ⋅! (ε ⋅! (sqrt (two ⋅! (n ⋅! (minus (ln oneId) (ln δn)))))), δn ⋆! (n ⋅! δ))

          mapM (\(x, τ) -> setVarP x (WithRelev IsRelevant (τ :@ PrivacyAnnotation newp))) (zip xs τs)
          return ()

   in do
      --traceM $ "checking privacy Loop: " <> show  (Loop niter cs (xi, xc) body)
      let cniter = checkSens scope niter <* mtruncateP zeroId

      -- build the tup of variables
      let cs = Tup ((\a -> Var (a :- JTAny)) <$> cs')

      -- check it
      let mcaps = checkSens scope cs <* mtruncateP inftyP

      -- add iteration and capture variables as args-checking-commands to the scope
      -- capture variable is not relevant bc captures get ∞ privacy anyways
      -- TODO: do we need to make sure that we have unique names here?
      let scope'  = setValue xi (checkSens scope (Arg xi JTInt NotRelevant)) scope
      let scope'' = setValue xc (checkSens scope (Arg xc JTAny NotRelevant)) scope'

      -- check body term in that new scope
      let cbody = checkPriv scope'' body 

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

      -- scale and sum contexts
      -- τit = type of the iterator (i.e. the term describung the number of iterations)
      -- τcs = type of the capture input tuple
      -- τb = inferred type of the body
      -- n = number of iterations as assumed in the loop body
      -- τbit = type of the iterator variable xi inferred in the body
      -- τbcs = type of the capture variable xc inferred in the body
      (τit, τloop_in, (τbody_out, n, τbit, τbody_in)) <- msum3Tup (cniter, mcaps, cbody')

      unify τit (NoFun (Numeric (Num DMInt (Const n)))) -- number of iterations must be constant integer
      unify (NoFun (Numeric (Num DMInt NonConst))) τbit -- number of iterations must match type requested by body

      τcsnf <- newVar
      unify (NoFun τcsnf) τloop_in -- functions cannot be captured.

{-
      -- TODO loops with Const captures/output don't work yet.
      -- the inferred capture type should be the same as the non-const version of the inferred body type
      -- so we can loop properly by plugging the loop result into the loop in again
      -- the inferred type for xc must be non-const, as we cannot assume that it will be the same in each
      -- iteration.
      addConstraint (Solvable (IsNonConst (τb, τbcs)))

      -- also the given capture that we start iteration with should fit into the expected capture
      addConstraint (Solvable (IsNonConst (τcs, τbcs)))
-}

      -- the types of body, input captures and captures as used in the body must all be equal
      -- (except Const-ness, actually. we'll figure that out at some point)

      addConstraint (Solvable (IsNonConst (τbody_out, τbody_in)))
      addConstraint (Solvable (UnifyWithConstSubtype (τloop_in, τbody_out)))

      return τbody_in



checkPri' scope (Reorder σ t) = do
  τ <- checkPriv scope t
  ρ <- newVar
  addConstraint (Solvable (IsReorderedTuple ((σ , τ) :=: ρ)))
  return ρ


checkPri' scope (SmpLet xs (Sample n m1_in m2_in) tail) =
  let checkArg :: DMTerm -> (TC (DMMain, Privacy))
      checkArg arg = do
         -- check the argument in the given scope,
         -- and scale scope by new variable, return both
         τ <- checkSens scope arg
         restrictAll oneId -- sensitivity of everything in context must be <= 1
         p <- newPVar
         mtruncateP p
         return (τ, p)
         
      mn = checkArg n
      mm1 = checkArg m1_in
      mm2 = checkArg m2_in
      msum = msum3Tup (mn, mm1, mm2)
      
      mtail = do
                -- add all variables bound by the sample let as args-checking-commands to the scope
                -- TODO: do we need to make sure that we have unique names here?
                let addarg scope' (x :- τ) = setValue x (checkSens scope (Arg x τ IsRelevant)) scope'
                let scope_with_samples = foldl addarg scope xs
              
                -- check the tail in the scope with the new args
                τ <- checkPriv scope_with_samples tail
              
                -- append the computation of removing the args from the context again, remembering their types
                -- and privacies
                xs_types_privs <- mapM (removeVar @PrivacyK) [ x | (x :- _) <- xs]
                let xs_types_privs' = [ (ty,p) | WithRelev _ (ty :@ PrivacyAnnotation p) <- xs_types_privs ]
                -- truncate tail context to infinite privacy and return tail type and args types/privacies
                case xs_types_privs' of
                     [(t1,p1), (t2,p2)] -> ((return (τ,(t1,p1),(t2,p2))) <* mtruncateP inftyP)
                     _ -> impossible $ ("Both results of sample must be assigned a name. Instead I got " <> (show xs_types_privs'))
  in do
      -- sum all involved contexts.
      -- tn, tm1, tm2: types of n_samples and the two matrices that are sampled
      -- pn, pm1, pm2: privacy vars that truncate the context of n, m1_in and m2_in
      -- ttail: inferred type of the tail
      -- (t1, (e1,d1)), (t2, (e2,d2)): inferred types and privacies of the xs in the tail
      (((tn,pn), (tm1,pm1), (tm2,pm2)), (ttail, (t1, (e1,d1)), (t2, (e2,d2)))) <- msumTup (msum, mtail)
      
      -- variables for clip parameter, dimensions and number of samples (m2)
      clp <- newVar
      m1 <- newVar
      m2 <- newVar
      n1 <- newVar
      n2 <- newVar
    
      -- set number of samples to const m2 and truncate context with 0
      unify tn (NoFun (Numeric (Num DMInt (Const m2))))
      unify pn (zeroId, zeroId)
      
      -- set input matrix types and truncate contexts to what it says in the rule
      unify tm1 (NoFun (DMMat LInf clp m1 n1 (NoFun (Numeric DMData))))
      unify tm2 (NoFun (DMMat LInf clp m1 n2 (NoFun (Numeric DMData))))
      let two = oneId ⋆! oneId
      unify pm1 (divide (two ⋅! (m2 ⋅! e1)) m1, divide (m2 ⋅! d1) m1)
      unify pm2 (divide (two ⋅! (m2 ⋅! e2)) m1, divide (m2 ⋅! d2) m1)

      -- set correct types for sample results in the tail
      unify tm1 t1
      unify tm2 t2

      -- expression has type of the tail
      return ttail
    
checkPri' scope t = throwError (TermColorError PrivacyK t)





---------------------------------------------------------
-- julia type conversion for black boxes

checkBBKind :: DMScope -> BBKind EmptyExtension -> TC DMMain
checkBBKind scope a = let
 getFloat :: TC (DMTypeOf NumKind)
 getFloat = do
                v <- newVar
                addConstraint (Solvable (IsFloat $ NoFun (Numeric v)))
                return v
 in case a of
  BBSimple jt -> case jt of
    JTInt  -> return $ NoFun $ Numeric $ Num DMInt NonConst
    JTReal -> do v <- getFloat; return $ NoFun $ Numeric $ v
    _      -> throwError $ TypeMismatchError $ "The type " <> show jt <> " is not allowed as return type of black boxes.\n"
                                              <> "You can only have annotations of the following form:\n"
                                              <> "[redacted]"
  BBVecLike jt pdt -> do
    -- typecheck the term 
    pdt_actual_ty <- checkSens scope pdt <* mscale zeroId

    -- make sure that it is const
    pdt_val <- newVar
    pdt_ty <- newVar
    unify pdt_actual_ty (NoFun $ Numeric $ Num pdt_ty (Const pdt_val))

    -- look what type was requested in form of a julia type
    case jt of
      JTVector JTInt -> do n <- newVar ; return $ NoFun $ DMVec n U pdt_val (NoFun $ Numeric $ Num DMInt NonConst)
      JTVector JTReal -> do n <- newVar ; r <- getFloat; return $ NoFun $ DMVec n U pdt_val (NoFun $ Numeric r)
      JTModel -> do r <- getFloat; return $ NoFun $ DMModel pdt_val r
      JTGrads -> do n <- newVar; r <- getFloat;  return $ NoFun $ DMGrads n U pdt_val (NoFun $ Numeric $ r)
      _ -> throwError $ TypeMismatchError $ "The type " <> show jt <> " is not allowed as return type of black boxes.\n"
                                              <> "You can only have annotations of the following form:\n"
                                              <> "[redacted]"


  BBMatrix jt pdt1 pdt2 -> do
    -- typecheck the terms
    (pdt1_actual_ty,pdt2_actual_ty) <- msumTup (checkSens scope pdt1, checkSens scope pdt2) <* mscale zeroId

    -- make sure they are is const
    pdt1_val <- newVar
    pdt1_ty <- newVar
    unify pdt1_actual_ty (NoFun $ Numeric $ Num pdt1_ty (Const pdt1_val))

    pdt2_val <- newVar
    pdt2_ty <- newVar
    unify pdt2_actual_ty (NoFun $ Numeric $ Num pdt2_ty (Const pdt2_val))

    -- look what type was requested in form of a julia type
    case jt of
      JTMatrix jt | or [jt == JTInt, jt == JTReal] -> do n <- newVar ; r <- getFloat; return $ NoFun $ DMMat n U pdt1_val pdt2_val (NoFun $ Numeric $ r)
      _ -> throwError $ TypeMismatchError $ "The type " <> show jt <> " is not allowed as return type of black boxes.\n"
                                              <> "You can only have annotations of the following form:\n"
                                              <> "[redacted]"


