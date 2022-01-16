
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

-- TODO: Here we assume that η really has type τ, and do not check it. Should maybe do that.
checkSen' scope (Sng η τ) = do
  res <- Numeric <$> (Const (constCoeff (Fin η)) <$> (createDMTypeBaseNum τ))
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
  logForce $ "checking arg:" <> show (Just x :- jτ) <> ", dmtype is " <> show τs
  -- the inferred type must be a subtype of the user annotation, if given.
  addJuliaSubtypeConstraint τs jτ

  -- put the variable in the Γ context with sensitivity 1
  setVarS x (WithRelev i (τs :@ SensitivityAnnotation oneId))
  return τs


checkSen' scope (Var (x :- dτ)) =  -- get the term that corresponds to this variable from the scope dict
   let mτ = getValueMaybe x scope
   in case mτ of
     Nothing -> logForce ("[Var-Sens] Scope is:\n" <> show (getAllKeys scope)) >> throwError (VariableNotInScope x)
     Just jτ -> do
                     logForce ("[Var-Sens] Scope is:\n" <> show (getAllKeys scope))
                     τ <- jτ -- extract the type of x
                     -- if the user has given an annotation
                     -- inferred type must be a subtype of the user annotation
                     addJuliaSubtypeConstraint τ dτ
                     return τ

checkSen' scope (Lam xτs body) =
  -- the body is checked in the toplevel scope, not the current variable scope.
  -- this reflects the julia behaviour
  do

    -- put a special term to mark x as a function argument. those get special treatment
    -- because we're interested in their privacy. put the relevance given in the function signature, too.
    let f s sc (Just x :- τ) = setValue x (checkSens s (Arg x τ IsRelevant)) sc
        f s sc (Nothing :- τ) = sc
    let addArgs s = foldl (f s) s xτs
    let scope' = addArgs scope

    -- check the body in the modified scope
    restype <- checkSens scope' body

    -- extract julia signature
    let sign = (sndA <$> xτs)
        
    -- get inferred types and sensitivities for the arguments
    xrτs <- getArgList @_ @SensitivityK xτs
    let xrτs' = [x :@ s | (x :@ SensitivityAnnotation s) <- xrτs]
    logForce $ "Checking Lam, outer scope: " <> show (getAllKeys scope) <> " | inner: " <> show (getAllKeys scope')

    -- make an arrow type.
    let τ = (xrτs' :->: restype)
    return (Fun [τ :@ (Just sign)])


checkSen' scope (LamStar xτs body) =
  -- the body is checked in the toplevel scope, not the current variable scope.
  -- this reflects the julia behaviour
  do
    -- put a special term to mark x as a function argument. those get special treatment
    -- because we're interested in their sensitivity
    let f s sc (Just x :- (τ , rel)) = setValue x (checkSens s (Arg x τ rel)) sc
        f s sc (Nothing :- _) = sc
    let addArgs s = foldl (f s) s xτs
    let scope' = addArgs scope

    -- check the body in the modified scope
    restype <- checkPriv scope' body

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
    return (Fun [τ :@ (Just sign)])


checkSen' scope (SLet (x :- dτ) term body) = do

   -- put the computation to check the term into the scope
   --  let scope' = setValueMaybe x (checkSens term scope) scope
   let scope' = setValueMaybe x (checkSens scope term) scope

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




checkSen' scope (BBApply app args cs) =
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
    (τ_box :: DMMain, argτs, _) <- msum3Tup (mf , msumS margs, msumS caps) -- sum args and f's context
    τ_ret <- newVar -- a type var for the function return type
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

    sbranch_check mf margs = do
        (τ_sum :: DMMain, argτs) <- msumTup (mf , msumS margs) -- sum args and f's context
        τ_ret <- newVar -- a type var for the function return type
        addConstraint (Solvable (IsFunctionArgument (τ_sum, Fun [(argτs :->: τ_ret) :@ Nothing])))
        return τ_ret

    margs = checkArg scope <$> args
    mf = checkSens scope f

  in do
    logForce ("[Apply-Sens]Scope is:\n" <> show (getAllKeys scope))
    sbranch_check mf margs

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
  let addarg scope (Just x :- τ) = setValue x (checkSens original_scope (Arg x τ NotRelevant)) scope
      addarg scope (Nothing :- τ) = scope
  let scope_with_args = foldl addarg original_scope xs

  -- check the body in the scope with the new args
  let cbody = checkSens scope_with_args body

  -- append the computation of removing the args from the context again, remembering their types
  -- and sensitivities
  let cbody' = do
        τ <- cbody
        xs_types_sens <- mapM (removeVar @SensitivityK) [x | (Just x :- _) <- xs]
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
  let cs = Tup ((\a -> Var (Just a :- JTAny)) <$> cs')
  -- check it
  let ccs = checkSens scope cs

  -- add iteration and capture variables as args-checking-commands to the scope
  -- TODO: do we need to make sure that we have unique names here?
  let scope' = case xi of
                 Just xi -> setValue xi (checkSens scope (Arg xi JTInt NotRelevant)) scope
                 Nothing -> scope
  let scope'' = setValue xc (checkSens scope (Arg xc JTAny IsRelevant)) scope'

  -- check body term in that new scope
  let cbody = checkSens scope'' body

  -- append the computation of removing the args from the context again, remembering their types
  -- and sensitivities
  let cbody' = do
        τ <- cbody
        WithRelev _ (τi :@ si) <- removeVarMaybe @SensitivityK xi
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
  (τit, τcs, (τb, (τbit, sbit), (τbcs, sbcs))) <- msum3Tup (cniter <* mscale sit, ccs <* mscale scs, cbody' <* mscale sb)

  unify (NoFun (Numeric (NonConst DMInt))) τbit -- number of iterations must match type requested by body

  τcsnf <- newVar
  unify (NoFun τcsnf) τcs -- functions cannot be captured.

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
  unify τb τbcs
  unify τcs τbcs

  return τbcs


checkSen' scope (MCreate n m (x1, x2) body) =
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

      let mn    = checkSens scope n
      let mm    = checkSens scope m
      let mbody = checkSens scope body

      -- variables for matrix dimension
      nv <- newVar
      mv <- newVar

      (τbody, _, _) <- msum3Tup (checkBody mbody nv mv, setDim mn nv, setDim mm mv)

      -- matrix entries cannot be functions.
      τ <- newVar
      unify τbody (NoFun τ)

      nrm <- newVar -- variable for norm
      return (NoFun (DMMat nrm U nv mv τ))

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

  return (NoFun (DMTup [Numeric (Const nv DMInt), Numeric (Const mv DMInt)]))


checkSen' scope (ClipM c m)  = do
  τb <- checkSens scope m -- check the matrix

  -- variables for norm and clip parameters and dimension
  nrm <- newVar
  clp <- newVar
  n <- newVar

  -- set correct matrix type
  unify τb (NoFun (DMGrads nrm clp n (Numeric DMData)))

  -- change clip parameter to input
  return (NoFun (DMTup [DMGrads nrm c n (Numeric DMData)]))

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

  -- set correct matrix type
  unify τb (NoFun (DMGrads nrm (Clip clp) n (Numeric DMData)))

  -- we have to scale by two unlike in the paper...see the matrixnorms pdf in julia docs
  mscale (oneId ⋆! oneId)

  -- move clip to the norm position,
  -- and forget about old `nrm
  -- technically the clipping parameter does not change, but we set it to U so it fits with the rest...
  -- see issue 
--  return (NoFun (DMGrads clp (Clip clp) n (Numeric (NonConst DMReal))))
  return (NoFun (DMTup [DMGrads clp U n (Numeric (NonConst DMReal))]))

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
      unify τm (NoFun (DMMat nrm clp n m (Numeric τ)))

      -- we don't restrict matrix dimension or index size, but leave that to the runtime errors...

      return (NoFun (Numeric τ))


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
      unify τv (NoFun (DMVec nrm clp n (Numeric τ)))

      -- we don't restrict vector dimension or index size, but leave that to the runtime errors...

      return (NoFun (Numeric τ))

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
      unify τm (NoFun (DMMat nrm clp n m (Numeric τ)))

      -- we don't restrict matrix dimension or index size, but leave that to the runtime errors...

      return (NoFun (DMVec nrm clp m (Numeric τ))) -- returns Vector type to accomodate julia behaviour

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
      unify ps (NoFun (DMParams m (Numeric τps)))
      unify gs (NoFun (DMGrads nrm clp m (Numeric τgs)))

      res <- TVar <$> newTVar "τr"
      addConstraint (Solvable (IsTypeOpResult (Binary DMOpSub ((Numeric τps):@s1, (Numeric τgs):@s2) res)))

      return (NoFun (DMTup [DMParams m res]))

checkSen' scope (ScaleGrad scalar grad) = do

  let dscalar = checkSens scope scalar
  let dgrad = checkSens scope grad

  -- Create sensitivity / type variables for the multiplication
  (τres , types_sens) <- makeTypeOp (IsBinary DMOpMul) 2

  ((τ1,s1),(τ2,s2)) <- case types_sens of
    [(τ1,s1),(τ2,s2)] -> pure ((τ1,s1),(τ2,s2))
    _ -> impossible "Wrong array return size of makeTypeOp"

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
  unify tscalar (NoFun τ1)

  -- and τ2 to the actual content type of the dmgrads
  -- (we allow any kind of annotation on the dmgrads here)
  unify tgrad (NoFun (DMGrads nrm clp m τ2))

  -- the return type is the same matrix, but
  -- the clipping is now changed to unbounded
  -- and the content type is the result of the multiplication
  return (NoFun (DMTup [DMGrads nrm U m τres]))

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

checkSen' scope (LastTerm t) = do
  -- typecheck the term t, and apply the current scope to it
  -- applyAllDelayedLayers scope (checkSens t scope)
  (checkSens scope t)


checkSen' scope (ZeroGrad m) = do
   -- check model
   tm <- checkSens scope m

   -- variables for element type, dimension, result norm and clip parameters
   τps <- newVar
   n <- newVar
   nrm <- newVar
   clp <- newVar -- actually variable, as all entries are zero

   -- input must be a model
   unify tm (NoFun (DMParams n (Numeric τps)))

   -- model gets copied into the params so it's infinitely sensitive
   mscale inftyS

   return (NoFun (DMGrads nrm clp n (Numeric τps)))


checkSen' scope (SumGrads g1 g2) = do

  -- Create sensitivity / type variables for the addition
  (τres , types_sens) <- makeTypeOp (IsBinary DMOpAdd) 2

  ((τ1,s1),(τ2,s2)) <- case types_sens of
    [(τ1,s1),(τ2,s2)] -> pure ((τ1,s1),(τ2,s2))
    _ -> impossible "Wrong array return size of makeTypeOp"

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
  unify tg1 (NoFun (DMGrads nrm clp1 m τ1))
  unify tg2 (NoFun (DMGrads nrm clp2 m τ2))

  -- the return type is the same matrix, but
  -- the clipping is now changed to unbounded
  -- and the content type is the result type of the addition
  return (NoFun (DMGrads nrm U m τres))


checkSen' scope term@(SBind x a b) = do
  throwError (TypeMismatchError $ "Found the term\n" <> showPretty term <> "\nwhich is a privacy term because of the bind in a place where a sensitivity term was expected.")


checkSen' scope term@(InternalExpectConst a) = do
  res <- checkSens scope a
  sa <- newVar
  ta <- newVar
  res' <- unify res (NoFun (Numeric (Const sa ta)))

  return res'

-- Everything else is currently not supported.
checkSen' scope t = (throwError (UnsupportedTermError t))


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

-- it is ambiguous if this is an application of a LamStar or an application of a Lam followed by implicit Return.
-- we handle that by resolving IsFunctionArgument ( T -> T, S ->* S) by setting S's privacies to infinity.
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
  --  let scope' = setValueMaybe x (checkSens term scope) scope
  let scope' = setValueMaybe x (checkSens scope term) scope

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
  let scope' = case x of
                 Just x -> setValue x (checkSens scope (Arg x dτ NotRelevant)) scope
                 Nothing -> scope

  -- check body with that new scope
  let dbody = checkPriv scope' body 
  let mbody = do
             τ <- dbody
             -- discard x from the context, never mind it's inferred annotation
             WithRelev _ (τx :@ _) <- removeVarMaybe @PrivacyK x
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

  let addarg scope (Just x :- _, i) = setValue x (checkSens original_scope (TProject i term)) scope
      addarg scope (Nothing :- _, i) = scope
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
  checkPri' original_scope (SBind (Just a :- JTAny) term
                   (TLet xs (Var (Just a :- JTAny))
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

checkPri' scope (Gauss rp εp δp f) =
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
      ctxBeforeTrunc <- use types
      logForce $ "[Gauss] Before truncation, context is:\n" <> show ctxBeforeTrunc
      mtruncateP inftyP
      ctxAfterTrunc <- use types
      logForce $ "[Gauss] After truncation, context is:\n" <> show ctxAfterTrunc
      (ivars, itypes) <- getInteresting
      logForce $ ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>\nInteresting variables: " <> show ivars <> "\n<<<<<<<<<<<<<<<<" 
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

      -- restrict input type to the correct thing
      n <- newVar -- dimension of input vector can be anything
      iclp <- newVar -- clip of input vector can be anything
      τv <- newVar -- input element type can be anything (as long as it's numeric)
      addConstraint(Solvable(IsLessEqual(τf, (NoFun (DMGrads L2 iclp n (Numeric (τv)))))))

      -- return result type as a tuple bc gauss is a mutating function
      return (NoFun (DMTup [(DMGrads LInf U n (Numeric (NonConst DMReal)))]))


checkPri' scope (Laplace rp εp f) =
  let
   setParam :: TC DMMain -> Sensitivity -> TC ()
   setParam dt v = do -- parameters must be const numbers.
      τ <- dt
      τv <- newVar
      unify τ (NoFun (Numeric (Const v τv)))
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
      logForce $ ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>\nInteresting variables: " <> show ivars <> "\n<<<<<<<<<<<<<<<<" 
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


      -- restrict input type to the correct thing
      n <- newVar -- dimension of input vector can be anything
      iclp <- newVar -- clip of input vector can be anything
      τv <- newVar -- input element type can be anything (as long as it's numeric)
      addConstraint(Solvable(IsLessEqual(τf, (NoFun (DMGrads L2 iclp n (Numeric (τv)))))))

      -- return result type as a tuple bc laplace is a mutating function
      return (NoFun (DMTup [(DMGrads LInf U n (Numeric (NonConst DMReal)))]))


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
      let cniter = checkSens scope niter

      let cniter' = do
                   τ <- cniter
                   mtruncateP zeroId
                   return τ

      -- build the tup of variables
      let cs = Tup ((\a -> Var (Just a :- JTAny)) <$> cs')

      -- check it
      let mcaps = checkSens scope cs
      let mcaps' = do
                   τ <- mcaps
                   mtruncateP inftyP
                   return τ


      -- add iteration and capture variables as args-checking-commands to the scope
      -- capture variable is not relevant bc captures get ∞ privacy anyways
      -- TODO: do we need to make sure that we have unique names here?
      let scope' = case xi of
                     Just xi -> setValue xi (checkSens scope (Arg xi JTInt NotRelevant)) scope
                     Nothing -> scope
      let scope'' = setValue xc (checkSens scope (Arg xc JTAny NotRelevant)) scope'

      -- check body term in that new scope
      let cbody = checkPriv scope'' body 

      -- append the computation of removing the args from the context again, remembering their types
      -- and sensitivities
      let cbody' = do
            τ <- cbody
            WithRelev _ (τi :@ _) <- removeVarMaybe @PrivacyK xi
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
      (τit, τcs, (τb, n, τbit, τbcs)) <- msum3Tup (cniter', mcaps', cbody')

      unify τit (NoFun (Numeric (Const n DMInt))) -- number of iterations must be constant integer
      unify (NoFun (Numeric (NonConst DMInt))) τbit -- number of iterations must match type requested by body

      τcsnf <- newVar
      unify (NoFun τcsnf) τcs -- functions cannot be captured.

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
      unify τb τbcs
      unify τcs τbcs

      return τbcs



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
                let addarg scope' (Just x :- τ) = setValue x (checkSens scope (Arg x τ IsRelevant)) scope'
                    addarg scope' (Nothing :- τ) = scope'
                let scope_with_samples = foldl addarg scope xs
              
                -- check the tail in the scope with the new args
                τ <- checkPriv scope_with_samples tail
              
                -- append the computation of removing the args from the context again, remembering their types
                -- and privacies
                xs_types_privs <- mapM (removeVar @PrivacyK) [ x | (Just x :- _) <- xs]
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
      unify tn (NoFun (Numeric (Const m2 DMInt)))
      unify pn (zeroId, zeroId)
      
      -- set input matrix types and truncate contexts to what it says in the rule
      unify tm1 (NoFun (DMMat LInf clp m1 n1 (Numeric DMData)))
      unify tm2 (NoFun (DMMat LInf clp m1 n2 (Numeric DMData)))
      let two = oneId ⋆! oneId
      unify pm1 (divide (two ⋅! (m2 ⋅! e1)) m1, divide (m2 ⋅! d1) m1)
      unify pm2 (divide (two ⋅! (m2 ⋅! e2)) m1, divide (m2 ⋅! d2) m1)

      -- set correct types for sample results in the tail
      unify tm1 t1
      unify tm2 t2

      -- expression has type of the tail
      return ttail
    
checkPri' scope t = (throwError (UnsupportedTermError t))
