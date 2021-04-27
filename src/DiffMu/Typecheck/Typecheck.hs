
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Typecheck.Operations
import DiffMu.Core.Scope
import DiffMu.Typecheck.JuliaType

import qualified Data.HashMap.Strict as H

import Debug.Trace




------------------------------------------------------------------------
-- The typechecking function

--------------------
-- Sensitivity terms

checkSen' :: DMTerm -> DMScope -> TC DMType

checkPriv :: DMTerm -> DMScope -> TC DMType
checkPriv t scope = do
   γ <- use types
   case γ of -- TODO prettify.
      Left (Ctx (MonCom c)) | H.null c -> return ()
      Right (Ctx (MonCom c)) | H.null c -> return ()
      _   -> throwError (ImpossibleError "Input context for checking must be empty.")
   types .= Right def -- cast to privacy context.

   res <- checkPri' t scope

   γ <- use types
   case γ of
      Right γ -> return res
      Left γ -> error $ "checkPriv returned a sensitivity context!\n" <> "It is:\n" <> show γ <> "\nThe input term was:\n" <> show t

checkSens :: DMTerm -> DMScope -> TC DMType
checkSens t scope = do
   γ <- use types
   case γ of -- TODO prettify.
      Left (Ctx (MonCom c)) | H.null c -> return ()
      Right (Ctx (MonCom c)) | H.null c -> return ()
      _   -> throwError (ImpossibleError "Input context for checking must be empty.")
   types .= Left def -- cast to sensitivity context.

   res <- checkSen' t scope

   γ <- use types
   case γ of
      Left γ -> return res
      Right γ -> error $ "checkSens returned a privacy context!\n" <> "It is:\n" <> show γ <> "\nThe input term was:\n" <> show t

-- TODO: Here we assume that η really has type τ, and do not check it. Should maybe do that.
checkSen' (Sng η τ) scope  = Numeric <$> (Const (constCoeff (Fin η)) <$> (createDMTypeNum τ))

-- a special term for function argument variables.
-- those get sensitivity 1, all other variables are var terms

-- TODO!!!! Get interestingness flag!
checkSen' (Arg x dτ i) scope = do τ <- createDMType dτ -- TODO subtype!
                                  setVarS x (Single i (τ :@ constCoeff (Fin 1)))
                                  return τ

checkSen' (Var x dτ) scope = do -- get the term that corresponds to this variable from the scope dict
                                (vt, scope') <- popDefinition scope x

                                -- check the term in the new, smaller scope'
                                τ <- checkSens vt scope'

                                case dτ of
                                  JTAny -> return τ
                                  dτ -> do
                                    -- if the user has given an annotation
                                    -- inferred type must be a subtype of the user annotation
                                    dτd <- createDMType dτ
                                    addConstraint (Solvable (IsLessEqual (τ, dτd) ))
                                    return τ

-- typechecking an op
checkSen' (Op op args) scope =
  -- We create a helper function, which infers the type of arg, unifies it with the given τ
  -- and scales the current context by s.
  let checkOpArg (arg,(τ,s)) = do
        τ_arg <- checkSens arg scope
        unify (Numeric τ) τ_arg
        mscale (svar s)
  in do
    -- We get create a new typeop constraint for op
    (res,arg_sens) <- makeTypeOp op (length args)

    -- We call our helper function `checkOpArg` on the argument-terms, zipped with the
    -- type(variables), sensitivities returned by `makeTypeOp`
    _ <- msumS ((checkOpArg <$> (zip args arg_sens)))

    -- We return the `res` type given by `makeTypeOp`
    return (Numeric res)


checkSen' (Phi cond ifbr elsebr) scope =
   let mcond = do
        τ_cond <- checkSens cond scope
        mscale inftyS
        return τ_cond
   in do
      τ_sum <- msumS [(checkSens ifbr scope), (checkSens elsebr scope), mcond]
      (τif, τelse) <- case τ_sum of
                           (τ1 : τ2 : _) -> return (τ1, τ2)
                           _ -> throwError (ImpossibleError "Sum cannot return empty.")
      τ <- newVar
      addConstraint (Solvable (IsSupremum (τ, τif, τelse)))
      return τ

checkSen' (Lam xτs body) scope = do

  -- put a special term to mark x as a function argument. those get special tratment
  -- because we're interested in their sensitivity
  let scope' = mconcat ((\(x :- τ) -> setValue x (Arg x τ IsInteresting)) <$> xτs) scope

  τr <- checkSens body scope'
  xrτs <- getArgList xτs
  return (xrτs :->: τr)


checkSen' (LamStar xτs body) scope = do

  -- put a special term to mark x as a function argument. those get special tratment
  -- because we're interested in their sensitivity
  let scope' = mconcat ((\((x :- τ), i) -> setValue x (Arg x τ i)) <$> xτs) scope

  τr <- checkPriv body scope'
  xrτs <- getArgList (map fst xτs)
  mtruncateS inftyS
  return (xrτs :->*: τr)


checkSen' (SLet (x :- dτ) term body) scope = do

  -- TODO this requires saving the annotation in the dict.
  case dτ of
     JTAny -> return dτ
     dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

  -- we're very lazy, only adding the new term for v to its scope entry
  scope' <- pushDefinition scope x term

  --check body, this will put the seinsitivity it has in the arguments in the monad context.
  τ <- checkSens body scope'
  return τ


checkSen' (Apply f args) scope = let
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
      addConstraint (Solvable (IsLessEqual (τ_lam, (argτs :->: τ_ret)))) -- f's type must be subtype of an arrow matching arg types.
      return τ_ret


checkSen' (FLet fname sign term body) scope = do

  -- make a Choice term to put in the scope
   scope' <- case (H.lookup fname scope) of
                  Nothing -> pushDefinition scope fname (Choice (H.singleton sign term))
                  Just (Choice d) -> do
                                        (_, scope'') <- popDefinition scope fname
                                        pushDefinition scope'' fname (Choice (H.insert sign term d))
                  _ -> throwError (ImpossibleError "Invalid scope entry.")

   -- check body with that new scope. Choice terms will result in IsChoice constraints upon ivocation of fname
   result <- checkSens body scope'
   _ <- removeVar @Sensitivity fname
   return result


checkSen' (Choice d) scope = let
      checkChoice :: DMTerm -> TC (DMType, Sensitivity)
      checkChoice t = do
         τ <- checkSens t scope
         flag <- newSVar "chflag"
         _ <- mscale (svar flag)
         return (τ, svar flag)
      in do

         dd <- mapM checkChoice d
         τ <- newVar
         addConstraint (Solvable (IsChoice (τ, dd)))
         return τ


checkSen' (Tup ts) scope = do
   τs <- msumS (map (\t -> (checkSens t scope)) ts)
   return (DMTup τs)

checkSen' (TLet xs tu body) scope = do
   --TODO chekc uniqueness
   maxs <- newVar

   let mtup = do -- checn and scale
          τ <- checkSens tu scope
          mscale maxs
          return τ

   let mbody = do
          let scope' = mconcat ((\(x :- dτ) -> setValue x (Arg x dτ IsInteresting)) <$> xs) scope -- TODO unique names
          let xnames = map fstA xs

          τb <- checkSens body scope'

          sτs <- mapM (removeVar @Sensitivity) xnames -- get inference result for xs

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

   let checkScale :: DMTerm -> TC (DMType, Sensitivity)
       checkScale term = do
          τ <- checkSens term scope
          s <- newVar
          mscale s
          return (τ, s)

   let mbody = do
         scope' <- pushDefinition scope xi (Arg xi JTNumInt NotInteresting)
         scope'' <- pushDefinition scope' xc (Arg xc JTAny IsInteresting)
         τ <- checkSens b scope
         xii <- removeVar @Sensitivity xi
         xci <- removeVar @Sensitivity xc
         s <- newVar
         mscale s
         return (τ, s, xii, xci)

   ((τit, sit), (τcs, scs), (τb, sb, (Single _ (τbit :@ sbit)), (Single _ (τbcs :@ sbcs)))) <- msum3Tup (checkScale niter, checkScale cs, mbody)

   addConstraint (Solvable (IsLessEqual (τit, τbit))) -- number of iterations must match typer equested by body
   addConstraint (Solvable (IsLessEqual (τcs, τbcs))) --  capture type must match type requested by body
   addConstraint (Solvable (IsLessEqual (τb, τbcs))) -- body output type must match body capture input type
   addConstraint (Solvable (IsLoopResult ((sit, scs, sb), sbcs, τit))) -- compute the right scalars once we know if τ_iter is const or not.

   return τb


checkSen' (Gauss rp εp δp f) scope = let
   setParam :: DMTerm -> TC Sensitivity
   setParam t = do -- parameters must be const numbers.
      τ <- checkSens t scope
      v <- newVar
      addConstraint (Solvable (IsLessEqual (τ, Numeric (Const v DMReal))))
      return v
   in do
      τf <- checkSens f scope
      (τs, senss, τfret) <- case τf of -- extract f's input types, sensitivities and return type.
                                 xss :->: τ -> return ((map fstAnn xss), (map sndAnn xss), τ)
                                 _ -> throwError (ImpossibleError "Gauss term must have Arr argument.")

      τgauss <- newVar
      addConstraint (Solvable (IsGaussResult (τgauss, τfret))) -- we decide later if its gauss or mgauss according to return type

      r <- setParam rp
      mapM (\s -> addConstraint (Solvable (IsLessEqual (s, r)))) senss -- all of f's sensitivities must be bounded by r

      ε <- setParam εp
      δ <- setParam δp

      return ((map (\t -> (t :@ (ε, δ))) τs) :->*: τgauss)


checkSen' (MCreate n m body) scope =
   let setDim :: DMTerm -> Sensitivity -> TC DMType
       setDim t s = do
          τ <- checkSens t scope -- check dimension term
          unify τ (Numeric (Const s DMInt)) -- dimension must be integral
          mscale zeroId
          return τ

       checkBody :: Sensitivity -> Sensitivity -> TC DMType
       checkBody nv mv = do
          τ <- checkSens body scope -- check body lambda

          mscale (nv ⋅! mv) -- scale with dimension penalty

          τbody <- case τ of -- extract body lambda return type
                        xss :->: τret -> return τret
                        _ -> throwError (ImpossibleError "MCreate term must have Arr argument.")

          -- body lambda input vars must be integer
          addConstraint (Solvable (IsLessEqual (τ, [((Numeric (NonConst DMInt)) :@ inftyS), ((Numeric (NonConst DMInt)) :@ inftyS)] :->: τbody)))

          return τbody
   in do
       -- variables for matrix dimension
       nv <- newVar
       mv <- newVar

       sum <- msumS [checkBody nv mv, setDim n nv, setDim m mv]

       τbody <- case sum of -- extract element type from constructing lambda
                  (τ : _) -> return τ
                  _ -> throwError (ImpossibleError "?!")

       nrm <- newVar -- variable for norm
       return (DMMat nrm U nv mv τbody)

checkSen' (ClipM c m) scope = do
   τb <- checkSens m scope -- check the matrix

   -- variables for norm and clip parameters and dimension
   nrm <- newVar
   clp <- newVar
   n <- newVar
   m <- newVar

   -- set correct matrix type
   unify τb (DMMat nrm clp n m (Numeric DMData))

   -- change clip parameter to input
   return (DMMat nrm c n m (Numeric DMData))

-- Everything else is currently not supported.
checkSen' t scope = throwError (UnsupportedTermError t)


--------------------------------------------------------------------------------
-- Privacy terms

checkPri' :: DMTerm -> DMScope -> TC DMType

checkPri' (Ret t) scope = do
   τ <- checkSens t scope
   mtruncateP inftyP
   return τ

checkPri' (SLet (x :- dτ) term body) scope =
  -- push x to scope, check body, and discard x from the result context.
  -- this is the bind rule; as we expect the body to be a privacy term we don't need to worry about x's sensitivity
  let mbody = do
         scope' <- pushDefinition scope x (Arg x dτ IsInteresting)
         τ <- checkPriv body scope'
         _ <- removeVar @Privacy x
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

checkPri' (FLet fname sign term body) scope = do -- this is the same as with checkSens

  -- make a Choice term to put in the scope
   scope' <- case (H.lookup fname scope) of
                  Nothing -> pushDefinition scope fname (Choice (H.singleton sign term))
                  Just (Choice d) -> do
                                        (_, scope'') <- popDefinition scope fname
                                        pushDefinition scope'' fname (Choice (H.insert sign term d))
                  _ -> throwError (ImpossibleError "Invalid scope entry.")

   -- check body with that new scope. Choice terms will result in IsChoice constraints upon ivocation of fname
   result <- checkPriv body scope'
   _ <- removeVar @Privacy fname
   return result


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


checkPri' (Apply f args) scope = let
   -- check a single argument, scale its context with the corresponding sensitivity variable
   checkFArg :: DMTerm -> Privacy -> TC DMType
   checkFArg arg p = do
      τ <- checkSens arg scope
      mtruncateP p
      return τ
   in do
      εvars :: [Sensitivity] <- mapM (\x -> newVar) args -- create privacy variables for all arguments
      δvars :: [Sensitivity] <- mapM (\x -> newVar) args
      let pvars = (inftyP :  (zip εvars δvars)) -- constext of f gets truncated to ∞
      let margs = zipWith checkFArg (f : args) pvars -- check f and args and scale with their respective pvar

      τ_sum <- msumP margs -- sum args and f's context
      (τ_lam, argτs) <- case τ_sum of
                             (τ : τs) -> return (τ, (zipWith (:@) τs pvars))
                             [] -> throwError (ImpossibleError "Sum cannot return empty list.")

      τ_ret <- newVar -- a type var for the function return type
      addConstraint (Solvable (IsLessEqual (τ_lam, (argτs :->*: τ_ret)))) -- f's type must be subtype of an arrow* matching arg types.
      return τ_ret

checkPri' (Loop it cs (xi, xc) b) scope = do
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

          mapM (\(x, τ) -> setVarP x (Single IsInteresting (τ :@ newp))) (zip xs τs)
          return ()

   let mbody = do
         scope' <- pushDefinition scope xi (Arg xi JTNumInt NotInteresting)
         scope'' <- pushDefinition scope' xc (Arg xc JTAny IsInteresting)
         τ <- checkSens b scope
         _ <- removeVar @Sensitivity xi -- TODO do something?
         _ <- removeVar @Sensitivity xc

         interesting <- getInteresting
         mtruncateP inftyP

         n <- newVar
         setInteresting interesting n
         return (τ, n)

   (τit, τcs, (τb, n)) <- msum3Tup (miter, mcaps, mbody)

   unify τit (Numeric (Const n DMInt)) -- number of iterations must be constant integer

   addConstraint (Solvable (IsLessEqual (τb, τcs))) -- body output type must match body capture input type

   return τb


checkPri' t scope = checkPriv (Ret t) scope -- secretly return if the term has the wrong color.


