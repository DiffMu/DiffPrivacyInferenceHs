
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Typecheck.Operations
import DiffMu.Core.Scope

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
checkSen' (Arg x dτ) scope = do τ <- createDMType dτ
                                setVar x (τ :@ constCoeff (Fin 1))
                                return τ

checkSen' (Var x dτ) scope = do -- get the term that corresponds to this variable from the scope dict
                                (vt, scope') <- popDefinition scope x

                                -- check the term in the new, smaller scope'
                                τ <- checkSens vt scope'

                                case dτ of
                                  JTAny _ -> return τ
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
  let scope' = mconcat ((\(x :- τ) -> setValue x (Arg x τ)) <$> xτs) scope

  τr <- checkSens body scope'
  xrτs <- getArgList xτs
  return (xrτs :->: τr)


checkSen' (LamStar xτs body) scope = do

  -- put a special term to mark x as a function argument. those get special tratment
  -- because we're interested in their sensitivity
  let scope' = mconcat ((\(x :- τ) -> setValue x (Arg x τ)) <$> xτs) scope

  τr <- checkPriv body scope'
  xrτs <- getArgList xτs
  mtruncateS inftyS
  return (xrτs :->*: τr)


checkSen' (SLet (x :- dτ) term body) scope = do

  -- TODO this requires saving the annotation in the dict.
  case dτ of
     JTAny _ -> return dτ
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
      checkChoice :: DMTerm -> TC DMType
      checkChoice t = do
         τ <- checkSens t scope
         flag <- newSVar "chflag"
         _ <- mscale (svar flag)
         return τ
      in do

         dd <- mapM checkChoice d
         τ <- newVar
         addConstraint (Solvable (IsChoice (τ, dd)))
         return τ


checkSen' (Tup ts) scope = do
   τs <- msumS (DiffMu.Prelude.map (\t -> (checkSens t scope)) ts)
   return (DMTup τs)


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
         scope' <- pushDefinition scope x (Arg x dτ)
         τ <- checkPriv body scope'
         _ <- removeVar @Privacy x
         return τ
  in do
     -- TODO this requires saving the annotation in the dict.
     case dτ of
          JTAny _ -> return dτ
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

checkPri' t scope = checkPriv (Ret t) scope -- secretly return if the term has the wrong color.


