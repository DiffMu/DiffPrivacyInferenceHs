
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Typecheck.Operations

import Data.HashMap.Strict as H

import Debug.Trace




------------------------------------------------------------------------
-- The typechecking function

--------------------
-- Sensitivity terms

checkSens :: DMTerm -> DMScope -> STC DMType

-- TODO: Here we assume that η really has type τ, and do not check it. Should maybe do that.
checkSens (Sng η τ) scope  = pure $ Numeric (Const (constCoeff (Fin η)) (createDMTypeNum τ))

-- a special term for function argument variables.
-- those get sensitivity 1, all other variables are var terms
checkSens (Arg x dτ) scope = do τ <- createDMType dτ
                                setVar x (τ :@ constCoeff (Fin 1))
                                return τ

checkSens (Var x dτ) scope = do -- get the term that corresponds to this variable from the scope dict
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
checkSens (Op op args) scope =
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
    _ <- msum ((checkOpArg <$> (zip args arg_sens)))

    -- We return the `res` type given by `makeTypeOp`
    return (Numeric res)

checkSens (Lam (Lam_ xτs body)) scope = do

  -- put a special term to mark x as a function argument. those get special tratment
  -- because we're interested in their sensitivity
  let scope' = mconcat ((\(x :- τ) -> setValue x [(Arg x τ)]) <$> xτs) scope

  τr <- checkSens body scope
  xrτs <- getArgList xτs
  return (xrτs :->: τr)

checkSens (SLet (x :- dτ) term body) scope = do

  -- TODO this requires saving the annotation in the dict.
  case dτ of
     JTAny -> return dτ
     dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

  -- we're very lazy, only adding the new term for v to its scope entry
  scope' <- pushDefinition scope x term

  --check body, this will put the seinsitivity it has in the arguments in the monad context.
  τ <- checkSens body scope'
  return τ

checkSens (FLet fname sign term body) scope = do

  -- make a Choice term to put in the scope
   scope' <- case (H.lookup fname scope) of
                  Nothing -> pushDefinition scope fname (Choice (H.singleton sign term))
                  Just [Choice d] -> do
                                        (_, scope'') <- popDefinition scope fname
                                        pushDefinition scope'' fname (Choice (H.insert sign term d))
                  _ -> throwError (ImpossibleError "Invalid scope entry.")


   result <- checkSens body scope'
   _ <- removeVar fname
   return result


checkSens (Choice d) scope = let
      checkChoice :: DMTerm -> STC DMType
      checkChoice t = do
         τ <- checkSens t scope
         flag <- newSVar "ch"
         _ <- mscale (svar flag)
         return τ
      in do

         dd <- mapM checkChoice d
         τ <- newVar
         addConstraint (Solvable (IsChoice (τ, dd)))
         return τ


-- Everything else is currently not supported.
checkSens t scope = throwError (UnsupportedTermError t)


--------------------
-- Privacy terms

checkPriv :: DMTerm -> DMScope -> PTC DMType

checkPriv (Ret t) scope = do
   throwError (ImpossibleError "?!")
--   τ <- checkSens t scope
--   _ <- truncate(∞)
--   return τ -- TODO truncate to inf

checkPriv (SLet (x :- dτ) term body) scope =
  -- push x to scope, check body, and discard x from the result context.
  -- this is the bind rule; as we expect the body to be a privacy term we don't need to worry about x's sensitivity
  let mbody = do
         scope' <- pushDefinition scope x (Arg x dτ)
         τ <- checkPriv body scope'
         _ <- removeVar x
         return τ
  in do
     -- TODO this requires saving the annotation in the dict.
     case dτ of
          JTAny -> return dτ
          dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

     sum <- msum [mbody, (checkPriv term scope)]
     res <- case sum of
                    [τ::DMType,_] -> return τ
                    _ -> throwError (ImpossibleError "?!")

     return res

checkPriv t scope = checkPriv (Ret t) scope


-------------------------------------------------------------
-- Definition of the scope

-- A scope with variables of type `v`, and contents of type `a` is simply a hashmap.
type Scope v a = HashMap v [a]

-- The default scope is an empty scope.
instance Default (Scope v a) where
  def = H.empty

-- Given a scope and a variable name v, we pop the topmost element from the list for v.
popDefinition :: (MonadDMTC e t, DictKey v, Show v) => Scope v a -> v -> t e (a, Scope v a)
popDefinition scope v =
  do (d,ds) <- case H.lookup v scope of
                 Just (x:xs) -> return (x,xs)
                 _           -> throwError (VariableNotInScope v)
     return (d, H.insert v ds scope)

-- Given a scope, a variable name v , and a DMTerm t, we push t to the list for v.
pushDefinition :: (MonadDMTC e t, DictKey v, Show v) => Scope v a -> v -> a -> t e (Scope v a)
pushDefinition scope v term =
   do (ds) <- case H.lookup v scope of
                  Just [xs] -> return (term:[xs])
                  _         -> return [term]
      return (H.insert v ds scope)


-- Our scopes have symbols as variables, and contain DMTerms.
type DMScope = Scope Symbol DMTerm

-- All hashmaps are `DictLike`
instance (DictKey k) => DictLike k v (HashMap k v) where
  setValue v m (h) = (H.insert v m h)
  deleteValue v (h) = (H.delete v h)
  getValue k (h) = h H.!? k





