
module DiffMu.Typecheck.Constraint.IsFunctionArgument where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Typecheck.JuliaType
--import DiffMu.Typecheck.Subtyping
import Algebra.PartialOrd

import Debug.Trace

import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as H
import Data.HashMap.Strict (HashMap)
import qualified Data.POSet as PO
import Data.POSet (POSet)

import Debug.Trace
import qualified Data.HashMap.Strict as H

  {-

---------------------------------------------------------------------
-- "Strict subtyping" of function calls
{-
-- if one side of the IsFunctionArgument constraint is NoFun, the other has to be NoFun as well.
-- this can be carried on into operations on annotated types.
-- this function creates all the constraints/substitutions to enforce the input type is NoFun
forceNoFun :: forall t a.(IsT MonadDMTC t, DMExtra a) => DMTypeOf MainKind -> t (DMTypeOf MainKind)
forceNoFun (TVar x) = do
  v <- newVar
  unify (TVar x) (NoFun v) -- the tvar is NoFun
-- these cases just recurse
forceNoFun (NoFun x) = pure $ NoFun x
forceNoFun (x :∧: y) = do
  xx <- forceNoFun x
  yy <- forceNoFun y
  return (xx :∧: yy)
-- these cases are forbidden, they cannot be NoFun
forceNoFun (Fun _) = error "Mismatch!"


-- if the given argument is a non-function, and we also expect a non-function, we just unify their types
solveIsFunctionArgument name (NoFun a1, NoFun a2) = do
  a1 ==! a2
  dischargeConstraint name

-- if we expect a non-function, the given argument must be a non-function.
solveIsFunctionArgument name (NoFun a1, b) = do
  nfb <- forceNoFun b
  return ()

-- if the given argument is a non-function, we must expect some non-function type.
solveIsFunctionArgument name (b, NoFun a1) = do
  nfb <- forceNoFun b
  return ()
-}

solveIsFunctionArgument :: IsT MonadDMTC t => Symbol -> (DMTypeOf MainKind, DMTypeOf MainKind) -> t ()

-- if the given argument and expected argument are both functions / collections of functions
solveIsFunctionArgument name (Fun xs, Fun ys) = do
  let wantedFunctions :: [DMTypeOf FunKind]
      wantedFunctions = [f | ((ForAll _ f) :@ _) <- ys]  -- TODO check if ForAll is empty and signature is Nothing
  let existingFunctions :: [([JuliaType], (DMTypeOf ForAllKind, [DMTypeOf FunKind]))]
      existingFunctions = [(jts , (f, [])) | (f :@ Just jts) <- xs]

  -- We check if there were any functions in xs (those which are given by a dict), which did not have a
  -- julia type annotation
  let existingFunctionsWithoutJuliaType :: [DMTypeOf ForAllKind]
      existingFunctionsWithoutJuliaType = [f | (f :@ Nothing) <- xs]

  case existingFunctionsWithoutJuliaType of
    -- if there are none such function (everything was annotated), we can attempt to solve the IsChoice constraint
    [] -> do
      dischargeConstraint name
      addConstraint (Solvable (IsChoice (H.fromList existingFunctions, wantedFunctions)))
      return ()

    -- if there were functions without annotation, error out
    xs -> internalError $ "Encountered functions without a required julia type annotation as the argument to a function:\n" <> show xs

solveIsFunctionArgument name (TVar a, Fun xs) = addSub (a := Fun xs) >> dischargeConstraint name >> pure ()


-- if both sides are variables or ∧ terms of variables
-- then we cannot do anything yet, since we do not know whether we have function terms inside, or not.
solveIsFunctionArgument name (_, _) = return ()

instance Solve MonadDMTC IsFunctionArgument (DMTypeOf MainKind, DMTypeOf MainKind) where
  solve_ Dict _ name (IsFunctionArgument (a,b)) = solveIsFunctionArgument name (a,b)

------------------------------------------------------------------------------------------------------
-- IsChoice constraints
-- these are created from IsFunctionArgument constraints if both sides are actually functions.

-- map Julia signature to method and the list of function calls that went to this method.
type ChoiceHash = HashMap [JuliaType] (DMTypeOf ForAllKind, [DMTypeOf FunKind])

-- hash has the existing methods, list has the required methods.
instance Solve MonadDMTC IsChoice (ChoiceHash, [DMTypeOf FunKind]) where
  solve_ Dict _ name (IsChoice arg) = solveIsChoice name arg

-- see if the constraint can be resolved. might update the IsCHoice constraint, do nothing, or discharge.
-- might produce new IsFunctionArgument constraints for the arguments.
solveIsChoice :: forall t. IsT MonadDMTC t => Symbol -> (ChoiceHash, [DMTypeOf FunKind]) -> t ()
solveIsChoice name (provided, required) = do
   -- remove all choices from the "required" list that have a unique match in the "provided" hashmap.
   -- when a choice is resolved, the corresponding counter in the hashmap is incremented by one.
   let matchArgs ::  ChoiceHash -> [DMTypeOf FunKind] -> t (ChoiceHash, [DMTypeOf FunKind])
       matchArgs curProv curReq = do
          case curReq of
             [] -> return (curProv, [])
             (τs : restReq) -> do -- go through all required methods
                 case τs of
                      TVar _ -> do -- it was a tvar
                              (resP, resR) <- (matchArgs curProv restReq) -- can't resolve TVar choice, keep it and recurse.
                              return (resP, (τs : resR))
                      _ -> do
                         -- get methods that could be a match, and free TVars in the args while we're at it
                         (candidates, hasFreeVars) <- getMatchCandidates τs curProv

                         -- if there is no free tyepevars in τs arguments, throw out methods that are more general than others
                         -- if we don't know all types we cannot do this, as eg for two methods
                         -- (Int, Int) => T
                         -- (Real, Number) => T
                         -- and arg types (TVar, DMInt), both methods are in newchoices, but if we later realize the TVar
                         -- is a DMReal, the first one does not match even though it's less general.
                         -- filter Fun arguments, as the all have the same type "Function" in julia/
                         let candidates' = case hasFreeVars of
                               -- if no tvars are in the args
                               True  -> keepLeastGeneral candidates
                               -- else we do not change them
                               False -> candidates

                         case and ((length candidates' == length curProv),(length candidates' > 1)) of
                            -- no choices were discarded, the constraint could not be simplified.
                            True -> do
                                       (resP, resR) <- (matchArgs curProv restReq) -- can't resolve choice, keep it and recurse.
                                       return (resP, (τs : resR))

                            -- some choices were discarded, so we can continue
                            False -> do
                               case H.toList candidates' of
                                   -- only one left, we can pick that one yay
                                   -- even if there is free TVars, we don't have to add subtype constraints for the user-given signature,
                                   -- as it was encoded in the Arr type of the choice, so its arg types can only be refinements.
                                  [(sign, (cτ, matches))] -> do
                                     -- append the match to the list of calls that matched this method.
                                     let resP = H.insert sign (cτ, (τs : matches)) curProv -- append match to match list
                                     res <- matchArgs resP restReq -- discard entry by recursing without τs
                                     return res

                                  _ -> do -- more than one left, need to wait.
                                     (resP, resR) <- (matchArgs curProv restReq) -- can't resolve choice, keep it and recurse.
                                     return (resP, (τs : resR))


   (newdict, newcs) <- matchArgs provided required -- get new dict and list of yet unresolved choices.

   -- discard or update constraint.
   case newcs of
        [] -> do -- complete resolution! set counters, discard.
                mapM resolveChoiceHash newdict
                dischargeConstraint name
        cs | (length required > length newcs) -> do
                -- still not all choices resolved, just kick the resolved ones out of the constraint.
                -- the kicked out ones are already included in their method's list in newdict.
                updateConstraint name (Solvable (IsChoice (newdict, newcs)))
        _ -> do
                return ()

   return ()




resolveChoiceHash :: forall t. IsT MonadDMTC t => (DMTypeOf ForAllKind, [DMTypeOf FunKind]) -> t ()
resolveChoiceHash ((ForAll freevs method), matches) = do
   -- before resolving, we create copies of the method's type where all free type variables
   -- are replaced by fresh type variables, so we can safely unify with the type of the matched function.
   let nvs :: forall k. IsKind k => t [DMTypeOf k]
       -- a fresh tvar for each method
       nvs = mapM (fmap TVar . newTVar) ["free" | _ <- matches]
   -- a multi-substitution for a variable
   let big_asub (SomeK a) = (\x -> SomeK (a := ListK x)) <$> nvs
   -- multisubstitutions for all free variables of the method
   subs <- mapM big_asub freevs
   -- a duplicate of method for each matches, with our fresh TVars
   duplicates' <- duplicateTerm subs method
   case duplicates' of
      Nothing -> do -- there are no free type variables in method.
         -- unify each match with the method
         mapM (\match -> unify match method) matches
         return ()
      Just duplicates -> do
         -- duplicate the constraints that have the free vars, as well
         duplicateAllConstraints subs
         -- unify all matches with their corresponding duplicate.
         zipWithM unify matches duplicates
         return ()

resolveChoiceHash (_, matches) = impossible "invalid type for method"


-- remove dict entries whose signature is supertype of some other signature.
-- this is only reasonable if the dmtype signature we're trying to match has no free variables,
-- bc then the minimal matching method is picked.
keepLeastGeneral :: ChoiceHash -> ChoiceHash
keepLeastGeneral cs =
  -- make a poset from the (julia-)subtype relations of the given signatures
  -- convert to JuliaSignature so we use our custom `leq`
  let pos :: POSet JuliaSignature
      pos = PO.fromList (map JuliaSignature (HS.toList (H.keysSet cs)))
      -- pick the ones that are not supertypes of any of the others
      mins = PO.lookupMin pos
      mins' = [(k, cs H.! k) | JuliaSignature k <- mins]
  in
      H.fromList mins'

-- kick out all methods in provided that would not match τsτ.
getMatchCandidates :: forall t. IsT MonadDMTC t => DMTypeOf FunKind -> ChoiceHash -> t (ChoiceHash, Bool)
getMatchCandidates τsτ provided = do
   (candidates, hasFreeVars) <- case τsτ of
      (args :->: _)  -> do
                        -- remove all methods that definitely don't match this signature
                        let cand = (H.filterWithKey (\s c -> choiceCouldMatch (fstAnn <$> args) s) provided)
                        -- filter all argument types that would be "Function" in julia...
                        let argsNoJFun = [(τa, ann) | (τa :@ ann) <- args, noJuliaFunction τa]
                        -- ... and get the free typevars of the rest.
                        let free = and (null . freeVars @_ @TVarOf <$> argsNoJFun)
                        return (cand, free)
      (args :->*: _) -> do -- same as for the above case.
                        let cand = (H.filterWithKey (\s c -> choiceCouldMatch (fstAnn <$> args) s) provided)
                        let argsNoJFun = [(τa, ann) | (τa :@ ann) <- args, noJuliaFunction τa]
                        let free = and (null . freeVars @_ @TVarOf <$> argsNoJFun)
                        return (cand, free)
      _ -> throwError (ImpossibleError ("Invalid type for Choice: " <> show τsτ))

   if H.null candidates
      then throwError (NoChoiceFoundError $ "No matching choice for " <> show τsτ <> " found in " <> show provided)
      else return (candidates, hasFreeVars)




-- determine whether a function with the given dmtype signature could match a method with the given juliatype signature.
choiceCouldMatch :: [DMTypeOf MainKind] -> [JuliaType] -> Bool
choiceCouldMatch args cs =
   case length args == length cs of
        False -> False
        True -> let couldMatch t c = or ((`leq` c) <$> juliatypes t)
                in (and (zipWith couldMatch args cs))


-- return False if this type would become a "Function" if converted to a julia type
noJuliaFunction :: DMTypeOf MainKind -> Bool
noJuliaFunction τ = (juliatypes τ == [JuliaType "Function"])
-}
