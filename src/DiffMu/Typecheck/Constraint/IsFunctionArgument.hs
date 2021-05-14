
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

import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as H
import Data.HashMap.Strict (HashMap)
import qualified Data.POSet as PO
import Data.POSet (POSet)

import Debug.Trace
import qualified Data.HashMap.Strict as H

---------------------------------------------------------------------
-- "Strict subtyping" of function calls

solveIsFunctionArgument :: IsT MonadDMTC t => Symbol -> (DMTypeOf (AnnKind AnnS), DMTypeOf (AnnKind AnnS)) -> t ()

-- if the given argument is a non-function, and we also expect a non-function, we unify their types and sensitities
solveIsFunctionArgument name (NoFun (a1 :@ RealS η1), NoFun (a2 :@ RealS η2)) = do
  a1 ==! a2
  η1 ==! η2
  dischargeConstraint name

-- if the given argument and expected argument are both functions / collections of functions
solveIsFunctionArgument name (Fun xs, Fun ys) = do
  let wantedFunctions :: [DMFun :& Sensitivity]
      wantedFunctions = [f :@ a | (f :@ (_ , a)) <- ys]
  let existingFunctions :: [([JuliaType], (DMFun :& Sensitivity, Sensitivity))]
      existingFunctions = [(jts , ((f :@ a), zeroId)) | (f :@ (Just jts , a)) <- xs]

  -- We check if there were any functions in xs (those which are given by a dict), which did not have a
  -- julia type annotation
  let existingFunctionsWithoutJuliaType :: [DMFun]
      existingFunctionsWithoutJuliaType = [f | (f :@ (Nothing , _)) <- xs]

  case existingFunctionsWithoutJuliaType of
    -- if there are none such function (everything was annotated), we can attempt to solve the IsChoice constraint
    [] -> do
      dischargeConstraint name
      addConstraint (Solvable (IsChoice (H.fromList existingFunctions, wantedFunctions)))
      return ()

    -- if there were functions without annotation, error out
    xs -> internalError $ "Encountered functions without a required julia type annotation as the argument to a function:\n" <> show xs

solveIsFunctionArgument name (TVar a, Fun xs) = addSub (a := Fun xs) >> dischargeConstraint name >> pure ()

-- TODO: Check whether in the case where at least one argument is known to be no fun, we can make the other one as well
--       or rather: would this be neccessary to get good results?
solveIsFunctionArgument name (NoFun (a :@ η), _) = return ()-- addSub (b := NoFun (a :@ η))
solveIsFunctionArgument name (_, NoFun (a :@ η)) = return ()-- addSub (b := NoFun (a :@ η))

-- if both sides are variables, or are {trunc,↷,∧} terms of variables
-- then we cannot do anything yet, since we do not know whether we have function terms inside, or not.
solveIsFunctionArgument name (_, _) = return ()

instance Solve MonadDMTC IsFunctionArgument (DMTypeOf (AnnKind AnnS), DMTypeOf (AnnKind AnnS)) where
  solve_ Dict _ name (IsFunctionArgument (a,b)) = solveIsFunctionArgument name (a,b)

instance Solve MonadDMTC IsFunctionArgument (DMTypeOf (AnnKind AnnP), DMTypeOf (AnnKind AnnP)) where
  solve_ Dict _ name (IsFunctionArgument (a,b)) = undefined -- TODO

------------------------------------------------------------------------------------------------------
-- IsChoice constraints
-- these are created from IsFunctionArgument constraints if both sides are actually functions.

type ChoiceHash = HashMap [JuliaType] ((DMFun :& Sensitivity), Sensitivity)

-- hash has the existing methods, list has the required methods.
instance Solve MonadDMTC IsChoice (ChoiceHash, [DMFun :& Sensitivity]) where
  solve_ Dict _ name (IsChoice arg) = solveIsChoice name arg

solveIsChoice :: forall t. IsT MonadDMTC t => Symbol -> (ChoiceHash, [DMFun :& Sensitivity]) -> t ()
solveIsChoice name (provided, required) = do
   -- remove all choices from the "required" list that have a unique match in the "provided" hashmap.
   -- when a choice is resolved, the corresponding counter in the hashmap is incremented by one.
   let matchArgs ::  ChoiceHash -> [DMFun :& Sensitivity] -> t (ChoiceHash, [DMFun :& Sensitivity])
       matchArgs curProv curReq = do
          case curReq of
             [] -> return (curProv, [])
             (τs : restReq) -> do -- go through all required methods
                 case fstAnn τs of
                      TVar _ -> do -- it was a tvar
                                   (resP, resR) <- (matchArgs curProv restReq) -- can't resolve TVar choice, keep it and recurse.
                                   return (resP, (τs : resR))
                      τsτ -> do
                              -- get methods that could be a match, and free TVars in the args while we're at it
                              (candidates, hasFreeVars) <- case τsτ of
                                  args :->: _  -> do
                                                    -- remove all methods that definitely don't match this signature
                                                    let cand = (H.filterWithKey (\s c -> choiceCouldMatch args s) provided)
                                                    -- filter all argument types that would be "Function" in julia...
                                                    let argsNoFun = filter (\τa -> case τa of {Fun _ -> False; _ -> True}) args
                                                    -- ... and get the free typevars of the rest.
                                                    let free = and (null . freeVars @_ @TVarOf <$> argsNoFun)
                                                    return (cand, free)
                                  args :->*: _ -> do -- same as for the above case.
                                                    let cand = (H.filterWithKey (\s c -> choiceCouldMatch args s) provided)
                                                    let argsNoJFun = filter noJuliaFunction args
                                                    let free = and (null . freeVars @_ @TVarOf <$> argsNoJFun)
                                                    return (cand, free)
                                  _ -> throwError (ImpossibleError ("Invalid type for Choice: " <> show τsτ))

                              if H.null candidates
                                 then throwError (NoChoiceFoundError $ "No matching choice for " <> show τs <> " found in " <> show provided)
                                 else pure Nothing

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

                              case length candidates' == length provided of
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
                                       [(sign, ((cτ :@ cs), count))] -> do
                                                                let (τ :@ s) = τs
                                                                generateApplyConstraints cτ τ
                                                                let resP = H.insert sign ((cτ :@ cs), count +! s) curProv -- count up
                                                                matchArgs resP restReq -- discard entry by recursing without τs

                                       _ -> do -- more than one left, need to wait.
                                               (resP, resR) <- (matchArgs curProv restReq) -- can't resolve choice, keep it and recurse.
                                               return (resP, (τs : resR))


   (newdict, newcs) <- matchArgs provided required -- get new dict and list of yet unresolved choices.

   -- discard or update constraint.
   case newcs of
        [] -> do -- complete resolution! set counters, discard.
                mapM (\((_ :@ flag), count) -> flag ==! count) newdict
                dischargeConstraint name
        cs | (length required > length newcs) -> do
                traceM $ "got rid of some choices:" <> show required <> " became " <> show newcs
                -- still not all choices resolved, just kick the resolved ones out of the constraint.
                -- the sensitivity of the kicked out ones is already included in their method's count in newdict.
                updateConstraint name (Solvable (IsChoice (newdict, newcs)))
        _ -> return ()

   return ()

-- remove dict entries whose signature is supertype of some other signature.
-- this is only reasonable if the dmtype signature we're trying to match has no free variables,
-- bc then the minimal matching method is picked.
keepLeastGeneral :: ChoiceHash -> ChoiceHash
keepLeastGeneral cs =
  -- make a poset from the (julia-)subtype relations of the given signatures
  let pos :: POSet [JuliaType]
      pos = PO.fromList (HS.toList (H.keysSet cs))
      -- pick the ones that are not supertypes of any of the others
      mins = PO.lookupMin pos
      mins' = [(k, cs H.! k) | k <- mins]
  in H.fromList mins'

-- determine whether a function with the given dmtype signature could match a method with the given juliatype signature.
choiceCouldMatch :: forall e. (DMExtra e) => [DMTypeOf (AnnKind e)] -> [JuliaType] -> Bool
choiceCouldMatch args cs =
   case length args == length cs of
        False -> False
        True -> let couldMatch t c = or ((`leq` c) <$> juliatypes t)
                in (and (zipWith couldMatch args cs))


-- return False if this type would become a "Function" if converted to a julia type
noJuliaFunction :: forall e. (DMExtra e) => DMTypeOf (AnnKind e) -> Bool
noJuliaFunction τ = (juliatypes τ == [JuliaType "Function"])

-- when a method is matched to it's call, we need to generate new IsFunctionArgument constraints for args and ret type.
generateApplyConstraints :: forall t. IsT MonadDMTC t => DMFun -> DMFun -> t ()
generateApplyConstraints method applicand = do
   -- 'method' is the function that is called in the julia runtime where 'applicand' came out of typechecking Apply term.
   -- they hence have to be the same type, except when one of their arguments is itself a function, in which case we need to
   -- get a new IsChoice constraint. we hence add IsFunctionArgument constraints, which will be resolved just like so.
   let addC :: (DMTypeOf (AnnKind AnnS), DMTypeOf (AnnKind AnnS)) -> t Symbol
       addC (a, b) = addConstraint (Solvable (IsFunctionArgument (a,b)))
   case (applicand, method) of
      (aargs :->: aret, margs :->: mret)   -> do
         -- margs are the types inferred when checking the method (FLet).
         -- aargs are the types of the arguments that were passed in Apply.
         -- a Fun type in margs hence encodes the methods the input function is required to have
         -- a Fun type in aargs encodes the methods the passed function actually has.
         -- so aargs goes first in the constraint.
         mapM addC (zip aargs margs)
         -- with return types it's the other way around: mret is the inferred return type of the method,
         -- so it encodes all method that returned function has. aret is actually just a tvar created when checking Apply
         addC (mret, aret)
         return ()
--      (aargs :->*: aret, margs :->*: mret)   -> do -- TODO IsFunctionArgument does not work for privacies
--         mapM addC (zip margs aargs)
--         addC (mret, aret)
--         return ()
      _ -> throwError (ImpossibleError ("Invalid type for Choice: " <> show (applicand, method)))
