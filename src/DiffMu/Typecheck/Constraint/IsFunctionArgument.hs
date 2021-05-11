
module DiffMu.Typecheck.Constraint.IsFunctionArgument where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Typecheck.JuliaType

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
    -- if there are none such function (everything was annotated), we are done, and can discharge this constraint,
    -- and add the IsChoice constraint
    [] -> do
      dischargeConstraint name
      -- TODO: Activate this line!
      -- addConstraint (Solvable (IsChoice (wantedFunctions, H.fromList existingFunctions)))
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

