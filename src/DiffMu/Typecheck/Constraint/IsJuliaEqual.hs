

module DiffMu.Typecheck.Constraint.IsJuliaEqual where

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


-----------------------------------------------------------------
-- Fake julia types
--
-- We do not have a real "julia type layer" for now. Since our types
-- mostly only differ from the julia types by having the singleton const types,
-- we have a constraint which checks this by unifying after making variables non-const
-- if possible.


-- defining the constraint
newtype IsJuliaEqual a = IsJuliaEqual a deriving Show

instance TCConstraint IsJuliaEqual where
  constr = IsJuliaEqual
  runConstr (IsJuliaEqual c) = c


makeNonConst_JuliaVersion ::  DMTypeOf k -> DMTypeOf k
makeNonConst_JuliaVersion (TVar a) = TVar a
makeNonConst_JuliaVersion (Const _ a) = NonConst a
makeNonConst_JuliaVersion (NonConst a) = NonConst a
makeNonConst_JuliaVersion (NoFun a) = NoFun (makeNonConst_JuliaVersion a)
makeNonConst_JuliaVersion (DMTup as) = DMTup (makeNonConst_JuliaVersion <$> as)
makeNonConst_JuliaVersion (Numeric a) = Numeric (makeNonConst_JuliaVersion a)
-- everything else is not changed
makeNonConst_JuliaVersion x = x

solveJuliaEqual :: (IsT MonadDMTC t) => Symbol -> DMMain -> DMMain -> t ()
solveJuliaEqual name (NoFun a) (NoFun b) = do
  -- we compute the free variables in the type which are of NumKind
  -- these are the once which block this constraint, since they have
  -- to be resolved to Const/NonConst, before we can apply the `makeNonConst_JuliaVersion`
  -- on `a` and `b`
  let freev = freeVars a <> freeVars b
      freev' = filterSomeK @TVarOf @NumKind freev

  case freev' of
    [] -> do let a' = makeNonConst_JuliaVersion a
                 b' = makeNonConst_JuliaVersion b
             unify a' b'
             dischargeConstraint name
    _ -> return()

solveJuliaEqual name _ _ = failConstraint name



-- solving it
instance Solve MonadDMTC IsJuliaEqual (DMMain, DMMain) where
  solve_ Dict _ name (IsJuliaEqual (a,b)) = solveJuliaEqual name a b

instance FixedVars TVarOf (IsJuliaEqual (DMMain, DMMain)) where
  fixedVars _ = mempty


