

module DiffMu.Typecheck.Constraint.IsJuliaEqual where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Unification

import Debug.Trace

import Prelude as P


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
  let freev = freeVars @_ @TVarOf a <> freeVars b
      freev0 = (filterSomeK @TVarOf @BaseNumKind freev)
      freev1 = filterSomeK @TVarOf @NormKind freev
      freev2 = filterSomeK @TVarOf @ClipKind freev

      -- compare the length of `m` and `n`, that is, if all free variables
      -- have the aforementioned kinds
      m = length freev
      n = length freev0 P.+ length freev1 P.+ length freev2

  case (m == n) of
    True -> do let a' = makeNonConst_JuliaVersion a
                   b' = makeNonConst_JuliaVersion b
               unify a' b'
               dischargeConstraint name
    False -> return()

solveJuliaEqual name (TVar _) _   = return ()
solveJuliaEqual name (_) (TVar _) = return ()
solveJuliaEqual name _ _ = failConstraint name



-- solving it
instance Solve MonadDMTC IsJuliaEqual (DMMain, DMMain) where
  solve_ Dict _ name (IsJuliaEqual (a,b)) = solveJuliaEqual name a b

instance FixedVars TVarOf (IsJuliaEqual (DMMain, DMMain)) where
  fixedVars _ = mempty


-------------------------------------------------------------------
-- set the a type to non-const, in case it's numeric or a tuple.
--

newtype IsNonConst a = IsNonConst a deriving Show

instance TCConstraint IsNonConst where
  constr = IsNonConst
  runConstr (IsNonConst c) = c

instance Typeable k => FixedVars TVarOf (IsNonConst (DMTypeOf k, DMTypeOf k)) where
  fixedVars (IsNonConst _) = []

instance Typeable k => Solve MonadDMTC IsNonConst (DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ name (IsNonConst (τ, τ_nonconst)) = do
     let freev = freeVars @_ @TVarOf τ
         freev' = filterSomeK @TVarOf @BaseNumKind freev

     case (length freev == length freev') of
       True -> do let a = makeNonConst_JuliaVersion τ
                  unify τ_nonconst a
                  dischargeConstraint name
       False -> return ()


