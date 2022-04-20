
module DiffMu.Typecheck.Constraint.Definitions where

import DiffMu.Prelude
import DiffMu.Abstract.Data.Error
import DiffMu.Abstract.Class.IsT
import DiffMu.Abstract.Class.Constraint
--import DiffMu.Core.Definitions
--import DiffMu.Core.Context
--import DiffMu.Core.TC
--import DiffMu.Core.Unification
--import DiffMu.Typecheck.Subtyping

import Debug.Trace
import Data.HashMap.Strict (HashMap)

--import Prelude as P


--------------------------------------------------------------------------
-- Constraints
--
-- Constraints are axiomatized as wrappers around their content. Every kind
-- of constraint *is* its own wrapper type, that is, we have:
--
-- IsEqual :: Type -> Type
-- IsLessEqual :: Type -> Type
-- IsTypeOpResult :: Type -> Type
-- ...
--
-- And usually these wrappers have constructors of the same name as their type,
-- i.e., we have, forall a:
--
--  Term constructor
--   |               Type constructor
--   |                |
--   v                v
-- IsEqual :: a -> IsEqual a
-- IsLessEqual :: a -> IsLessEqual a
-- IsTypeOpResult :: a -> IsTypeOpResult a
-- ...
--
-- For example, we have:
newtype IsTypeOpResult a = IsTypeOpResult a
  deriving (Show, ShowPretty, Eq)
--
-- The idea is that `a` represents the data which is the actual content which needs
-- to be solved by this constraint, and the type of the wrapper around it tells us
-- what kind of constraint this is.
-- For example, it makes sens to have `IsEqual (DMType,DMType)` or `IsMaximum (Sensitivity,Sensitivity,Sensitivity)`
-- or `IsTypeOpResult DMTypeOp`.
--
-- Having the generic type parameter a allows us to treat all constraints equally,
-- in cases where we are writing generic code for dealing with any kind of constraints.
-- In order for this to work, we have to proof that our "constraint type" is nothing
-- but a wrapper around `a`. For this, we show that it is an instance of the `TCConstraint`
-- type class, for example:
instance TCConstraint IsTypeOpResult where
  constr = IsTypeOpResult
  runConstr (IsTypeOpResult c) = c
  -- where
  --
  -- `constr` :: a -> c a
  --  requires that we can put our "data" into the constraint.
  --
  -- `runConstr` :: c a -> a
  --  requires that we can extract our "data" from the constraint.
--
--
-- There are two further type classes associated with constraints:
-- 1. Constraints exist in order to be solved. This is axiomatized by the typeclass
--    `Solve isT c a`, which says that the class of monads described by `isT`
--    (e.g., `isT := MonadDMTC`) can solve constraints of (wrapper-)type `c`
--    with data `a`.
--
--    For example, we have the instance `Solve MonadDMTC IsTypeOpResult DMTypeOp`
--    (see in DiffMu.Typecheck.Operations).
--    But also `Solve MonadDMTC IsEqual (DMTypeOf k)`, for any k.
--    (see in DiffMu.Core.Unification).
--    These instances implement the `solve_` function which runs in the `MonadDMTC` monad
--    and tries to solve the constraint.
--
--    NOTE: we use a class of monads `isT` here, instead of a specific monad `t` here, because
--          of the following problem: It should be possible to add a constraint while in the
--          sensitivity typechecking monad (`TC Sensitivity a`) but solve it in the privacy monad.
--          Thus we define "solvability" for the whole class of TC like monads at once.
--          That is, for the class `MonadDMTC`.
--
-- 2. While typechecking (and/or solving constraints) we sometimes have to add new constraints.
--    The typeclass `MonadConstraint isT t` expresses that, the monad `t` allows us to
--    add, discharge or update constraints which are solvable by monads in the class `isT`.
--    All monads in the `MonadDMTC` class are instances of `MonadConstraint MonadDMTC`.
--
--    But to reiterate: the Haskell type system only allows to add a constraint `c`, via
--    ```
--    do addConstraint (Solvable (c))
--    ```
--    if there is an instance of `Solve isT c a` currently in scope.
--
--
-- NOTE: The basic constraints definitions for equality/less-equal are located
--       in Abstract.Class.Constraint.
--       Here, also the definition of `Solvable` and `MonadConstraint` is to be found.
--
--
--

-- Equal (solver in Core/Unification.hs):
newtype IsEqual a = IsEqual a
  deriving (Show, ShowPretty, Eq)

instance TCConstraint IsEqual where
  constr = IsEqual
  runConstr (IsEqual c) = c

---- Less Equal (subtyping, solver in Typecheck/Subtyping.hs)
newtype IsLessEqual a = IsLessEqual a
  deriving (Show, ShowPretty, Eq)

instance TCConstraint IsLessEqual where
  constr = IsLessEqual
  runConstr (IsLessEqual c) = c


---- Sups
newtype IsSupremum a = IsSupremum a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsSupremum where
  constr = IsSupremum
  runConstr (IsSupremum c) = c

---- Infimum
newtype IsInfimum a = IsInfimum a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsInfimum where
  constr = IsInfimum
  runConstr (IsInfimum c) = c

-------------------------------------------------------------------
-- Function calls and choice resolution (solver in Typecheck/Constraint/IsFunctionArgument.hs)
-------------------------------------------------------------------

---- Choices
newtype IsChoice a = IsChoice a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsChoice where
  constr = IsChoice
  runConstr (IsChoice c) = c


newtype IsFunctionArgument a = IsFunctionArgument a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsFunctionArgument where
  constr = IsFunctionArgument
  runConstr (IsFunctionArgument c) = c

-------------------------------------------------------------------
-- Julia Types (solver in Typecheck/Constraint/IsJuliaEqual.hs)
-------------------------------------------------------------------

-------------------------------------------------------------------
-- set the a type to non-const, in case it's numeric or a tuple.
--

newtype IsNonConst a = IsNonConst a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsNonConst where
  constr = IsNonConst
  runConstr (IsNonConst c) = c

-------------------------------------------------------------------
-- Mostly unify two types, but when encountering const / non-const
-- things behave like subtyping.
--

newtype UnifyWithConstSubtype a = UnifyWithConstSubtype a deriving (Show, ShowPretty, Eq)

instance TCConstraint UnifyWithConstSubtype where
  constr = UnifyWithConstSubtype
  runConstr (UnifyWithConstSubtype c) = c

-----------------------------------------------------------------
-- Fake julia types
--
-- We do not have a real "julia type layer" for now. Since our types
-- mostly only differ from the julia types by having the singleton const types,
-- we have a constraint which checks this by unifying after making variables non-const
-- if possible.

newtype IsJuliaEqual a = IsJuliaEqual a deriving (Show, ShowPretty,  Eq)

instance TCConstraint IsJuliaEqual where
  constr = IsJuliaEqual
  runConstr (IsJuliaEqual c) = c


----------------------------------------------------------------
-- Things that should be functions

newtype IsFunction a = IsFunction a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsFunction where
  constr = IsFunction
  runConstr (IsFunction c) = c

-------------------------------------------------------------------
-- Cheap Constraints (solver in Typecheck/Constraint/CheapConstraints.hs)
-------------------------------------------------------------------



-------------------------------------------------------------------
--  Less (for sensitivities)
--

newtype IsLess a = IsLess a
  deriving (Show, ShowPretty, Eq)

instance TCConstraint IsLess where
  constr = IsLess
  runConstr (IsLess c) = c



-------------------------------------------------------------------
-- set the a type to a variable const, in case it's numeric or a tuple.
--

newtype MakeConst a = MakeConst a deriving (Show, ShowPretty, Eq)

instance TCConstraint MakeConst where
  constr = MakeConst
  runConstr (MakeConst c) = c



----------------------------------------------------------
-- replacing all Numeric TVars by non-const


newtype MakeNonConst a = MakeNonConst a deriving (Show, ShowPretty, Eq)

instance TCConstraint MakeNonConst where
  constr = MakeNonConst
  runConstr (MakeNonConst c) = c



-------------------------------------------------------------------
-- is it Loop or static Loop (i.e. is no of iterations const or not)

newtype IsLoopResult a = IsLoopResult a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsLoopResult where
  constr = IsLoopResult
  runConstr (IsLoopResult c) = c


--------------------------------------------------
-- is it gauss or mgauss?
--

newtype IsAdditiveNoiseResult a = IsAdditiveNoiseResult a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsAdditiveNoiseResult where
  constr = IsAdditiveNoiseResult
  runConstr (IsAdditiveNoiseResult c) = c



--------------------------------------------------
-- projecting of tuples

newtype IsTProject a = IsTProject a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsTProject where
  constr = IsTProject
  runConstr (IsTProject c) = c


--------------------------------------------------
-- black boxes

newtype IsBlackBox a = IsBlackBox a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsBlackBox where
  constr = IsBlackBox
  runConstr (IsBlackBox c) = c



newtype IsBlackBoxReturn a = IsBlackBoxReturn a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsBlackBoxReturn where
  constr = IsBlackBoxReturn
  runConstr (IsBlackBoxReturn c) = c



--------------------------------------------------
-- matrix or vector

newtype IsVecOrMat a = IsVecOrMat a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsVecOrMat where
  constr = IsVecOrMat
  runConstr (IsVecOrMat c) = c



--------------------------------------------------
-- gradient or vector or 1d-matrix
--

newtype IsVecLike a = IsVecLike a deriving (Show, ShowPretty, Eq)

instance TCConstraint IsVecLike where
  constr = IsVecLike
  runConstr (IsVecLike c) = c

--------------------------------------------------
-- container norm conversion
--

newtype ConversionResult a = ConversionResult a deriving (Show, ShowPretty, Eq)

instance TCConstraint ConversionResult where
  constr = ConversionResult
  runConstr (ConversionResult c) = c

