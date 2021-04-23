
module DiffMu.Core.Unification where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.TC

import Data.HashMap.Strict
-------------------------------------------------------------------
-- Unification of dmtypes
--


-- Before we can unify dmtypes, we have to proof that we can unify
-- sensitivities.
-- We unify them simply by adding an equality constraint. That this
-- constraint is solvable in any class of monads, in particular in MonadDMTC,
-- is shown in Abstract.Data.MonadicPolynomial.
--
instance Unify MonadDMTC Sensitivity where
  unify_ s1 s2 = do
    c <- addConstraint @MonadDMTC (Solvable (IsEqual (s1, s2)))
    return s1

instance Unify MonadDMTC Privacy where
  unify_ (a1,b1) (a2,b2) = (,) <$> (unify_ a1 a2) <*> (unify_ b1 b2)

-- Unification of DMTypes (of any kind k) is given by:
instance Unify MonadDMTC (DMTypeOf k) where
  unify_ DMReal DMReal                 = pure DMReal
  unify_ DMInt DMInt                   = pure DMInt
  unify_ DMData DMData                 = pure DMData
  unify_ (Numeric t) (Numeric s)       = Numeric <$> unify t s
  unify_ (NonConst τ₁) (NonConst τ₂)   = NonConst <$> unify τ₁ τ₂
  unify_ (Const η₁ τ₁) (Const η₂ τ₂)   = Const <$> unify η₁ η₂ <*> unify τ₁ τ₂
  unify_ (as :->: a) (bs :->: b)       = (:->:) <$> unify as bs <*> unify a b
  unify_ (as :->*: a) (bs :->*: b)     = (:->*:) <$> unify as bs <*> unify a b
  unify_ (DMTup as) (DMTup bs)         = DMTup <$> unify as bs
  unify_ (TVar x) (TVar y) | x == y    = pure $ TVar x
  unify_ (TVar x) t                    = addSub (x := t) >> pure t
  unify_ t (TVar x)                    = addSub (x := t) >> pure t
  unify_ L1 L1                         = pure L1
  unify_ L2 L2                         = pure L2
  unify_ LInf LInf                     = pure LInf
  unify_ U U                           = pure U
  unify_ (Clip k) (Clip s)             = Clip <$> unify k s
  unify_ (DMMat nrm1 clp1 n1 m1 τ1) (DMMat nrm2 clp2 n2 m2 τ2) =
     DMMat <$> unify nrm1 nrm2 <*> unify clp1 clp2 <*> unify n1 n2 <*> unify m1 m2 <*> unify τ1 τ2
  unify_ t s                           = throwError (UnificationError t s)

-- Above we implictly use unification of terms of the type (a :& b).
-- These are unified entry-wise:
instance (Unify isT a, Unify isT b) => Unify isT (a :& b) where
  unify_ (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unify_ a₁ a₂ <*> unify_ e₁ e₂

-- Similarly, lists of terms are unified elements wise,
-- but they only match if they are of the same lenght:
instance (Show a, Unify MonadDMTC a) => Unify MonadDMTC [a] where
  unify_ xs ys | length xs == length ys = mapM (uncurry unify_) (zip xs ys)
  unify_ xs ys = throwError (UnificationError xs ys)

-- Using the unification instance, we implement solving of the `IsEqual` constraint for DMTypes.
instance Solve MonadDMTC IsEqual (DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ _ (IsEqual (a,b)) = unify_ a b >> pure ()


-- TODO: not implemented yet, need julia subtyping access.
instance Solve MonadDMTC IsChoice (DMType, (HashMap [JuliaType] DMType)) where
  solve_ Dict _ _ (IsChoice (τ, cs)) = pure ()


-- TODO implement this
instance Solve MonadDMTC IsLessEqual (Sensitivity, Sensitivity) where
  solve_ Dict _ _ (IsLessEqual (s1, s2)) = pure ()

-------------------------------------------------------------------
-- Monadic monoid structure on dmtypes
--

-- We define a monadic semigroup structure on `DMTypeOf k`,
-- which is simply unification.
instance (IsT MonadDMTC t) => SemigroupM (t) (DMTypeOf k) where
  (⋆) = unify

-- This is even a monadic monoid, with the neutral element given by a new type variable.
instance (SingI k, Typeable k, IsT MonadDMTC t) => MonoidM (t) (DMTypeOf k) where
  neutral = TVar <$> newTVar ""

-- An optimized check for whether a given DMType is a neutral does not create new typevariables,
-- but simply checks if the given DMType is one.
instance (SingI k, Typeable k, IsT MonadDMTC t) => (CheckNeutral (t) (DMTypeOf k)) where
  checkNeutral (TVar x) = return True
  checkNeutral (_) = return False



