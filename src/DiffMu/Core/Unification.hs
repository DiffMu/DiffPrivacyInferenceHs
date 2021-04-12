
module DiffMu.Core.Unification where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.TC

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


-- Unification of DMTypes (of any kind k) is given by:
instance Unify MonadDMTC (DMTypeOf k) where
  unify_ DMReal DMReal                 = pure DMReal
  unify_ DMInt DMInt                   = pure DMInt
  unify_ (Numeric t) (Numeric s)       = Numeric <$> unify_ t s
  unify_ (NonConst τ₁) (NonConst τ₂)   = NonConst <$> unify_ τ₁ τ₂
  unify_ (Const η₁ τ₁) (Const η₂ τ₂)   = Const <$> unify_ η₁ η₂ <*> unify_ τ₁ τ₂
  unify_ (as :->: a) (bs :->: b)       = (:->:) <$> unify_ as bs <*> unify_ a b
  unify_ (TVar x) (TVar y) | x == y    = pure $ TVar x
  unify_ (TVar x) t                    = addSub (x := t) >> pure t
  unify_ t (TVar x)                    = addSub (x := t) >> pure t
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
instance Solve MonadDMTC IsEqual (DMTypeOf k,DMTypeOf k) where
  solve_ Dict _ _ (IsEqual (a,b)) = unify_ a b >> pure ()


-------------------------------------------------------------------
-- Monadic monoid structure on dmtypes
--

-- We define a monadic semigroup structure on `DMTypeOf k`,
-- which is simply unification.
instance (IsT MonadDMTC t) => SemigroupM (t e) (DMTypeOf k) where
  (⋆) = unify

-- This is even a monadic monoid, with the neutral element given by a new type variable.
instance (SingI k, Typeable k, IsT MonadDMTC t) => MonoidM (t e) (DMTypeOf k) where
  neutral = TVar <$> newTVar ""

-- An optimized check for whether a given DMType is a neutral does not create new typevariables,
-- but simply checks if the given DMType is one.
instance (SingI k, Typeable k, IsT MonadDMTC t) => (CheckNeutral (t e) (DMTypeOf k)) where
  checkNeutral (TVar x) = return True
  checkNeutral (_) = return False



