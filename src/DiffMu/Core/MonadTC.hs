
-- {-# LANGUAGE UndecidableInstances #-}

module DiffMu.Core.MonadTC where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.Term

-- class (TermSubstitute x a) => MonadSubstitute x a t where

class (Monad t, Term v a) => MonadTC v a t where
  addSub :: Sub v a -> t ()
  getSubs :: t (Subs v a)

class Constraint c where
  constr :: a -> c a
  runConstr :: c a -> a

  constrInside :: (Monad t) => (a -> t a) -> c a -> t (c a)
  constrInside f c = constr <$> f (runConstr c)


-- data Discharged = IsDischarged | NotDischarged

class (Normalize t a, Constraint c) => Solve t c a where
  solve_ :: c a -> t ()

class (Normalize t a) => Unify t a where
  unify_ :: a -> a -> t a

unify :: (Unify t a) => a -> a -> t a
unify a b = chainM2 unify_ (normalize a) (normalize b)

instance (Normalize t a, Normalize t b) => Normalize t (a,b) where
  normalize (a,b) = (,) <$> normalize a <*> normalize b

instance (Normalize t a, Unify t a) => Solve t IsEqual (a,a) where
  solve_ (IsEqual (a,b)) = unify a b >> pure ()

solve :: (Solve t c a) => c a -> t ()
solve c = constrInside normalize c >>= solve_


data Solvable t where
  Solvable :: Solve t c a => c a -> Solvable t

data Solvable' (t :: * -> * -> *) where
  Solvable' :: (forall e. Solve (t e) c a, Show (c a)) => c a -> Solvable' t

instance Show (Solvable' t) where
  show (Solvable' c) = show c

class (forall e. Monad (t e)) => MonadConstraint' t s | s -> t where
  type ConstrVar t :: *
  addConstraint' :: Solvable' t -> s e ()
  addConstraint'2 :: (forall e. Solve (t e) c a, Show (c a)) => c a -> s e ()
  dischargeConstraint' :: ConstrVar t -> s e ()
  getUnsolvedConstraint' :: s e (Maybe (ConstrVar t, Solvable' t))

class Monad t => MonadConstraint t where
  addConstraint :: Solvable t -> t ()
  getUnsolvedConstraint :: t (Solvable t)


newtype IsEqual a = IsEqual a
instance Constraint IsEqual where
  constr = IsEqual
  runConstr (IsEqual c) = c

newtype IsLessEqual a = IsLessEqual a
  deriving (Show)
instance Constraint IsLessEqual where
  constr = IsLessEqual
  runConstr (IsLessEqual c) = c

-- class Solve t IsEqual (a,a) => Unifiable t a

-- instance Unifiable 
-- type UnifiableTerm = 
-- class Term a => UnifiableTerm a where


-- normalizeTerm :: (MonadTC a x t) => a -> t a
-- normalizeTerm a = do
--     σs <- getSubs
--     σs ↷ a






