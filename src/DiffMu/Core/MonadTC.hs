
-- {-# LANGUAGE UndecidableInstances #-}

module DiffMu.Core.MonadTC where

import DiffMu.Prelude
-- import DiffMu.Core.Definitions
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

data Solvable'' (t :: (* -> *) -> * -> * -> *) where
  Solvable'' :: (forall m e. Monad m => Solve (t m e) c a, Show (c a)) => c a -> Solvable'' t

instance Show (Solvable'' t) where
  show (Solvable'' c) = show c

class (forall e. Monad (t e)) => MonadConstraint' v t s | s -> t, s -> v where
  -- type ConstrVar t :: *
  addConstraint' :: Solvable' t -> s v
  -- addConstraint'2 :: (forall e. Solve (t e) c a, Show (c a)) => c a -> s ()
  dischargeConstraint' :: v -> s ()
  getUnsolvedConstraint' :: s (Maybe (v, Solvable' t))

class (forall m e. Monad m => Monad (t m e)) => MonadConstraint'' v t | t -> v where
  addConstraint'' :: (forall m e. Monad m => Solve (t m e) c a, Monad m, Show (c a)) => c a -> t m e v

class Monad t => MonadConstraint t where
  addConstraint :: Solvable t -> t ()
  getUnsolvedConstraint :: t (Solvable t)

---------------------------------------
-- solution with tags
class (Normalize t a, Constraint c) => SolveTag (tag :: k) t c a | t -> tag where
  solveTag_ :: c a -> t ()

data SolvableTag (tag :: k) where
  SolvableTag :: (forall t. SolveTag tag t c a) => c a -> SolvableTag tag

class Monad t => MonadConstraintTag tag v t where
  addConstraintTag :: SolveTag tag t c a => c a -> t v
  -- getUnsolvedConstraint :: t (Solvable t)

------------------------------------
-- solution with different monads

class (Normalize t a, Constraint c) => SolveDiff t c a where
  solveDiff_ :: c a -> t ()

class Monad t => MonadConstraintDiff v t s | s -> t where
  addConstraintDiff :: SolveDiff t c a => c a -> s v

-- class SolvableDiff t where
--   SolvableDiff :: SolveDiff t c a => c a -> SolvableDiff t

------------------------------------

type Constraint' c = (forall a. Newtype (c a) a)


-- => Constraint c where

newtype Constr a = On a
instance Constraint (Constr) where
  constr = On
  runConstr (On c) = c

newtype IsTypeOpResult a = IsTypeOpResult a
  deriving (Show)
instance Newtype (IsTypeOpResult a) a
instance Constraint IsTypeOpResult where
  constr = IsTypeOpResult
  runConstr (IsTypeOpResult c) = c
  -- deriving (Constraint)

newtype IsEqual a = IsEqual a
--   deriving (Constraint)
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






