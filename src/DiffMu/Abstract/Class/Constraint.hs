
{-# LANGUAGE UndecidableInstances #-}


module DiffMu.Abstract.Class.Constraint where

import DiffMu.Prelude
import DiffMu.Abstract.Class.IsT
import DiffMu.Abstract.Class.Term
-- import DiffMu.Abstract.Class.MonadTerm

data SolvingMode = SolveExact | SolveAssumeWorst

class TCConstraint c where
  constr :: a -> c a
  runConstr :: c a -> a

  insideConstr :: (Monad t) => (a -> t a) -> c a -> t (c a)
  insideConstr f c = constr <$> f (runConstr c)

class TCConstraint c => Solve (isT :: (* -> *) -> Constraint) c a where
  solve_ :: Dict ((IsT isT t)) -> SolvingMode -> Symbol -> c a -> t ()



data Solvable isT where
  Solvable :: (Solve isT c a, (HasNormalize isT a), Show (c a)) => c a -> Solvable isT

-- solve' :: (Solve isT c a, IsT isT t, Normalize (t) a) => c a -> t ()
solve :: (Monad (t), IsT isT t) => SolvingMode -> Symbol -> (Solvable isT) -> t ()
solve mode name (Solvable (c :: c a) :: Solvable isT) = f Proxy
  where f :: (Monad (t), IsT isT t) => Proxy (t) -> t ()
        f (_ :: Proxy (t)) = (insideConstr normalize c >>= solve_ @isT Dict mode name)


instance (isT t, Monad (t)) => Normalize (t) (Solvable isT) where
  normalize (Solvable (c :: c a)) = (Solvable @isT <$> insideConstr (normalize @(t)) c)

instance Show (Solvable isT) where
  show (Solvable c) = show c



class (Monad t) => MonadConstraint isT t | t -> isT where
-- class (IsT isT t) => MonadConstraint v isT t e | t -> isT where
  type ConstraintBackup t
  addConstraint :: Solvable isT -> t Symbol
  getUnsolvedConstraintMarkNormal :: t (Maybe (Symbol , Solvable isT))
  dischargeConstraint :: Symbol -> t ()
  failConstraint :: Symbol -> t ()
  updateConstraint :: Symbol -> Solvable isT -> t ()
  clearConstraints :: t (ConstraintBackup t)
  restoreConstraints :: ConstraintBackup t -> t ()



-- Basic constraints
newtype IsEqual a = IsEqual a
  deriving (Show)

instance TCConstraint IsEqual where
  constr = IsEqual
  runConstr (IsEqual c) = c


---- Less Equal (subtyping)
newtype IsLessEqual a = IsLessEqual a
  deriving (Show)

instance TCConstraint IsLessEqual where
  constr = IsLessEqual
  runConstr (IsLessEqual c) = c

---- Sups
newtype IsSupremum a = IsSupremum a deriving Show

instance TCConstraint IsSupremum where
  constr = IsSupremum
  runConstr (IsSupremum c) = c

---- Choices
newtype IsChoice a = IsChoice a deriving Show

instance TCConstraint IsChoice where
  constr = IsChoice
  runConstr (IsChoice c) = c

