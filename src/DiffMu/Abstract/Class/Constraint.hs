
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

class TCConstraint c => Solve (isT :: * -> (* -> * -> *) -> Constraint) c a where
  solve_ :: Dict ((IsT isT t)) -> SolvingMode -> Symbol -> c a -> t e ()



data Solvable isT where
  Solvable :: (Solve isT c a, (HasNormalize isT t a), Show (c a)) => c a -> Solvable isT

-- solve' :: (Solve isT c a, IsT isT t, Normalize (t e) a) => c a -> t e ()
solve :: (Monad (t e), IsT isT t) => SolvingMode -> Symbol -> (Solvable isT) -> t e ()
solve mode name (Solvable (c :: c a) :: Solvable isT) = f Proxy
  where f :: (Monad (t e), IsT isT t) => Proxy (t e) -> t e ()
        f (_ :: Proxy (t e)) = (insideConstr normalize c >>= solve_ @isT Dict mode name)


instance (isT e t, Monad (t e)) => Normalize (t e) (Solvable isT) where
  normalize (Solvable (c :: c a)) = (Solvable @isT <$> insideConstr (normalize @(t e)) c)

instance Show (Solvable isT) where
  show (Solvable c) = show c



class (Monad t) => MonadConstraint isT t | t -> isT where
-- class (IsT isT t) => MonadConstraint v isT t e | t -> isT where
  addConstraint :: Solvable isT -> t Symbol
  getUnsolvedConstraintMarkNormal :: t (Maybe (Symbol , Solvable isT))
  dischargeConstraint :: Symbol -> t ()
  failConstraint :: Symbol -> t ()
  updateConstraint :: Symbol -> Solvable isT -> t ()



-- Basic constraints
newtype IsEqual a = IsEqual a
  deriving (Show)
--   deriving (TCConstraint)
instance TCConstraint IsEqual where
  constr = IsEqual
  runConstr (IsEqual c) = c


---- Less Equal
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

