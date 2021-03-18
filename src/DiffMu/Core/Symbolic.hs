
module DiffMu.Core.Symbolic where

import DiffMu.Prelude
-- import DiffMu.Prelude.MonadicAlgebra
import DiffMu.Core.MonadicPolynomial
import qualified Prelude as P

data SymVal =
  Infty | Fin Float -- a| Ln (SymTerm t)
  deriving (Generic, Show, Eq)

instance Hashable SymVal

instance Monad t => CheckNeutral t SymVal where
  checkNeutral ma = do a <- ma
                       return (a == Fin 0)

-- data SymTerm = SymTerm SymVal
--   deriving (Generic, Show)

instance Monad t => SemigroupM t (SymVal) where
  (⋆) Infty Infty        = pure Infty
  (⋆) Infty (Fin _)      = pure Infty
  (⋆) (Fin _) Infty      = pure Infty
  (⋆) (Fin a) (Fin b)    = pure $ Fin (a P.+ b)


instance Monad t => MonoidM t (SymVal) where
  neutral = pure $ Fin 0

instance Monad t => CMonoidM t (SymVal)

-- instance Group SymVal where
--   neg Infty = MinusInfty

-- TODO: Check correctness: is zero handled differently?
instance Monad t => SemiringM t (SymVal) where
  one = pure $ Fin 1
  (⋅) Infty Infty        = pure $ Infty
  (⋅) Infty (Fin _)      = pure $ Infty
  (⋅) (Fin _) Infty      = pure $ Infty
  (⋅) (Fin a) (Fin b)    = pure $ Fin (a P.* b)

data SymVar =
  Var Symbol | Ln SymTerm
  deriving (Show, Generic, Eq, Ord)

instance Hashable SymVar

type SymTerm = CPolyM SymVal Rational SymVar


-- type SymTerm t = Combination t SymVal Rational Symbol

