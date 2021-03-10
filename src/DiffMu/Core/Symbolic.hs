
module DiffMu.Core.Symbolic where

import DiffMu.Prelude
import qualified Prelude as P

data SymVal =
  Infty | Fin Float
  deriving (Generic, Show)

data SymTerm = SymTerm
  deriving (Generic, Show)

{-
instance Monoid SymVal where
  (<>) Infty Infty        = Infty
  (<>) Infty (Fin _)      = Infty
  (<>) (Fin _) Infty      = Infty
  (<>) (Fin a) (Fin b)    = Fin (a P.+ b)

instance Monoid SymVal where
  mempty = Fin 0

instance CMonoid SymVal

-- instance Group SymVal where
--   neg Infty = MinusInfty

-- TODO: Check correctness: is zero handled differently?
instance SemiRing SymVal where
  one = Fin 1
  (*) Infty Infty        = Infty
  (*) Infty (Fin _)      = Infty
  (*) (Fin _) Infty      = Infty
  (*) (Fin a) (Fin b)    = Fin (a P.* b)

type SymTerm = CPoly SymVal Rational Symbol

-}
