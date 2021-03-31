
module DiffMu.Core.Symbolic where

import DiffMu.Prelude
-- import DiffMu.Prelude.MonadicAlgebra
import DiffMu.Core.MonadicPolynomial2
import qualified Prelude as P

data SymVal =
  Infty | Fin Float -- a| Ln (SymTerm t)
  deriving (Generic, Eq)
instance Show SymVal where
  show Infty = "∞"
  show (Fin f) = show f

instance Hashable SymVal

instance Monad t => CheckNeutral t SymVal where
  checkNeutral a = return (a == Fin 0)

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
  HonestVar Symbol | Ln SymTerm
  deriving (Generic, Eq)

instance Show SymVar where
  show (HonestVar v) = show v
  show (Ln te) = "ln(" <> show te <> ")"

instance Hashable SymVar

-- newtype MultInt = MultInt Int
--   deriving (Hashable, Eq)
-- instance Show MultInt where
--   show (MultInt a) = show a

-- instance Monad m => SemigroupM m MultInt where
--   (⋆) (MultInt a) (MultInt b) = pure $ MultInt $ (P.*) a b

-- instance Monad m => MonoidM m MultInt where
--   neutral = pure (MultInt 1)

type SymTerm = CPolyM SymVal Int SymVar

-- WARNING: This is not implemented, we should actually check for zero here!
instance Monad m => CheckNeutral m SymTerm where
  checkNeutral a = pure False


svar :: Symbol -> SymTerm
svar a = injectVarId (HonestVar a)
  -- LinCom (MonCom [(Fin 1, MonCom [(1,HonestVar a)])])

-- type SymTerm t = Combination t SymVal Rational Symbol

