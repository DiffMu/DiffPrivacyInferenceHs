{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Core.Symbolic where

import DiffMu.Prelude
-- import DiffMu.Prelude.MonadicAlgebra
import DiffMu.Abstract
import qualified Prelude as P

import Data.Singletons.TH

data SymVal =
  Infty | Fin Rational -- a| Ln (SymTerm t)
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

data SensKind = MainSensKind
  deriving (Eq)

genSingletons [''SensKind]


data SymVar (k :: SensKind) =
  HonestVar (SymbolOf k) | Ln (SymTerm MainSensKind)
  deriving (Generic, Eq)

instance Show (SymVar k) where
  show (HonestVar v) = show v
  show (Ln te) = "ln(" <> show te <> ")"

instance Hashable (SymVar k)


instance Show SensKind where
  show MainSensKind = "S"


-- newtype MultInt = MultInt Int
--   deriving (Hashable, Eq)
-- instance Show MultInt where
--   show (MultInt a) = show a

-- instance Monad m => SemigroupM m MultInt where
--   (⋆) (MultInt a) (MultInt b) = pure $ MultInt $ (P.*) a b

-- instance Monad m => MonoidM m MultInt where
--   neutral = pure (MultInt 1)
type SymTerm :: SensKind -> *
type SymTerm = CPolyM SymVal Int (SymVar MainSensKind)
-- SingleKinded (LinCom SymVal (MonCom Int (SymVar MainSensKind)))

instance CheckContains (SymVar MainSensKind) (SymbolOf MainSensKind) where
  checkContains (Ln _) = Nothing
  checkContains (HonestVar v) = Just v


-- WARNING: This is not implemented, we should actually check for zero here!
instance Monad m => CheckNeutral m (SymTerm k) where
  checkNeutral a = pure False

-- SingleKinded (LinCom SymVal (MonCom Int (SymVar MainSensKind)))

svar :: SymbolOf MainSensKind -> (SymTerm MainSensKind)
svar a = injectVarId (HonestVar a)

  -- LinCom (MonCom [(Fin 1, MonCom [(1,HonestVar a)])])

-- type SymTerm t = Combination t SymVal Rational Symbol

instance (SemigroupM m a, SemigroupM m b) => SemigroupM m (a,b) where
  (⋆) (a1,a2) (b1,b2) = (,) <$> (a1 ⋆ b1) <*> (a2 ⋆ b2)

instance (MonoidM m a, MonoidM m b) => MonoidM m (a,b) where
  neutral = (,) <$> neutral <*> neutral

instance (CheckNeutral m a, CheckNeutral m b) => CheckNeutral m (a,b) where
  checkNeutral (a,b) = do
    x <- checkNeutral a
    y <- checkNeutral b
    return (and [x,y])
