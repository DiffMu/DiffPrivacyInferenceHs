{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Core.Symbolic where

import DiffMu.Prelude
-- import DiffMu.Prelude.MonadicAlgebra
import DiffMu.Abstract
import qualified Prelude as P

import Data.Singletons.TH
import Data.HashMap.Strict as H

data SymVal =
  Infty | Fin Float -- a| Ln (SymTerm t)
  deriving (Generic, Eq)
instance Show SymVal where
  show Infty = "∞"
  show (Fin f) = show f
    -- let a = numerator f
    --     b = denominator f
    -- in if b == 1 then show a
    --              else show @Float (fromRational f)

instance Ord SymVal where
  _ <= Infty = True
  Fin a <= Fin b = a <= b
  Infty <= Fin _ = False

instance Hashable SymVal

instance Monad t => CheckNeutral t SymVal where
  checkNeutral a = return (a == Fin 0)

data SensKind = MainSensKind
  deriving (Eq)

genSingletons [''SensKind]

-- data SymTerm = SymTerm SymVal
--   deriving (Generic, Show)
-- addition
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

-- multiplication
-- TODO: Check correctness: is zero handled differently?
instance Monad t => SemiringM t (SymVal) where
  one = pure $ Fin 1
  (⋅) Infty Infty        = pure $ Infty
  (⋅) Infty (Fin _)      = pure $ Infty
  (⋅) (Fin _) Infty      = pure $ Infty
  (⋅) (Fin a) (Fin b)    = pure $ Fin (a P.* b)

-- instance SingI SensKind where


data SymVar (k :: SensKind) =
  HonestVar (SymbolOf k)
  | Id (SymTerm MainSensKind)
  | Ln (SymTerm MainSensKind)
  | Exp (SymTerm MainSensKind, SymTerm MainSensKind)
  | Ceil (SymTerm MainSensKind)
  | Sqrt (SymTerm MainSensKind)
  | Max [SymTerm MainSensKind]
  | Minus (SymTerm MainSensKind, SymTerm MainSensKind)
  | Div (SymTerm MainSensKind, SymTerm MainSensKind)
  deriving (Generic, Eq)

ln s = injectVarId (Ln s)
exp b e = injectVarId (Exp (b, e))
ceil s = injectVarId (Ceil s)
sqrt s = injectVarId (Sqrt s)
maxS s = injectVarId (Max s)
minus s t = injectVarId (Minus (s, t))
divide s t = injectVarId (Div (s, t))

tryComputeSym :: SymVar k -> SymVar k
tryComputeSym x = case f x of
                    Just val -> Id val
                    Nothing -> x
  where
    extractVal :: SymTerm MainSensKind -> Maybe SymVal
    extractVal (SingleKinded (LinCom (MonCom h))) =
      let h' = H.toList h
      in case h' of
        [(exp,coeff)] | exp == neutralId -> Just coeff
        _                                -> Nothing

    dmMinus :: SymVal -> SymVal -> SymVal
    dmMinus Infty Infty     = undefined
    dmMinus Infty b         = undefined
    dmMinus a Infty         = undefined
    dmMinus (Fin a) (Fin b) = Fin (a P.- b)

    dmSqrt :: SymVal -> SymVal
    dmSqrt Infty = Infty
    dmSqrt (Fin a) = Fin (P.sqrt a)

    dmCeil :: SymVal -> SymVal
    dmCeil Infty = Infty
    dmCeil (Fin a) = Fin (P.fromIntegral (P.ceiling a))

    dmExp :: SymVal -> SymVal -> SymVal
    dmExp a Infty = Infty
    dmExp Infty a = Infty
    dmExp (Fin a) (Fin b) = Fin (a P.** b)

    dmLog :: SymVal -> SymVal
    dmLog Infty = Infty
    dmLog (Fin a) = Fin (P.log a)

    dmDiv :: SymVal -> SymVal -> Maybe SymVal
    dmDiv Infty _ = Nothing
    dmDiv _ (Infty) = Nothing
    dmDiv (Fin a) (Fin b) = Just (Fin (a P./ b))

    f :: SymVar k -> Maybe (SymTerm MainSensKind)
    f (HonestVar _)  = Nothing
    f (Id t)         = Nothing
    f (Ln a)         = constCoeff <$> (dmLog <$> extractVal a)
    f (Exp (a,b))    = constCoeff <$> (dmExp <$> extractVal a <*> extractVal b)
    f (Ceil a)       = constCoeff <$> (dmCeil <$> extractVal a)
    f (Sqrt a)       = constCoeff <$> (dmSqrt <$> extractVal a)
    f (Max [])       = Nothing
    f (Max (a:as))   = case all (== a) as of
        False -> constCoeff <$> (maximum <$> mapM extractVal (a:as))
        True  -> Just a
    f (Minus (a, b)) = case extractVal b of
        (Just (Fin 0))  -> pure a
        _               -> constCoeff <$> (dmMinus <$> extractVal a <*> extractVal b)
    -- NOTE: Without the check for b=0, we get an easier definition, but then it only computes
    --       minus terms where both operands are known. And thus terms like
    --         `a_0 - 0.0`
    --       cannot be solved.
    --
    -- f (Minus (a, b)) = constCoeff <$> (dmMinus <$> extractVal a <*> extractVal b)
    f (Div (a, b)) = case extractVal b of
        (Just (Fin 1))  -> pure a
        _               -> constCoeff <$> (join (dmDiv <$> extractVal a <*> extractVal b))

instance Show (SymVar k) where
  show (HonestVar v) = show v
  show (Id te) = "id(" <> show te <> ")"
  show (Ln te) = "ln(" <> show te <> ")"
  show (Exp (b, e)) = show b <> "^(" <> show e <> ")"
  show (Ceil te) = "ceil(" <> show te <> ")"
  show (Sqrt te) = "sqrt(" <> show te <> ")"
  show (Max te) = "max(" <> show te <> ")"
  show (Minus (t1, t2)) = "(" <> show t1 <> " - " <> show t2 <> ")"
  show (Div (t1, t2)) = "(" <> show t1 <> " / " <> show t2 <> ")"

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
  checkContains (Id _) = Nothing
  checkContains (Ln _) = Nothing
  checkContains (Exp _) = Nothing
  checkContains (Ceil _) = Nothing
  checkContains (Sqrt _) = Nothing
  checkContains (Max _) = Nothing
  checkContains (Minus _) = Nothing
  checkContains (Div _) = Nothing
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


instance (Substitute SymVar (CPolyM SymVal Int (SymVar MainSensKind)) (SymVar k2)) where
  substitute σ (HonestVar v) = pure (HonestVar v)
  substitute σ (Id v)        = tryComputeSym <$> Id <$> substitute σ v
  substitute σ (Ln a)        = tryComputeSym <$> Ln <$> substitute σ a
  substitute σ (Exp (b,e))   = tryComputeSym <$> ((\b e -> Exp (b,e)) <$> substitute σ b <*> substitute σ e)
  substitute σ (Ceil a)      = tryComputeSym <$> Ceil <$> substitute σ a
  substitute σ (Sqrt a)      = tryComputeSym <$> Sqrt <$> substitute σ a
  substitute σ (Max as)      = tryComputeSym <$> Max <$> mapM (substitute σ) as
  substitute σ (Minus (a,b)) = tryComputeSym <$> ((\a b -> Minus (a,b)) <$> substitute σ a <*> substitute σ b)
  substitute σ (Div (a,b))   = tryComputeSym <$> ((\a b -> Div (a,b)) <$> substitute σ a <*> substitute σ b)





