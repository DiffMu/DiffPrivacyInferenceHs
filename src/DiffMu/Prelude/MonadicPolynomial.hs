
module DiffMu.Prelude.MonadicPolynomial where

import DiffMu.Imports
import DiffMu.Prelude.MonadicAlgebra

-- import GHC.Generics as All (Generic)
-- import Prelude as All (Show, IO, putStrLn, undefined, otherwise, fst, snd)

-- import Data.Semigroup as All hiding (diff, Min, Max, Any, WrapMonoid)
-- import Data.Monoid as All hiding (Last, First, getLast, getFirst, WrapMonoid)


class Monad t => NormalizableM t n where
  normalize :: n -> t n

newtype MonDict m v = MonDict ([(m,v)])
  deriving (Generic, Show)

class (MonoidM t m, CheckNeutral t m, Eq m, Ord v)    => HasMonDict t m v
instance (MonoidM t m, CheckNeutral t m, Eq m, Ord v) => HasMonDict t m v


instance (HasMonDict t m v) => NormalizableM t (MonDict m v) where
  normalize (MonDict xs) = MonDict <$> (sor xs [])

    where singl :: (m,v) -> t [(m,v)]
          singl (m,v) = checkNeutral m >>= f
             where f True  = pure []
                   f False = pure [(m,v)]

          ins :: (m,v) -> [(m,v)] -> t [(m,v)]
          ins (m,v) [] = singl (m,v)
          ins (m,v) ((m2, v2) : xs) = f (compare v v2)
             where f :: Ordering -> t [(m,v)]
                   f LT = singl (m,v) ?<> pure ((m2,v2) : xs)
                   f EQ = do m' <- m ⋆ m2
                             singl (m', v) ?<> pure xs
                   f GT = pure (m2,v2) ?: (ins (m,v) xs)

          sor :: [(m,v)] -> [(m,v)] -> t [(m,v)]
          sor [] ys = return ys
          sor (x:xs) ys =
            do ys' <- (ins x ys)
               (sor xs ys)


instance (HasMonDict t m v) => SemigroupM t (MonDict m v) where
  (⋆) (MonDict xs) (MonDict ys) = normalize (MonDict (xs <> ys))

instance (HasMonDict t m v) => MonoidM t (MonDict m v) where
  neutral = pure $ MonDict []


instance (HasMonDict t m v) => ModuleM t m (MonDict m v) where
  (⋅) m (MonDict xs) =
    let g m₁ (m₂,v₂) = do m' <- m₁ ⋆ m₂
                          return (m', v₂)
        f m₁ xs = mapM (g m₁) xs

    in (MonDict <$> (f m xs)) >>= normalize


instance (HasMonDict t m v, MonoidM t v) => ModuleM t v (MonDict m v) where
  (⋅) v (MonDict xs) =
    let g v₁ (m₂,v₂) = do v' <- v₁ ⋆ v₂
                          return (m₂, v')
        f v₁ xs = mapM (g v₁) xs

    in (MonDict <$> (f v xs)) >>= normalize

  -- (⋅) v (MonDict xs) = normalize (MonDict (f v xs))
  --   where f v xs = fmap (\(m1,v1) -> (m1, v <> v1)) xs


-- NOTE: Danger: this assumes that the input values are normal!
instance (Eq m, Eq v) => Eq (MonDict m v) where
  (==) (xs) (ys) = f xs ys
    where
      f (MonDict xs) (MonDict ys) = xs == ys

instance (Eq m, Ord v) => Ord (MonDict m v) where
  compare (xs) (ys) = f (xs) (ys)
    where
      f (MonDict xs) (MonDict ys) = compare (fmap snd xs) (fmap snd ys)


-- data PVars e v = PVars (MonDict e v)
--   deriving (Generic, Show)

-- instance Normalizable (Monom r v) where
--   normalize (Monom r vs) = Monom r (sort vs)
-- (PVars e v)

{-
instance (HasInverse m, HasMonDict m v) => HasInverse (MonDict m v) where
  neg (MonDict xs) = MonDict (fmap (\(m,v) -> (neg m, v)) xs)
-}



-- newtype WrapMonoid m = WrapMonoid m
--   deriving (Generic, Show)

-- instance (Ring r) => Monoid (WrapMonoid r) where

newtype Combination r v = Combination (MonDict r v)
  deriving (Generic, Show)

instance (HasMonDict t r v) => SemigroupM t (Combination r v) where
  (⋆) (Combination p) (Combination q) = fmap Combination (p ⋆ q)

instance (HasMonDict t r v) => MonoidM t (Combination r v) where
  neutral = Combination <$> neutral

instance (HasMonDict t r v) => ModuleM t r (Combination r v) where
  (⋅) r (Combination p) = fmap Combination (r ⋅ p)



instance (CMonoidM t r, HasMonDict t r v) => CMonoidM t (Combination r v)


-- instance (HasOne r, HasMonDict t r v, Pointed v) => HasOne (Combination r v) where
--   one = Combination (MonDict [(one, pt)])

instance (SemiringM t r, HasMonDict t r v, MonoidM t v) => SemiringM t (Combination r v) where
  one = f <$> one <*> neutral
    where f a b = Combination (MonDict [(a, b)])

  (*) (Combination (MonDict p)) (Combination q) = fmap Combination (f p q)
    where f :: [(r,v)] -> MonDict r v -> t (MonDict r v)
          f [] q = neutral
          f ((xr,xv) : xs) q = (pure xr) ?⋅ (pure xv ?⋅ pure q) ?⋆ (f xs q)


type CPolyM r e v = Combination r (MonDict e v)

{-
-}
