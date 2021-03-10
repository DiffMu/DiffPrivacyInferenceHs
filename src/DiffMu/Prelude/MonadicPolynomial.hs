
module DiffMu.Prelude.MonadicPolynomial where

import DiffMu.Imports
import DiffMu.Prelude.MonadicAlgebra

-- import GHC.Generics as All (Generic)
-- import Prelude as All (Show, IO, putStrLn, undefined, otherwise, fst, snd)

-- import Data.Semigroup as All hiding (diff, Min, Max, Any, WrapMonoid)
-- import Data.Monoid as All hiding (Last, First, getLast, getFirst, WrapMonoid)


class Monad t => NormalizableM t n where
  normalize :: n -> t n

newtype MonDict t m v = MonDict ([(m,v)])
  deriving (Generic)

class (MonoidM t m, Eq m, Ord v)    => HasMonDict t m v
instance (MonoidM t m, Eq m, Ord v) => HasMonDict t m v




instance (HasMonDict t m v) => NormalizableM t (MonDict t m v) where
  normalize (MonDict xs) = MonDict <$> (sor xs [])

    where singl :: (m,v) -> [(m,v)]
          singl (m,v) | m == pt = []
          singl (m,v) | otherwise = [(m,v)]

          ins :: (m,v) -> [(m,v)] -> t [(m,v)]
          ins (m,v) [] = return $ singl (m,v)
          ins (m,v) ((m2, v2) : xs) = f (compare v v2)
             where f :: Ordering -> t [(m,v)]
                   f LT = return $ singl (m,v) <> ((m2,v2) : xs)
                   f EQ = do m' <- m ⋆ m2
                             return $ singl (m', v) <> xs
                   f GT = pure (m2,v2) ?: (ins (m,v) xs)

          sor :: [(m,v)] -> [(m,v)] -> t [(m,v)]
          sor [] ys = return ys
          sor (x:xs) ys =
            do ys' <- (ins x ys)
               (sor xs ys)



instance (HasMonDict t m v) => SemigroupM t (MonDict t m v) where
  (⋆) (MonDict xs) (MonDict ys) = normalize (MonDict (xs <> ys))

instance (HasMonDict t m v) => Pointed (MonDict t m v) where
  pt = MonDict []

instance (HasMonDict t m v) => ModuleM t m (MonDict t m v) where
  (⋅) m (MonDict xs) =
    let g m₁ (m₂,v₂) = do m' <- m₁ ⋆ m₂
                          return (m', v₂)
        f m₁ xs = mapM (g m₁) xs

    in (MonDict <$> (f m xs)) >>= normalize


instance (HasMonDict t m v, MonoidM t v) => ModuleM t v (MonDict t m v) where
  (⋅) v (MonDict xs) =
    let g v₁ (m₂,v₂) = do v' <- v₁ ⋆ v₂
                          return (m₂, v')
        f v₁ xs = mapM (g v₁) xs

    in (MonDict <$> (f v xs)) >>= normalize

  -- (⋅) v (MonDict xs) = normalize (MonDict (f v xs))
  --   where f v xs = fmap (\(m1,v1) -> (m1, v <> v1)) xs


-- NOTE: Danger: this assumes that the input values are normal!
instance (HasMonDict t m v) => Eq (MonDict t m v) where
  (==) (xs) (ys) = f xs ys
    where
      f (MonDict xs) (MonDict ys) = xs == ys

instance (HasMonDict t m v) => Ord (MonDict t m v) where
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

newtype Poly t r v = Poly (MonDict t r v)
  deriving (Generic)

instance (HasMonDict t r v) => SemigroupM t (Poly t r v) where
  (⋆) (Poly p) (Poly q) = fmap Poly (p ⋆ q)

instance (HasMonDict t r v) => Pointed (Poly t r v) where
  pt = Poly pt

instance (HasMonDict t r v) => ModuleM t r (Poly t r v) where
  (⋅) r (Poly p) = fmap Poly (r ⋅ p)


instance (CMonoidM t r, HasMonDict t r v) => CMonoidM t (Poly t r v)


instance (HasOne r, HasMonDict t r v, Pointed v) => HasOne (Poly t r v) where
  one = Poly (MonDict [(one, pt)])

instance (SemiringM t r, HasMonDict t r v, MonoidM t v) => SemiringM t (Poly t r v) where
  (*) (Poly (MonDict p)) (Poly q) = fmap Poly (f p q)
    where f :: [(r,v)] -> MonDict t r v -> t (MonDict t r v)
          f [] q = pure pt
          f ((xr,xv) : xs) q = (pure xr) ?⋅ (xv ⋅ q) ?⋆ (f xs q)


type CPoly t r e v = Poly t r (MonDict t e v)

