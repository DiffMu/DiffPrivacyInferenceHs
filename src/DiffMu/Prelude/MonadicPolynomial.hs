
module DiffMu.Prelude.MonadicPolynomial where

import DiffMu.Imports
import DiffMu.Prelude.MonadicAlgebra

-- import GHC.Generics as All (Generic)
-- import Prelude as All (Show, IO, putStrLn, undefined, otherwise, fst, snd)

-- import Data.Semigroup as All hiding (diff, Min, Max, Any, WrapMonoid)
-- import Data.Monoid as All hiding (Last, First, getLast, getFirst, WrapMonoid)


newtype MonCom m v = MonCom ([(m,v)])
  deriving (Generic, Show)

class (MonoidM t m, CheckNeutral t m, Eq m, Ord v)    => HasMonCom t m v
instance (MonoidM t m, CheckNeutral t m, Eq m, Ord v) => HasMonCom t m v


instance (HasMonCom t m v) => Normalize t (MonCom m v) where
  normalize (MonCom xs) = MonCom <$> (sor xs [])

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


instance (HasMonCom t m v) => SemigroupM t (MonCom m v) where
  (⋆) (MonCom xs) (MonCom ys) = normalize (MonCom (xs <> ys))

instance (HasMonCom t m v) => MonoidM t (MonCom m v) where
  neutral = pure $ MonCom []


instance (HasMonCom t m v) => ModuleM t m (MonCom m v) where
  (↷) m (MonCom xs) =
    let g m₁ (m₂,v₂) = do m' <- m₁ ⋆ m₂
                          return (m', v₂)
        f m₁ xs = mapM (g m₁) xs

    in (MonCom <$> (f m xs)) >>= normalize


instance (HasMonCom t m v, MonoidM t v) => ModuleM t v (MonCom m v) where
  (↷) v (MonCom xs) =
    let g v₁ (m₂,v₂) = do v' <- v₁ ⋆ v₂
                          return (m₂, v')
        f v₁ xs = mapM (g v₁) xs

    in (MonCom <$> (f v xs)) >>= normalize

  -- (⋅) v (MonCom xs) = normalize (MonCom (f v xs))
  --   where f v xs = fmap (\(m1,v1) -> (m1, v <> v1)) xs


-- NOTE: Danger: this assumes that the input values are normal!
instance (Eq m, Eq v) => Eq (MonCom m v) where
  (==) (xs) (ys) = f xs ys
    where
      f (MonCom xs) (MonCom ys) = xs == ys

instance (Eq m, Ord v) => Ord (MonCom m v) where
  compare (xs) (ys) = f (xs) (ys)
    where
      f (MonCom xs) (MonCom ys) = compare (fmap snd xs) (fmap snd ys)


-- data PVars e v = PVars (MonCom e v)
--   deriving (Generic, Show)

-- instance Normalizable (Monom r v) where
--   normalize (Monom r vs) = Monom r (sort vs)
-- (PVars e v)

{-
instance (HasInverse m, HasMonCom m v) => HasInverse (MonCom m v) where
  neg (MonCom xs) = MonCom (fmap (\(m,v) -> (neg m, v)) xs)
-}



-- newtype WrapMonoid m = WrapMonoid m
--   deriving (Generic, Show)

-- instance (Ring r) => Monoid (WrapMonoid r) where

newtype LinCom r v = LinCom (MonCom r v)
  deriving (Generic, Show)

instance (HasMonCom t r v) => SemigroupM t (LinCom r v) where
  (⋆) (LinCom p) (LinCom q) = LinCom <$> (p ⋆ q)

instance (HasMonCom t r v) => MonoidM t (LinCom r v) where
  neutral = LinCom <$> neutral

instance (HasMonCom t r v) => ModuleM t r (LinCom r v) where
  (↷) r (LinCom p) = LinCom <$> (r ↷ p)

instance (HasMonCom t r v, MonoidM t v) => ModuleM t v (LinCom r v) where
  (↷) v (LinCom p) = LinCom <$> (v ↷ p)



instance (CMonoidM t r, HasMonCom t r v) => CMonoidM t (LinCom r v)


-- instance (HasOne r, HasMonCom t r v, Pointed v) => HasOne (LinCom r v) where
--   one = LinCom (MonCom [(one, pt)])

instance (SemiringM t r, HasMonCom t r v, MonoidM t v) => SemiringM t (LinCom r v) where
  one = f <$> one <*> neutral
    where f a b = LinCom (MonCom [(a, b)])

  (⋅) (LinCom (MonCom p)) q = (f p q)
    where f :: [(r,v)] -> LinCom r v -> t (LinCom r v)
          f [] q = LinCom <$> neutral
          f ((xr,xv) : xs) q = xr ↷> (xv ↷ q) <+> (f xs q)

type CPolyM r e v = LinCom r (MonCom e v)


