
{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Prelude.MonadicAlgebra
--   (
--     SemigroupM(..), MonoidM(..), CMonoidM(..), SemiringM(..)
-- -- , Abelian(..), Ring(..), Module(..)
--     -- HasInverse(..)
--   )
where

import DiffMu.Imports hiding (mempty, (<>))

-- import Data.Semigroup as All hiding (diff, Min, Max, Any)
-- import Data.Monoid as All hiding (Last, First, getLast, getFirst)

import qualified Prelude as P

class Monad t => SemigroupM t a where
  (⋆) :: a -> a -> t a

chainM2 :: Monad t => (a -> b -> t c) -> t a -> t b -> t c
chainM2 f a b = do
  a' <- a
  b' <- b
  f a' b'

(?⋆) = chainM2 (⋆)

-- class Has a where
--   mempty :: a
class Pointed a where
  pt :: a

class (SemigroupM t a, Pointed a) => MonoidM t a
instance (SemigroupM t a, Pointed a) => MonoidM t a

class (MonoidM t a) => CMonoidM t a where
  (+) :: a -> a -> t a
  (+) x y = x ⋆ y

(?+) = chainM2 (+)

type Semigroup = SemigroupM Identity

class HasOne r where
  one :: r

class (HasOne r, CMonoidM t r) => SemiringM t r where
  (*) :: r -> r -> t r

(?*) a b = chainM2 (*)

(?:) = liftM2 (:)

class (MonoidM t m) => ModuleM t m x where
  (⋅) :: m -> x -> t x

(?⋅) :: ModuleM t m x => t m -> t x -> t x
(?⋅) a b = do
  a' <- a
  b' <- b
  a' ⋅ b'



  {-
(?:) :: Monad m => m a -> m [a] -> m [a]
(?:) x xs = (:) <$> x <*> xs

{-
class Monoid g => HasInverse g where
  neg :: g -> g

class Monoid t => Module t x where
  (⋅) :: t -> x -> x

class (SemiRing r, HasInverse r) => Ring r
instance (SemiRing r, HasInverse r) => Ring r

class (CMonoid t, HasInverse t) => Abelian t
instance (CMonoid t, HasInverse t) => Abelian t



-- class Group a => Abelian a where
--   (+) :: a -> a -> a
  -- (+) x y = x <> y

-- class Abelian r => Ring r where
--   one :: r
--   (*) :: r -> r -> r



-- instance P.Num a => Semigroup a where
--   (<>) a b = a P.+ b

-}
-}
