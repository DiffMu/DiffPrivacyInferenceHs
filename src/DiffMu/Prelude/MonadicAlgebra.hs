
-- {-# LANGUAGE UndecidableInstances #-}

module DiffMu.Prelude.MonadicAlgebra
--   (
--     SemigroupM(..), MonoidM(..), CMonoidM(..), SemiringM(..)
-- -- , Abelian(..), Ring(..), Module(..)
--     -- HasInverse(..)
--   )
where

import DiffMu.Imports

-- import Data.Semigroup as All hiding (diff, Min, Max, Any)
-- import Data.Monoid as All hiding (Last, First, getLast, getFirst)

import qualified Prelude as P


chainM2 :: Monad t => (a -> b -> t c) -> t a -> t b -> t c
chainM2 f a b = do
  a' <- a
  b' <- b
  f a' b'

chainM2_L :: Monad t => (a -> b -> t c) -> t a -> b -> t c
chainM2_L f a b = do
  a' <- a
  f a' b

chainM2_R :: Monad t => (a -> b -> t c) -> a -> t b -> t c
chainM2_R f a b = do
  b' <- b
  f a b'

extractIdentity2 :: (a -> b -> Identity c) -> a -> b -> c
extractIdentity2 f a b = runIdentity (f a b)

class Monad t => Normalize t n where
  normalize :: n -> t n


-- class Has a where
--   mempty :: a
-- class Pointed a where
--   pt :: a


class Monad t => SemigroupM t a where
  (⋆) :: a -> a -> t a

(<⋆>) = chainM2 (⋆)
(<⋆)  = chainM2_L (⋆)
(⋆>)  = chainM2_R (⋆)
(⋆!)  = extractIdentity2 (⋆)

-- type Semigroup = SemigroupM Identity

class (SemigroupM t a) => MonoidM t a where
  neutral :: t a
neutralId :: MonoidM Identity a => a
neutralId = runIdentity neutral
-- type Monoid = MonoidM Identity

class MonoidM t a => CheckNeutral t a where
  checkNeutral :: a -> t Bool

-- instance (SemigroupM t a) => MonoidM t a

class (MonoidM t a) => CMonoidM t a where
  (+) :: a -> a -> t a
  (+) x y = x ⋆ y
  zero :: t a
  zero = neutral

(<+>) = chainM2 (+)
(<+)  = chainM2_L (+)
(+>)  = chainM2_R (+)
(+!)  = extractIdentity2 (+)

-- type Semigroup = SemigroupM Identity

-- class HasOne r where
--   one :: r

class (CMonoidM t r) => SemiringM t r where
  one :: t r
  (⋅) :: r -> r -> t r

(<⋅>) = chainM2 (⋅)
(<⋅)  = chainM2_L (⋅)
(⋅>)  = chainM2_R (⋅)
(⋅!)  = extractIdentity2 (⋅)

(?:) = liftM2 (:)
(?<>) = liftM2 (<>)

class (MonoidM t m) => ModuleM t m x where
  (↷) :: m -> x -> t x

-- NOTE: Appearently, these functions cannot be defined using
--       chainM2 and its variants. Reason unclear.
(<↷>) :: ModuleM t m x => t m -> t x -> t x
(<↷>) a b = do
  a' <- a
  b' <- b
  a' ↷ b'

(<↷) :: ModuleM t m x => t m -> x -> t x
(<↷) a b = do
  a' <- a
  a' ↷ b

(↷>) :: ModuleM t m x => m -> t x -> t x
(↷>) a b = do
  b' <- b
  a ↷ b'

(↷!) :: ModuleM Identity m x => m -> x -> x
(↷!) a b = runIdentity (a ↷ b)


  {-
(?:) :: Monad m => m a -> m [a] -> m [a]
(?:) x xs = (:) <$> x <⋅> xs

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
--   (⋅) :: r -> r -> r



-- instance P.Num a => Semigroup a where
--   (<>) a b = a P.+ b

-}
-}
