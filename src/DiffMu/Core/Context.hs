
module DiffMu.Core.Context where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadicPolynomial

import Data.HashMap.Strict as H

type Context v a = HashMap v a





-- testa :: Hashable a => a -> a
-- testa x = x

-- testb :: (Hashable v, Hashable a) => Context v a -> Context v a
-- testb x = testa x

-- instance Default (NameCtx) where

-- instance Default (Ctx a) where
--   def = Ctx (LinCom (MonCom []))

-- instance Default (Full a) where


instance (SemigroupM t a, SemigroupM t b) => SemigroupM t (a :& b) where
  (⋆) (a₁ :@ b₁) (a₂ :@ b₂) = (:@) <$> (a₁ ⋆ a₂) <*> (b₁ ⋆ b₂)

instance (MonoidM t a, MonoidM t b) => MonoidM t (a :& b) where
  neutral = (:@) <$> neutral <*> neutral


-- addConstraint :: Constraint -> TC e ()
-- addConstraint c = modify f
--   where f (Full s t cs γ) = Full s t (c:cs) γ



  -- (⋆) (a₁ :@ b₁) (a₂ :@ b₂) = (a₁ ⋆ a₂ :@ b₁ ⋆ b₂)






-- instance Semigroup (Ctx a) where
--   (<>) a b = undefined

-- instance Semigroup (Full a) where








