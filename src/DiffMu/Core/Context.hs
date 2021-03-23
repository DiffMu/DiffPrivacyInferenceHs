
module DiffMu.Core.Context where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadicPolynomial

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








