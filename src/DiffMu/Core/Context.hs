
module DiffMu.Core.Context where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadicPolynomial
import DiffMu.Core.MonadTC
import DiffMu.Core.TC
import DiffMu.Core.Unification

import Data.HashMap.Strict as H

import Debug.Trace





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

instance (CheckNeutral m a, CheckNeutral m b) => CheckNeutral m (a :& b) where
  checkNeutral (a :@ b) = (\a b -> and [a,b]) <$> checkNeutral a <*> checkNeutral b

scale :: Sensitivity -> TypeCtx Sensitivity -> TypeCtx Sensitivity
scale η γ = f <$> γ
  where f (τ :@ s) = τ :@ traceShowId ((traceShowId η) ⋅! (traceShowId s))

mscale :: MonadDMTC Sensitivity t => Sensitivity -> t Sensitivity ()
mscale η = types %= scale η

-- msum :: [TCT m e a] -> TCT m e [a]
msum :: (Show e, MonadDMTC e t, MonoidM (t e) e, CheckNeutral (t e) e) => [t e a] -> t e [a]
msum ms = do
  initΣ <- use types
  f initΣ ms def

    where
      f :: (Show e, MonadDMTC e t, MonoidM (t e) e, CheckNeutral (t e) e) => TypeCtx e -> [t e a] -> TypeCtx e -> t e [a]
      f initΣ [] accΣ = types .= accΣ >> return []
      f initΣ (m:ms) accΣ = do
        types .= initΣ
        a <- m
        mΣ <- use types
        m_acc_Σ <- (traceShowId mΣ) ⋆ (traceShowId accΣ)
        as <- f initΣ ms (m_acc_Σ)
        return []

normalizeTypes :: (Normalize (t e) e, MonadDMTC e t) => t e ()
normalizeTypes = do
  curΣ <- use types
  normΣ <- normalize curΣ
  types .= normΣ


-- addConstraint :: Constraint -> TC e ()
-- addConstraint c = modify f
--   where f (Full s t cs γ) = Full s t (c:cs) γ



  -- (⋆) (a₁ :@ b₁) (a₂ :@ b₂) = (a₁ ⋆ a₂ :@ b₁ ⋆ b₂)






-- instance Semigroup (Ctx a) where
--   (<>) a b = undefined

-- instance Semigroup (Full a) where








