
module DiffMu.Core.Context where

import DiffMu.Prelude
-- import DiffMu.Core.MonadicPolynomial
import DiffMu.Abstract
import DiffMu.Core.Definitions
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
msum :: (Show e, IsT MonadDMTC t, MonoidM (t e) e, CheckNeutral (t e) e) => [t e a] -> t e [a]
msum ms = do
  initΣ <- use types
  f initΣ ms def

    where
      f :: (Show e, IsT MonadDMTC t, MonoidM (t e) e, CheckNeutral (t e) e) => TypeCtx e -> [t e a] -> TypeCtx e -> t e [a]
      f initΣ [] accΣ = types .= accΣ >> return []
      f initΣ (m:ms) accΣ = do
        types .= initΣ
        a <- m
        mΣ <- use types
        m_acc_Σ <- (traceShowId mΣ) ⋆ (traceShowId accΣ)
        as <- f initΣ ms (m_acc_Σ)
        return []


monadicChange :: MonadState s m => (m a) -> (a -> m s) -> (a -> m a) -> m ()
monadicChange getF putF change = do
  curVal <- getF
  newVal <- change curVal
  putF newVal
  return ()

-- NOTE: Warning, this function destroys information if the function `f` which does the update
-- has monadic effects in m which affect the part of the state which is accessed by the lens.
(%=~) :: MonadState s m => (forall f. Functor f => LensLike f s s a a) -> (a -> m a) -> m ()
(%=~) lens f = do
  curVal <- use lens
  newVal <- f curVal
  lens .= newVal
  return ()

infixr 4 %=~


-- (%=~) :: MonadState s m => (LensLike m s s a a) -> (a -> m a) -> m ()
-- (%=~) lens f = do
--   curState <- get
--   newState <- lens f curState
--   put newState
--   return ()

  -- curV <- use lens
  -- normV <- f curV
  -- lens .= normV
  -- return ()

-- mytest lens = do
--   curΣ <- use lens
--   normΣ <- normalize curΣ
--   lens .= normΣ

normalizeContext :: (Normalize (t e) e, MonadDMTC e t) => t e ()
normalizeContext = do
  types %=~ normalize
  meta.constraints %=~ normalize




solveAllConstraints :: forall t e. (IsT MonadDMTC t, Normalize (t e) e) => SolvingMode -> t e ()
solveAllConstraints mode = do
  normalizeContext
  openConstr <- getUnsolvedConstraintMarkNormal

  --
  ctx <- use (meta @e .constraints)
  traceM ("Solving constraints. I have: " <> show ctx <> ".\n Currently looking at: " <> show (fst <$> openConstr))
  --

  case openConstr of
    Nothing -> return ()
    Just (name, (constr)) -> do
      solve mode name constr
      solveAllConstraints mode




  -- do
  -- curΣ <- use types
  -- normΣ <- normalize curΣ
  -- types .= normΣ


-- addConstraint :: Constraint -> TC e ()
-- addConstraint c = modify f
--   where f (Full s t cs γ) = Full s t (c:cs) γ



  -- (⋆) (a₁ :@ b₁) (a₂ :@ b₂) = (a₁ ⋆ a₂ :@ b₁ ⋆ b₂)






-- instance Semigroup (Ctx a) where
--   (<>) a b = undefined

-- instance Semigroup (Full a) where








