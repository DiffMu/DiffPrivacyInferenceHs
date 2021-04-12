
module DiffMu.Core.Context where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.TC
import DiffMu.Core.Unification

import Data.HashMap.Strict as H

import Debug.Trace

-------------------------------------------------------------------
-- Operations on contexts / On the current context in the monad.
--

-- A helper function which scale any type context with a given sensitivity `η`.
scale :: Sensitivity -> TypeCtx Sensitivity -> TypeCtx Sensitivity
scale η γ = f <$> γ
  where f (τ :@ s) = τ :@ traceShowId ((traceShowId η) ⋅! (traceShowId s))

-- Scales the current type context living in our typechecking-state monad by a given `η`.
mscale :: MonadDMTC Sensitivity t => Sensitivity -> t Sensitivity ()
mscale η = types %= scale η

-- Given a list of computations in a MonadDMTC monad, it executes all computations
-- on the same input type context, and sums the resulting type contexts.
-- All additional data (constraints, substitutions, metavariable contexts) are passed sequentially.
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


-- Helper function for using a monadic function to update the state of a "by a lens accessible"
-- value in a state monad. Such an operator does not seem to be defined in the "lenses" library.
-- This might be because using it is not always well behaved, the following note applies.
--
-- NOTE: Warning, this function destroys information if the function `f` which does the update
-- has monadic effects in m which affect the part of the state which is accessed by the lens.
(%=~) :: MonadState s m => (forall f. Functor f => LensLike f s s a a) -> (a -> m a) -> m ()
(%=~) lens f = do
  curVal <- use lens
  newVal <- f curVal
  lens .= newVal
  return ()

infixr 4 %=~

-- Normalizes all contexts in our typechecking monad, i.e., applies all available substitutions.
normalizeContext :: (Normalize (t e) e, MonadDMTC e t) => t e ()
normalizeContext = do
  types %=~ normalize
  meta.constraints %=~ normalize


-- Iterates over all constraints which are currently in a "changed" state, and tries to solve them.
-- Returns if no "changed" constraints remains.
-- An unchanged constraint is marked "changed", if it is affected by a new substitution.
-- A changed constraint is marked "unchanged" if it is read by a call to `getUnsolvedConstraintMarkNormal`.
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





