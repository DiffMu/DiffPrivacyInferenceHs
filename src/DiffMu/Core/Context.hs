
module DiffMu.Core.Context where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.TC
import DiffMu.Core.Unification
import DiffMu.Core.Symbolic

import qualified Data.HashMap.Strict as H

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

zeroAnnotation :: (MonadDMTC e t, Default e) => t e e
zeroAnnotation = return def

instance Default Sensitivity where
  def = constCoeff (Fin 0)

instance Default Privacy where
  def = (def,def)

truncate :: f -> TypeCtx e -> TypeCtx f
truncate η γ = truncate_annotation <$> γ
   where
      truncate_annotation :: (DMType :& e) -> (DMType :& f)
      truncate_annotation (τ :@ annotation) = do
         n <- checkNeutral annotation
         zero <- zeroAnnotation
         return (case n of
            True -> (τ :@ zero)
            _    -> (τ :@ η))

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


-- Look up the types and sensitivities/privacies of the variables in `xτs` from the current context.
-- If a variable is not present in Σ (this means it was not used in the lambda body),
-- create a new type/typevar according to type hint given in `xτs` and give it zero annotation
getArgList :: forall t. MonadDMTC Sensitivity t => [Asgmt JuliaType] -> t Sensitivity [DMType :& Sensitivity]
getArgList xτs = do
  (γ :: Ctx Symbol (DMType :& Sensitivity)) <- use types

  let f :: Asgmt JuliaType -> t Sensitivity (DMType :& Sensitivity)
      f (x :- τ) = case getValue x γ of
        -- If the symbol was in the context γ, then we get its type and sensitivity
        Just τe -> return τe
        -- if the type hint is DMDUnkown, we just add a typevar. otherwise we can be more specific
        Nothing -> (:@) <$> createDMType τ <*> pure (constCoeff (Fin 0))
  xτs' <- mapM f xτs

  -- We have to remove all symbols x from the context
  let γ' = composeFun ((\(x :- _) -> deleteValue x) <$> xτs) γ

  types .= γ'

  return xτs'

removeVar :: forall t e. MonadDMTC e t => Symbol -> t e (Maybe (DMType :& e))
removeVar x = do
  (γ :: Ctx Symbol (DMType :& e)) <- use types
  let v = getValue x γ
  let γ' = deleteValue x γ
  return v


