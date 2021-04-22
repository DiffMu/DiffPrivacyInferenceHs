
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
scale :: Sensitivity -> TypeCtxSP -> TypeCtxSP
scale η (Left γ) = Left (f <$> γ)
  where f (τ :@ s) = τ :@ (η ⋅! s)
scale η (Right γ) = Right (f <$> γ)
  where f :: DMType :& Privacy -> DMType :& Privacy
        f (τ :@ (δ,ε)) = τ :@ (η ⋅! δ, η ⋅! ε)

-- Scales the current type context living in our typechecking-state monad by a given `η`.
mscale :: MonadDMTC t => Sensitivity -> t ()
mscale η = types %= scale η

zeroAnnotation :: (MonadDMTC t, Default e) => t e
zeroAnnotation = return def

instance Default Sensitivity where
  def = constCoeff (Fin 0)

instance Default Privacy where
  def = (def,def)

instance (CMonoidM t a, CMonoidM t b) => CMonoidM t (a,b)

truncate_impl :: forall f e. (CMonoidM Identity f, CMonoidM Identity e, Eq e) => f -> TypeCtx e -> TypeCtx f
truncate_impl η γ = truncate_annotation <$> γ
   where
      truncate_annotation :: (DMType :& e) -> (DMType :& f)
      truncate_annotation (τ :@ annotation) =
        (case annotation == zeroId of
            True -> τ :@ zeroId
            _    -> τ :@ η)

truncateS :: Sensitivity -> TypeCtxSP -> TypeCtxSP
truncateS η (Left γ) = Left (truncate_impl η γ)
truncateS η (Right γ) = Left (truncate_impl η γ)

truncateP :: Privacy -> TypeCtxSP -> TypeCtxSP
truncateP η (Left γ) = Right (truncate_impl η γ)
truncateP η (Right γ) = Right (truncate_impl η γ)

instance (MonadInternalError t, SemigroupM t a, SemigroupM t b) => SemigroupM t (Either a b) where
  (⋆) (Left a) (Left b) = Left <$> (a ⋆ b)
  (⋆) (Right a) (Right b) = Right <$> (a ⋆ b)
  (⋆) _ _ = internalError "Could not match left and right. (Probably a sensitivity / privacy context mismatch.)"
-- instance (MonoidM t a, MonoidM t b) => MonoidM t (Either a b) where

resetToDefault :: (Default a, Default b) => Either a b -> Either a b
resetToDefault (Left a) = Left def
resetToDefault (Right b) = Right def

-- Given a list of computations in a MonadDMTC monad, it executes all computations
-- on the same input type context, and sums the resulting type contexts.
-- All additional data (constraints, substitutions, metavariable contexts) are passed sequentially.
msum :: (IsT MonadDMTC t) => [t a] -> t [a]
-- msum :: (Show e, IsT MonadDMTC t, MonoidM (t) e, CheckNeutral (t) e) => [t a] -> t [a]
-- msum :: [t a] -> t [a]
msum ms = do
  initΣ <- use types
  f initΣ ms (resetToDefault initΣ)

    where
      -- f :: (Show e, IsT MonadDMTC t, MonoidM (t) e, CheckNeutral (t) e) => TypeCtxSP -> [t a] -> TypeCtxSP -> t [a]
      f :: (IsT MonadDMTC t) => TypeCtxSP -> [t a] -> TypeCtxSP -> t [a]
      f initΣ [] accΣ = types .= accΣ >> return []
      f initΣ (m:ms) accΣ = do
        types .= initΣ
        a <- m
        mΣ <- use types
        m_acc_Σ <- (traceShowId mΣ) ⋆ (traceShowId accΣ)
        as <- f initΣ ms (m_acc_Σ)
        return (a : as)


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

setVar :: MonadDMTC t => Symbol -> DMType :& Sensitivity -> t ()
setVar k v = types %=~ setValueM k (Left v :: Either (DMType :& Sensitivity) (DMType :& Privacy))


-- Normalizes all contexts in our typechecking monad, i.e., applies all available substitutions.
normalizeContext :: (MonadDMTC t) => t ()
normalizeContext = do
  types %=~ normalize
  meta.constraints %=~ normalize


-- Iterates over all constraints which are currently in a "changed" state, and tries to solve them.
-- Returns if no "changed" constraints remains.
-- An unchanged constraint is marked "changed", if it is affected by a new substitution.
-- A changed constraint is marked "unchanged" if it is read by a call to `getUnsolvedConstraintMarkNormal`.
solveAllConstraints :: forall t. (IsT MonadDMTC t) => SolvingMode -> t ()
solveAllConstraints mode = do
  normalizeContext
  openConstr <- getUnsolvedConstraintMarkNormal

  --
  ctx <- use (meta .constraints)
  traceM ("Solving constraints. I have: " <> show ctx <> ".\n Currently looking at: " <> show (fst <$> openConstr))
  --

  case openConstr of
    Nothing -> return ()
    Just (name, (constr)) -> do
      solve mode name constr
      solveAllConstraints mode


-- solvingAllNewConstraints :: (IsT MonadDMTC t) => t a -> t ()
-- solvingAllNewConstraints f = do
--   backup <- clearConstraints
--   res <- f
--   restoreConstraints backup

-- Look up the types and sensitivities/privacies of the variables in `xτs` from the current context.
-- If a variable is not present in Σ (this means it was not used in the lambda body),
-- create a new type/typevar according to type hint given in `xτs` and give it zero annotation
getArgList :: forall t e. (MonadDMTC t, DMExtra e, CMonoidM t e) => [Asgmt JuliaType] -> t [DMType :& e]
getArgList xτs = do
  (γ :: TypeCtxSP) <- use types

  let f :: Asgmt JuliaType -> t (DMType :& e)
      f (x :- τ) = do
        val <- getValueM x γ
        case val of
          -- If the symbol was in the context γ, then we get its type and sensitivity
          Just τe -> cast τe
            --castExtra -- TODO: Cast does not quite work here, because we also have an dmtype inside
          -- if the type hint is DMDUnkown, we just add a typevar. otherwise we can be more specific
          Nothing -> (:@) <$> createDMType τ <*> zero
  xτs' <- mapM f xτs

  -- We have to remove all symbols x from the context
  let deleteSingle :: [TypeCtxSP -> t (TypeCtxSP)]
      deleteSingle = ((\(x :- _) -> deleteValueM x) <$> xτs)
      -- temp = mapM (\(x :- _) -> deleteValueM x) xτs
  γ' <- composeFunM deleteSingle γ

  types .= γ'

  return xτs'

removeVar :: forall e t. (MonadDMTC t, DMExtra e) => Symbol -> t (Maybe (DMType :& e))
removeVar x =  do
  -- (γ :: Ctx Symbol (DMType :& e)) <- use types
  γ <- use types
  v <- getValueM x γ
  γ' <- deleteValueM x γ
  types .= γ'
  cast v


