
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
  where f (WithRelev i x) = WithRelev i (η :↷: x)
  -- where f (WithRelev i (τ :@ s)) = WithRelev i (τ :@ (η ⋅! s))
scale η (Right γ) = Right (f <$> γ)
  where f (WithRelev i x) = WithRelev i (η :↷: x)
  -- where f :: WithRelev AnnP -> WithRelev AnnP
  --       f (WithRelev i (τ :@ (δ,ε))) = WithRelev i (τ :@ (η ⋅! δ, η ⋅! ε))

-- Scales the current type context living in our typechecking-state monad by a given `η`.
mscale :: MonadDMTC t => Sensitivity -> t ()
mscale η = types %= scale η

zeroWithRelevation :: (MonadDMTC t, Default e) => t e
zeroWithRelevation = return def

instance Default Sensitivity where
  def = constCoeff (Fin 0)

instance Default Privacy where
  def = (def,def)

inftyS :: Sensitivity
inftyS = constCoeff Infty

inftyP :: Privacy
inftyP = (constCoeff Infty, constCoeff Infty)

instance (CMonoidM t a, CMonoidM t b) => CMonoidM t (a,b)

-- truncate_impl :: forall f e. (CMonoidM Identity f, CMonoidM Identity e, Eq e) => f -> TypeCtx e -> TypeCtx f
truncate_impl :: forall f e. RealizeAnn f -> TypeCtx e -> TypeCtx f
truncate_impl η γ = truncate_annotation <$> γ
   where
      truncate_annotation :: (WithRelev e) -> (WithRelev f)
      truncate_annotation (WithRelev i x) = WithRelev i (Trunc η x)
      -- truncate_annotation (WithRelev i (τ :@ annotation)) =
      --   (case annotation == zeroId of
      --       True -> WithRelev i (τ :@ zeroId)
      --       _    -> WithRelev i (τ :@ η))

truncateS :: Sensitivity -> TypeCtxSP -> TypeCtxSP
truncateS η (Left γ) = Left (truncate_impl η γ)
truncateS η (Right γ) = Left (truncate_impl η γ)

truncateP :: Privacy -> TypeCtxSP -> TypeCtxSP
truncateP η (Left γ) = Right (truncate_impl η γ)
truncateP η (Right γ) = Right (truncate_impl η γ)

-- Truncates the current type context living in our typechecking-state monad by a given Sensitivity `η`.
mtruncateS :: MonadDMTC t => Sensitivity -> t ()
mtruncateS η = types %= truncateS η

-- Truncates the current type context living in our typechecking-state monad by a given Privacy `η`.
mtruncateP :: MonadDMTC t => Privacy -> t ()
mtruncateP η = types %= truncateP η

instance (MonadInternalError t, SemigroupM t a, SemigroupM t b) => SemigroupM t (Either a b) where
  (⋆) (Left a) (Left b) = Left <$> (a ⋆ b)
  (⋆) (Right a) (Right b) = Right <$> (a ⋆ b)
  (⋆) _ _ = error "Could not match left and right. (Probably a sensitivity / privacy context mismatch.)"
--  (⋆) _ _ = internalError "Could not match left and right. (Probably a sensitivity / privacy context mismatch.)"
-- instance (MonoidM t a, MonoidM t b) => MonoidM t (Either a b) where

resetToDefault :: (Default a, Default b) => Either a b -> Either a b
resetToDefault (Left a) = Left def
resetToDefault (Right b) = Right def

-- Given a list of computations in a MonadDMTC monad, it executes all computations
-- on the same input type context, and sums the resulting type contexts.
-- All additional data (constraints, substitutions, metavariable contexts) are passed sequentially.
msum :: (IsT MonadDMTC t) => TypeCtxSP -> [t a] -> t [a]
-- msum :: (Show e, IsT MonadDMTC t, MonoidM (t) e, CheckNeutral (t) e) => [t a] -> t [a]
-- msum :: [t a] -> t [a]
msum emptyΣ ms = do
  initΣ <- use types
  f initΣ ms (emptyΣ)

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

msumP = msum (Right def)
msumS = msum (Left def)

msumTup :: (IsT MonadDMTC t) => (t a, t b) -> t (a,b)
msumTup (ma, mb) = do
  tΣ <- use types
  types .= tΣ
  a <- ma
  aΣ <- use types

  types .= tΣ
  b <- mb
  bΣ <- use types

  resΣ <- (aΣ ⋆ bΣ)
  types .= resΣ

  return (a , b)


msum3Tup :: (IsT MonadDMTC t) => (t a, t b, t c) -> t (a,b,c)
msum3Tup (ma, mb, mc) = do
  tΣ <- use types
  types .= tΣ
  a <- ma
  aΣ <- use types

  types .= tΣ
  b <- mb
  bΣ <- use types

  types .= tΣ
  c <- mc
  cΣ <- use types

  m_acc_Σ <- (aΣ ⋆ bΣ)
  resΣ <- (m_acc_Σ ⋆ cΣ)
  types .= resΣ

  return (a, b, c)



setVarS :: MonadDMTC t => Symbol -> WithRelev AnnS -> t ()
setVarS k v = types %=~ setValueM k (Left v :: Either (WithRelev AnnS) (WithRelev AnnP))

setVarP :: MonadDMTC t => Symbol -> WithRelev AnnP -> t ()
setVarP k v = types %=~ setValueM k (Right v :: Either (WithRelev AnnS) (WithRelev AnnP))



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
          Just τe -> ((:@) <$> createDMType τ <*> zero)
--sndAnnI τe
          -- if the type hint is DMDUnkown, we just add a typevar. otherwise we can be more specific
          Nothing -> ((:@) <$> createDMType τ <*> zero)
  xτs' <- mapM f xτs

  -- We have to remove all symbols x from the context
  let deleteWithRelev :: [TypeCtxSP -> t (TypeCtxSP)]
      deleteWithRelev = ((\(x :- _) -> deleteValueM x) <$> xτs)
      -- temp = mapM (\(x :- _) -> deleteValueM x) xτs
  γ' <- composeFunM deleteWithRelev γ

  types .= γ'

  return xτs'

removeVar :: forall e t. (DMExtra e, MonadDMTC t) => Symbol -> t (WithRelev e)
removeVar x =  do
  -- (γ :: Ctx Symbol (DMType :& e)) <- use types
  γ <- use types
  v <- getValueM x γ
  vr <- case v of
     Just vv -> cast vv
     Nothing -> WithRelev IsRelevant <$> ((zeroId :↷:) <$> newVar) -- ((:@) <$> newVar <*> return zeroId)
  γ' <- deleteValueM x γ
  types .= γ'
  return vr

lookupVar :: forall e t. (DMExtra e, MonadDMTC t) => Symbol -> t (Maybe (WithRelev e))
lookupVar x =  do
  γ <- use types
  v <- getValueM x γ
  cast v

getInteresting :: MonadDMTC t => t ([Symbol],[DMType],[Privacy])
getInteresting = return ([],[],[]) --do
   -- γ <- use types
   -- h <- case γ of
   --         Left _ -> throwError (ImpossibleError "getInteresting called on sensitivity context.")
   --         Right (Ctx (MonCom h')) -> return (H.toList h')
   -- let f :: MonadDMTC t => [(Symbol, WithRelev AnnP)] -> t ([Symbol],[DMType],[Privacy])
   --     f lst = case lst of
   --                ((x, (WithRelev i (τ :@ p))) : xτs) -> case i of
   --                      IsRelevant -> do
   --                         (xs, τs, ps) <- f xτs
   --                         return ((x:xs),(τ:τs),(p:ps))
   --                      NotRelevant -> f xτs
   --                [] -> return ([],[],[])
   -- f h

---------------------------------------------------------------------------
-- Algebraic instances for annot

-- TODO: If we are going to implement 'Multiple', then this instance has to change
-- instance (Show e, IsT MonadDMTC t, SemigroupM t e) => SemigroupM t (WithRelev e) where
instance (IsT MonadDMTC t) => SemigroupM t (WithRelev e) where
  (⋆) (WithRelev i e) (WithRelev j f) = WithRelev (i <> j) <$> (e ⋆ f)

instance (IsT MonadDMTC t, DMExtra e) => MonoidM t (WithRelev e) where
  neutral = WithRelev IsRelevant <$> neutral

instance (IsT MonadDMTC t, DMExtra e) => CheckNeutral t (WithRelev e) where
  checkNeutral (WithRelev i a) = checkNeutral a

