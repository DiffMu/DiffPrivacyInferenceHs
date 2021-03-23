
module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadTC
import DiffMu.Core.Term
import DiffMu.Core.MonadicPolynomial
import DiffMu.Core.Symbolic

type TVar = Symbol
type SVar = Symbol

instance Substitute TVar DMType DMType where

instance Term TVar DMType where
  var x = TVar x


  -- substituteAll σ (VarNum t) = pure $ VarNum t
  -- substituteAll σ (ConstNum t s) = pure $ ConstNum t s
  -- substituteAll σ (TVar a) = σ a
  -- substituteAll σ (t :->: s) = (:->:) <$> (σ ↷ t) <*> substituteAll σ s

-- instance (ModuleM t m a, ModuleM t m b) => ModuleM t m (a :& b) where

instance Substitute SVar Sensitivity Sensitivity where
  substitute σs s = substitute f s
    where f (HonestVar a) = σs (a)
          f b = pure $ var (b)


instance Term SVar Sensitivity where

type TSubs = Subs DMType
type SSubs = Subs Sensitivity

data Meta1Ctx = Meta1Ctx
  {
    sensVars :: NameCtx,
    typeVars :: NameCtx,
    constraintVars :: NameCtx
  }
  deriving (Generic, Show)

data Meta0Ctx extra = Meta0Ctx
  {
    sensSubs :: Subs SVar Sensitivity,
    typeSubs :: Subs TVar DMType,
    constraints :: MonCom (Solvable' TC) Symbol,
    context :: Ctx extra
  }
  deriving (Generic, Show)

data Full extra = Full
  {
    meta1 :: Meta1Ctx,
    meta0 :: Meta0Ctx extra
  }
  deriving (Generic, Show)

modify0 :: (Meta0Ctx e -> Meta0Ctx e) -> TC e ()
modify0 f = modify (\s -> s {meta0 = f (meta0 s)})

modify1 :: (Meta1Ctx -> Meta1Ctx) -> TC e ()
modify1 f = modify (\s -> s {meta1 = f (meta1 s)})

state0 :: (Meta0Ctx e -> (a, Meta0Ctx e)) -> TC e a
state0 f = state (\s -> let (a,b) = f (meta0 s)
                        in (a, s {meta0 = b}))

state1 :: (Meta1Ctx -> (a, Meta1Ctx)) -> TC e a
state1 f = state (\s -> let (a,b) = f (meta1 s)
                        in (a, s {meta1 = b}))

instance Default (Meta1Ctx) where
instance Default (Meta0Ctx e) where
instance Default (Full e) where

  -- Full ::  NameCtx -> NameCtx -> NameCtx -> Subs DMType -> ConstraintOlds -> Ctx extra -> Full extra
  -- deriving (Generic, Show)

-- type TC extra = StateT (Full extra) (Except DMException)
newtype TC extra a = TC {runTC :: (StateT (Full extra) (Except DMException) a)}
  deriving (Functor, Applicative, Monad, MonadState (Full extra), MonadError DMException)


type STC a = TC Sensitivity a
type PTC a = TC Privacy a


instance MonadTC TVar DMType (TC e) where
  getSubs = typeSubs . meta0 <$> get

instance MonadTC SVar Sensitivity (TC e) where
  getSubs = sensSubs . meta0 <$> get

getUnsolved :: MonCom (Solvable' TC) Symbol -> Maybe (Symbol, Solvable' TC)
getUnsolved = undefined

instance MonadConstraint' TC where
  type ConstrVar TC = Symbol
  addConstraint' c = modify0 (\f -> f {constraints = MonCom [(c,"hello")]})
  getUnsolvedConstraint' = getUnsolved . constraints . meta0 <$> get

instance MonadWatch (TC e) where


class (MonadImpossible t, MonadWatch t, MonadTC TVar DMType t, MonadTC SVar Sensitivity t) => MonadDMTC t where
instance MonadDMTC (TC e) where

instance MonadImpossible (TC e) where
  impossible err = throwError (ImpossibleError err)

instance MonadDMTC t => Normalize t DMType where
  normalize n =
    do σ <- getSubs @TVar @DMType
       n₂ <- σ ↷ n
       σ <- getSubs @SVar @Sensitivity
       -- n₃ <- σ ↷ n₂
       undefined

instance (Normalize t a, Normalize t b) => Normalize t (a :& b) where
  normalize (a :@ b) = (:@) <$> normalize a <*> normalize b

instance (Normalize t a) => Normalize t [a] where
  normalize as = mapM normalize as

-- instance Monad t => Normalize t DMNumType where
--   normalize = pure

instance MonadDMTC t => Normalize t Sensitivity where
  normalize n =
    do σ <- getSubs @SVar @Sensitivity
       σ ↷ n


newType :: Symbol -> TC e DMType
newType hint = state1 f
  where f (Meta1Ctx s t c) =
          let (τ , s') = newName hint s
          in (TVar τ , Meta1Ctx s t c)











       -- σ <- getSubstitutions @_ @Sensitivity
       -- σ ↷ n







