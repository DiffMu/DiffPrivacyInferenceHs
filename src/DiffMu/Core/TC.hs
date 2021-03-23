
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

data Full extra = Full
  {
    sensVars :: NameCtx,
    typeVars :: NameCtx,
    constraintVars :: NameCtx,
    sensSubs :: Subs SVar Sensitivity,
    typeSubs :: Subs TVar DMType,
    constraints :: MonCom (Solvable' TC) Symbol,
    context :: Ctx extra
  }
  deriving (Generic, Show)

instance Default (Full e) where

  -- Full ::  NameCtx -> NameCtx -> NameCtx -> Subs DMType -> ConstraintOlds -> Ctx extra -> Full extra
  -- deriving (Generic, Show)

-- type TC extra = StateT (Full extra) (Except DMException)
newtype TC extra a = TC {runTC :: (StateT (Full extra) (Except DMException) a)}
  deriving (Functor, Applicative, Monad, MonadState (Full extra), MonadError DMException)


type STC a = TC Sensitivity a
type PTC a = TC Privacy a


instance MonadTC TVar DMType (TC e) where
  getSubs = typeSubs <$> get

instance MonadTC SVar Sensitivity (TC e) where
  getSubs = sensSubs <$> get

getUnsolved :: MonCom (Solvable' TC) Symbol -> Maybe (Symbol, Solvable' TC)
getUnsolved = undefined

instance MonadConstraint' TC where
  type ConstrVar TC = Symbol
  addConstraint' c = modify (\f -> f {constraints = MonCom [(c,"hello")]})
  getUnsolvedConstraint' = getUnsolved <$> constraints <$> get

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

instance Monad t => Normalize t DMNumType where
  normalize = pure

instance MonadDMTC t => Normalize t Sensitivity where
  normalize n =
    do σ <- getSubs @SVar @Sensitivity
       σ ↷ n














       -- σ <- getSubstitutions @_ @Sensitivity
       -- σ ↷ n







