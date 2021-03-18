
module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadTC
import DiffMu.Core.Term
import DiffMu.Core.MonadicPolynomial

instance Term DMType where
  type Var DMType = Symbol
  var x = TVar x

  substituteAll σ (VarNum t) = pure $ VarNum t
  substituteAll σ (ConstNum t s) = pure $ ConstNum t s
  substituteAll σ (TVar a) = σ a
  substituteAll σ (t :->: s) = (:->:) <$> (σ ↷ t) <*> substituteAll σ s

-- instance (ModuleM t m a, ModuleM t m b) => ModuleM t m (a :& b) where


type TSubs = Subs DMType
type SSubs = Subs Sensitivity

data Full extra = Full
  {
    sensVars :: NameCtx,
    typeVars :: NameCtx,
    constraintVars :: NameCtx,
    sensSubs :: Subs Sensitivity,
    typeSubs :: Subs DMType,
    constraints :: MonCom (Solvable' TC) Symbol,
    context :: Ctx extra
  }
  -- Full ::  NameCtx -> NameCtx -> NameCtx -> Subs DMType -> ConstraintOlds -> Ctx extra -> Full extra
  -- deriving (Generic, Show)

-- type TC extra = StateT (Full extra) (Except DMException)
newtype TC extra a = TC (StateT (Full extra) (Except DMException) a)
  deriving (Functor, Applicative, Monad, MonadState (Full extra), MonadError DMException)


type STC a = TC Sensitivity a
type PTC a = TC Privacy a


instance MonadTC DMType (TC e) where
  getSubs = typeSubs <$> get

instance MonadTC Sensitivity (TC e) where
  getSubs = sensSubs <$> get

getUnsolved :: MonCom (Solvable' TC) Symbol -> Maybe (Symbol, Solvable' TC)
getUnsolved = undefined

instance MonadConstraint' TC where
  type ConstrVar TC = Symbol
  addConstraint' c = modify (\f -> f {constraints = MonCom [(c,"hello")]})
  getUnsolvedConstraint' = getUnsolved <$> constraints <$> get




instance MonadImpossible (TC e) where
  impossible err = throwError (ImpossibleError err)

instance Normalize (TC e) DMType where
  normalize n =
    do σ <- getSubs @DMType
       σ ↷ n
       σ <- getSubs @Sensitivity
       σ ↷ n

instance (Normalize t a, Normalize t b) => Normalize t (a :& b) where
  normalize (a :@ b) = (:@) <$> normalize a <*> normalize b

instance (Normalize t a) => Normalize t [a] where
  normalize as = mapM normalize as

instance Monad t => Normalize t DMNumType where
  normalize = pure

instance Normalize (TC e) Sensitivity where
  normalize n =
    do σ <- getSubs @Sensitivity
       σ ↷ n













       -- σ <- getSubstitutions @_ @Sensitivity
       -- σ ↷ n







