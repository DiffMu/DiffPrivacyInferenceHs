
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadTC
import DiffMu.Core.Term
import DiffMu.Core.MonadicPolynomial2
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
    _sensVars :: NameCtx,
    _typeVars :: NameCtx,
    _constraintVars :: NameCtx
  }
  deriving (Generic)

data Meta0Ctx extra = Meta0Ctx
  {
    _sensSubs :: Subs SVar Sensitivity,
    _typeSubs :: Subs TVar DMType,
    _constraints :: MonCom (Solvable' TC) Symbol,
    _types :: TypeCtx extra
  }
  deriving (Generic)

data Full extra = Full
  {
    _meta1 :: Meta1Ctx,
    _meta0 :: Meta0Ctx extra
  }
  deriving (Generic)

newtype TCT m extra a = TCT {runTCT :: (StateT (Full extra) (ExceptT DMException m) a)}
  deriving (Functor, Applicative, Monad, MonadState (Full extra), MonadError DMException)

-- liftTC :: TC e a -> TCT m e a
-- liftTC = _

type TC = TCT Identity

type STC a = TC Sensitivity a
type PTC a = TC Privacy a

$(makeLenses ''Meta1Ctx)
$(makeLenses ''Meta0Ctx)
$(makeLenses ''Full)


instance Show Meta1Ctx where
  show (Meta1Ctx s t c) =  "- sens vars: " <> show s <> "\n"
                        <> "- type vars: " <> show t <> "\n"
                        <> "- cnst vars: " <> show c <> "\n"

instance Show e => Show (Meta0Ctx e) where
  show (Meta0Ctx sσ tσ cs γ) = "- sens subs:   " <> show sσ <> "\n"
                            <> "- type subs:   " <> show tσ <> "\n"
                            <> "- constraints: " <> show cs <> "\n"
                            <> "- types:       " <> show γ <> "\n"
instance Show e => Show (Full e) where
  show (Full m1 m0) = "\nMeta1:\n" <> show m1 <> "\nMeta0:\n" <> show m0 <> "\n"

-- modify02 :: MonadDMTC e t => (Meta0Ctx e -> Meta0Ctx e) -> t e
-- modify02 f = modify (\s -> s {meta0 = f (meta0 s)})

-- modify0 :: MonadDMTC e t => (Meta0Ctx e -> Meta0Ctx e) -> t e ()
-- modify0 f = modify (\s -> s {meta0 = f (meta0 s)})

-- modify1 :: MonadDMTC e t => (Meta1Ctx -> Meta1Ctx) -> t e ()
-- modify1 f = modify (\s -> s {meta1 = f (meta1 s)})

-- state0 :: MonadDMTC e t => (Meta0Ctx e -> (a, Meta0Ctx e)) -> t e a
-- state0 f = state (\s -> let (a,b) = f (meta0 s)
--                         in (a, s {meta0 = b}))

-- state1 :: MonadDMTC e t => (Meta1Ctx -> (a, Meta1Ctx)) -> t e a
-- state1 f = state (\s -> let (a,b) = f (meta1 s)
--                         in (a, s {meta1 = b}))

instance Default (Meta1Ctx) where
instance Default (Meta0Ctx e) where
instance Default (Full e) where

  -- Full ::  NameCtx -> NameCtx -> NameCtx -> Subs DMType -> ConstraintOlds -> Ctx extra -> Full extra
  -- deriving (Generic, Show)

-- type TC extra = StateT (Full extra) (Except DMException)
-- newtype TC extra a = TC {runTC :: (StateT (Full extra) (Except DMException) a)}
--   deriving (Functor, Applicative, Monad, MonadState (Full extra), MonadError DMException)



instance Monad m => MonadTC TVar DMType (TCT m e) where
  getSubs = view (meta0.typeSubs) <$> get

instance Monad m => MonadTC SVar Sensitivity (TCT m e) where
  getSubs = view (meta0.sensSubs) <$> get

getUnsolved :: MonCom (Solvable' TC) Symbol -> Maybe (Symbol, Solvable' TC)
getUnsolved = undefined

instance Monad m => MonadConstraint' TC (TCT m) where
  type ConstrVar TC = Symbol
  addConstraint' c = undefined -- modify0 (\f -> f {constraints = MonCom [(c,"hello")]}) -- --modify0 (\s -> s {constraints = _}) -- 
  getUnsolvedConstraint' = getUnsolved <$> view (meta0.constraints) <$> get
  addConstraint'2 c = return ()

instance Monad m => MonadWatch (TCT m e) where

instance Monad m => Solve (TCT m e) IsLessEqual (DMType,DMType) where
  solve_ (IsLessEqual (a,b)) = undefined

class (MonadImpossible (t e), MonadWatch (t e),
       MonadTC TVar DMType (t e), MonadTC SVar Sensitivity (t e),
       MonadState (Full e) (t e),
       MonadError DMException (t e)) => MonadDMTC e t where
-- instance MonadDMTC e (TC) where
instance Monad m => MonadDMTC e (TCT m) where

instance Monad m => MonadImpossible (TCT m e) where
  impossible err = throwError (ImpossibleError err)

instance MonadDMTC e t => Normalize (t e) DMType where
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

instance MonadDMTC e t => Normalize (t e) Sensitivity where
  normalize n =
    do σ <- getSubs @SVar @Sensitivity
       σ ↷ n


newType :: MonadDMTC e t => Text -> t e DMType
newType hint = meta1.typeVars %%= (first TVar . newName hint)
  -- where f names = let (τ , names') = newName hint names
  --                 in (TVar τ, names')


  -- state (over meta0 f)
  -- where f (Meta1Ctx s t c) =
  --         let (τ , s') = newName hint s
  --         in (TVar τ , Meta1Ctx s t c)


setVar :: MonadDMTC e t => Symbol -> DMType :& e -> t e ()
setVar k v = meta0.types %= setValue k v










