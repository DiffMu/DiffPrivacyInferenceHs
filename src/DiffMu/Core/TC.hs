
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadTC
import DiffMu.Core.Term
import DiffMu.Core.MonadicPolynomial2
import DiffMu.Core.Symbolic

instance (Substitute v x a, Substitute v x b) => Substitute v x (a :& b) where
  substitute σs (a :@ b) = (:@) <$> substitute σs a <*> substitute σs b

instance Substitute v x a => Substitute v x [a] where
  substitute σs xs = mapM (substitute σs) xs

instance Substitute TVar DMType Sensitivity where
  substitute σs η = pure η

instance Substitute TVar DMType DMType where
  substitute σs DMInt = pure DMInt
  substitute σs DMReal = pure DMReal
  substitute σs (Const η τ) = Const <$> substitute σs η <*> substitute σs τ
  substitute σs (TVar x) = σs x
  substitute σs (τ1 :->: τ2) = (:->:) <$> substitute σs τ1 <*> substitute σs τ2

instance Substitute SVar Sensitivity DMType where
  substitute σs DMInt = pure DMInt
  substitute σs DMReal = pure DMReal
  substitute σs (Const η τ) = Const <$> substitute σs η <*> substitute σs τ
  substitute σs (TVar x) = pure (TVar x)
  substitute σs (τ1 :->: τ2) = (:->:) <$> substitute σs τ1 <*> substitute σs τ2


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
  var v = var (HonestVar v)

type TSubs = Subs DMType
type SSubs = Subs Sensitivity

-- data Meta1Ctx = Meta1Ctx
--   {
--     _sensVars :: NameCtx,
--     _typeVars :: NameCtx,
--     _constraintVars :: NameCtx
--   }
--   deriving (Generic)

data Tag = DM

data KindedNameCtx ks = KindedNameCtx NameCtx ks
  deriving (Generic)
type ConstraintCtx = KindedNameCtx (Ctx Symbol (Solvable' TC))

instance Show ks => Show (KindedNameCtx ks) where
  show (KindedNameCtx _ kinds) = show kinds
instance Default ks => Default (KindedNameCtx ks)

newKindedName :: DictLike Symbol k ks => Text -> k -> KindedNameCtx ks -> (Symbol, KindedNameCtx ks)
newKindedName hint k (KindedNameCtx names kinds) =
  let (name, names') = newName hint names
      kinds' = setValue name k kinds
  in (name, KindedNameCtx names' kinds')

-- data Meta0Ctx extra = Meta0Ctx
--   {
--     _sensSubs :: Subs SVar Sensitivity,
--     _typeSubs :: Subs TVar DMType,
--     _constraints :: ConstraintCtx, -- MonCom (Solvable'' TCT) Symbol,
--   }
--   deriving (Generic)

data MetaCtx extra = MetaCtx
  {
    _sensVars :: NameCtx,
    _typeVars :: NameCtx,
    _constraintVars :: NameCtx,
    _sensSubs :: Subs SVar Sensitivity,
    _typeSubs :: Subs TVar DMType,
    _constraints :: ConstraintCtx -- MonCom (Solvable'' TCT) Symbol,
  }
  deriving (Generic)

data Full extra = Full
  {
    -- _meta1 :: Meta1Ctx,
    -- _meta0 :: Meta0Ctx extra
    _meta :: MetaCtx extra,
    _types :: TypeCtx extra
  }
  deriving (Generic)

newtype TCT m extra a = TCT {runTCT :: (StateT (Full extra) (ExceptT DMException m) a)}
  deriving (Functor, Applicative, Monad, MonadState (Full extra), MonadError DMException)

-- liftTC :: TC e a -> TCT m e a
-- liftTC = _

type TC = TCT Identity

type STC a = TC Sensitivity a
type PTC a = TC Privacy a

-- $(makeLenses ''Meta1Ctx)
-- $(makeLenses ''Meta0Ctx)
$(makeLenses ''MetaCtx)
$(makeLenses ''Full)


-- instance Show Meta1Ctx where
--   show (Meta1Ctx s t c) =  "- sens vars: " <> show s <> "\n"
--                         <> "- type vars: " <> show t <> "\n"
--                         <> "- cnst vars: " <> show c <> "\n"

-- instance Show e => Show (Meta0Ctx e) where
--   show (Meta0Ctx sσ tσ cs γ) = "- sens subs:   " <> show sσ <> "\n"
--                             <> "- type subs:   " <> show tσ <> "\n"
--                             <> "- constraints: " <> show cs <> "\n"
--                             <> "- types:       " <> show γ <> "\n"

instance Show (MetaCtx e) where
  show (MetaCtx s t c sσ tσ cs) =
       "- sens vars: " <> show s <> "\n"
    <> "- type vars: " <> show t <> "\n"
    <> "- cnst vars: " <> show c <> "\n"
    <> "- sens subs:   " <> show sσ <> "\n"
    <> "- type subs:   " <> show tσ <> "\n"
    <> "- constraints: " <> show cs <> "\n"
    -- <> "- types:       " <> show γ <> "\n"

instance Show e => Show (Full e) where
  show (Full m γ) = "\nMeta:\n" <> show m <> "\nTypes:\n" <> show γ <> "\n"

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

-- instance Default (Meta1Ctx) where
-- instance Default (Meta0Ctx e) where
instance Default (MetaCtx e) where
instance Default (Full e) where

  -- Full ::  NameCtx -> NameCtx -> NameCtx -> Subs DMType -> ConstraintOlds -> Ctx extra -> Full extra
  -- deriving (Generic, Show)

-- type TC extra = StateT (Full extra) (Except DMException)
-- newtype TC extra a = TC {runTC :: (StateT (Full extra) (Except DMException) a)}
--   deriving (Functor, Applicative, Monad, MonadState (Full extra), MonadError DMException)



instance Monad m => MonadTC TVar DMType (TCT m e) where
  getSubs = view (meta.typeSubs) <$> get
  addSub σ = do
    σs <- use (meta.typeSubs)
    σs' <- σs ⋆ singletonSub σ
    meta.typeSubs .= σs'

instance Monad m => MonadTC SVar Sensitivity (TCT m e) where
  getSubs = view (meta.sensSubs) <$> get
  addSub σ = do
    σs <- use (meta.sensSubs)
    σs' <- σs ⋆ singletonSub σ
    meta.sensSubs .= σs'

getUnsolved :: MonCom (Solvable' TC) Symbol -> Maybe (Symbol, Solvable' TC)
getUnsolved = undefined

instance Monad m => MonadConstraint' Symbol TC (TCT m e) where
  -- type ConstrVar TC = Symbol
  addConstraint' c = meta.constraints %%= newKindedName "constr" c
  -- modify0 (\f -> f {constraints = MonCom [(c,"hello")]}) -- --modify0 (\s -> s {constraints = _}) -- 
  getUnsolvedConstraint' = undefined -- getUnsolved <$> view (meta0.constraints) <$> get
  -- addConstraint'2 c = return ()

-- instance MonadConstraint'' Symbol TCT where
--   addConstraint'' c = meta0.constraints %%= newKindedName "" (Solvable'' c)

-- instance Monad t => MonadConstraintTag DM Symbol (TCT t e) where
--   addConstraintTag c = meta0.constraints %%= newKindedName "" (SolvableTag c)

-- instance Monad t => MonadConstraintDiff Symbol (TC e) (TCT t e) where
--   addConstraintDiff c = _ -- meta0.constraints %%= newKindedName "" (SolvableTag c)






instance Monad m => MonadWatch (TCT m e) where

instance Solve (TC e) IsLessEqual (DMType,DMType) where
  solve_ (IsLessEqual (a,b)) = undefined

class (MonadImpossible (t e), MonadWatch (t e),
       MonadTC TVar DMType (t e), MonadTC SVar Sensitivity (t e),
       MonadState (Full e) (t e),
       MonadError DMException (t e),
       MonadConstraint' Symbol (TC) (t e)) => MonadDMTC e t where
-- instance MonadDMTC e (TC) where
instance Monad m => MonadDMTC e (TCT m) where



instance Monad m => MonadImpossible (TCT m e) where
  impossible err = throwError (ImpossibleError err)

instance MonadDMTC e t => Normalize (t e) DMType where
  normalize n =
    do σ <- getSubs @TVar @DMType
       n₂ <- σ ↷ n
       σ <- getSubs @SVar @Sensitivity
       n₃ <- σ ↷ n₂
       return n₃

instance (Normalize t a, Normalize t b) => Normalize t (a :& b) where
  normalize (a :@ b) = (:@) <$> normalize a <*> normalize b

instance (Normalize t a) => Normalize t [a] where
  normalize as = mapM normalize as

instance (Normalize t a, Normalize t b, Normalize t c) => Normalize t (a, b, c) where
  normalize (a,b,c) = (,,) <$> normalize a <*> normalize b <*> normalize c
-- instance Monad t => Normalize t DMNumType where
--   normalize = pure

instance MonadDMTC e t => Normalize (t e) Sensitivity where
  normalize n =
    do σ <- getSubs @SVar @Sensitivity
       σ ↷ n

instance Monad t => Normalize t Symbol where
  normalize = pure

instance MonadDMTC e t => Normalize (t e) DMTypeOp where
  normalize (Unary op τ res) = Unary op <$> normalize τ <*> normalize res
  normalize (Binary op τ res) = Binary op <$> normalize τ <*> normalize res
  normalize (Ternary op τ res) = Ternary op <$> normalize τ <*> normalize res
  -- normalize (Binary op σ τ) = Binary op <$> normalize σ <*> normalize τ
  -- normalize (Ternary op ρ σ τ) = Ternary op <$> normalize ρ <*> normalize σ <*> normalize τ

instance MonadDMTC e t => Solve (t e) (IsTypeOpResult) DMTypeOp where
  solve_ (IsTypeOpResult (Unary op τ res)) = undefined
  solve_ (IsTypeOpResult (Binary op τ res)) = undefined
  solve_ (IsTypeOpResult (Ternary op τ res)) = undefined
  -- solve_ (Constr (Binary op σ τ)) = undefined
  -- solve_ (Constr (Ternary op ρ σ τ)) = undefined



newTVar :: MonadDMTC e t => Text -> t e TVar
newTVar hint = meta.typeVars %%= (newName hint)

newSVar :: MonadDMTC e t => Text -> t e SVar
newSVar hint = meta.sensVars %%= (newName hint)

  -- where f names = let (τ , names') = newName hint names
  --                 in (TVar τ, names')


  -- state (over meta0 f)
  -- where f (Meta1Ctx s t c) =
  --         let (τ , s') = newName hint s
  --         in (TVar τ , Meta1Ctx s t c)


setVar :: MonadDMTC e t => Symbol -> DMType :& e -> t e ()
setVar k v = types %= setValue k v










