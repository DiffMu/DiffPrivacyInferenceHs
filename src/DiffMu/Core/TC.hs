
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}


module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Symbolic

import qualified Data.HashMap.Strict as H

import Debug.Trace

instance (Substitute v x a, Substitute v x b) => Substitute v x (a :& b) where
  substitute σs (a :@ b) = (:@) <$> substitute σs a <*> substitute σs b

instance Substitute v x a => Substitute v x [a] where
  substitute σs xs = mapM (substitute σs) xs

instance Substitute TVarOf DMTypeOf Sensitivity where
  substitute σs η = pure η

instance Substitute TVarOf DMTypeOf (DMTypeOf k) where
  substitute σs DMInt = pure DMInt
  substitute σs DMReal = pure DMReal
  substitute σs (Numeric τ) = Numeric <$> substitute σs τ
  substitute σs (NonConst τ) = NonConst <$> substitute σs τ
  substitute σs (Const η τ) = Const <$> substitute σs η <*> substitute σs τ
  substitute σs (TVar x) = σs x
  substitute σs (τ1 :->: τ2) = (:->:) <$> substitute σs τ1 <*> substitute σs τ2
  substitute σs (DMTup τs) = DMTup <$> substitute σs τs

instance Substitute SVarOf SensitivityOf (DMTypeOf k) where
  substitute σs DMInt = pure DMInt
  substitute σs DMReal = pure DMReal
  substitute σs (Numeric τ) = Numeric <$> substitute σs τ
  substitute σs (NonConst τ) = NonConst <$> substitute σs τ
  substitute σs (Const η τ) = Const <$> substitute σs η <*> substitute σs τ
  substitute σs (TVar x) = pure (TVar x)
  substitute σs (τ1 :->: τ2) = (:->:) <$> substitute σs τ1 <*> substitute σs τ2
  substitute σs (DMTup τs) = DMTup <$> substitute σs τs


instance Term TVarOf DMTypeOf where
  var x = TVar x




  -- substituteAll σ (VarNum t) = pure $ VarNum t
  -- substituteAll σ (ConstNum t s) = pure $ ConstNum t s
  -- substituteAll σ (TVar a) = σ a
  -- substituteAll σ (t :->: s) = (:->:) <$> (σ ↷ t) <*> substituteAll σ s

-- instance (ModuleM t m a, ModuleM t m b) => ModuleM t m (a :& b) where

instance Substitute SVarOf SensitivityOf (SensitivityOf k) where
  substitute (σs :: forall k. (Typeable k) => SVarOf k -> t (SensitivityOf k)) s = substitute f s
    where f :: (Typeable l) => SymVar l -> t (SensitivityOf l)
          f (HonestVar a) = σs (a)
          f b = pure $ var (b)


instance Term SVarOf SensitivityOf where
  var (v) = var (HonestVar v)

type TSubs = Subs DMTypeOf
type SSubs = Subs SensitivityOf

-- data Meta1Ctx = Meta1Ctx
--   {
--     _sensVars :: NameCtx,
--     _typeVars :: NameCtx,
--     _constraintVars :: NameCtx
--   }
--   deriving (Generic)

class (MonadImpossible (t), MonadWatch (t),
       MonadTerm DMTypeOf (t), MonadTerm SensitivityOf (t),
       MonadState (Full) (t),
       MonadError DMException (t),
       MonadInternalError t,
       -- MonadConstraint' Symbol (TC) (t),
       -- MonadConstraint Symbol (MonadDMTC) (t),
       MonadConstraint (MonadDMTC) (t)
       -- LiftTC t
      ) => MonadDMTC t where

data Tag = DM

data AnnNameCtx ks = AnnNameCtx NameCtx ks
  deriving (Generic)
-- data DMSolvable where
--   DMSolvable :: (forall e t. MonadDMTC t => Solve (t) c a) => c a -> DMSolvable

-- instance Show DMSolvable where
--   show a = "some constraint"

-- instance MonadDMTC t => Normalize (t) DMSolvable where
--   -- normalize (DMSolvable c) = DMSolvable <$> normalize c

data Watched a = Watched Changed a

instance Show a => Show (Watched a) where
  show (Watched IsChanged a) = "*" <> show a
  show (Watched NotChanged a) = show a

instance (MonadWatch t, Normalize t a) => Normalize t (Watched a) where
  normalize (Watched c a) =
    do resetChanged
       a' <- normalize a
       newc <- getChanged
       return (Watched (c <> newc) a')

type ConstraintCtx = AnnNameCtx (Ctx Symbol (Watched (Solvable MonadDMTC)))
-- type ConstraintCtx = AnnNameCtx (Ctx Symbol (Solvable' TC))

instance (MonadWatch t, Normalize t ks) => Normalize t (AnnNameCtx ks) where
  normalize (AnnNameCtx names ks) =
    do res <- AnnNameCtx names <$> normalize ks
       -- isC <- getChanged
       -- traceShowM $ "CHANGED: " <> show isC <> "\n"
       return res

instance Show ks => Show (AnnNameCtx ks) where
  show (AnnNameCtx _ kinds) = show kinds
instance Default ks => Default (AnnNameCtx ks)

newAnnName :: DictLike Symbol k ks => Text -> k -> AnnNameCtx ks -> (Symbol, AnnNameCtx ks)
newAnnName hint k (AnnNameCtx names kinds) =
  let (name, names') = newName hint names
      kinds' = setValue name k kinds
  in (name, AnnNameCtx names' kinds')

-- data Meta0Ctx extra = Meta0Ctx
--   {
--     _sensSubs :: Subs SVar Sensitivity,
--     _typeSubs :: Subs TVar DMType,
--     _constraints :: ConstraintCtx, -- MonCom (Solvable'' TCT) Symbol,
--   }
--   deriving (Generic)

-- data Watching = IsWatching | NotWatching
--   deriving (Show)

-- instance Default Watching where
--   def = NotWatching

class Cast a b where
  cast :: MonadDMTC t => a -> t b

type DMExtra = Cast (Either Sensitivity Privacy)

-- class DMExtra e where
--   castExtra :: MonadDMTC t => Either Sensitivity Privacy -> t e

instance Cast (Either Sensitivity Privacy) Sensitivity where
  cast (Left e) = return e
  cast (Right e) = internalError "Expected a sensitivity but got a privacy."

instance Cast (Either Sensitivity Privacy) Privacy where
  cast (Left e) = internalError "Expected a privacy but got a sensitivity."
  cast (Right e) = return e

instance (Cast (Either a b) x) => Cast (Either (z :& a) (z :& b)) (z :& x) where
  cast (Left (x :@ e)) = (x :@) <$> cast @(Either a b) (Left e)
  cast (Right (x :@ e)) = (x :@) <$> cast @(Either a b) (Right e)

instance (Cast a b) => Cast (Maybe a) (Maybe b) where
  cast Nothing = pure Nothing
  cast (Just a) = Just <$> cast a

-- instance Cast (Either (DMType :& Sensitivity) (DMType :& Privacy)) (DMType :& Sensitivity) where
--   cast (Left e) = return e
--   cast (Right e) = internalError "Expected a sensitivity but got a privacy."

-- instance Cast (Either (DMType :& Sensitivity) (DMType :& Privacy)) (DMType :& Privacy) where
--   cast (Left e) = internalError "Expected a privacy but got a sensitivity."
--   cast (Right e) = return e

-- instance (Cast a b, Cast c d) => Cast (a :& c) (b :& d) where
--   cast (a :@ b) = (:@) <$> cast a <*> cast b

-- instance Cast DMType DMType where
--   cast t = pure t

type TypeCtx extra = Ctx Symbol (DMType :& extra)
type TypeCtxSP = Either (TypeCtx Sensitivity) (TypeCtx Privacy)

data Watcher = Watcher Changed
  deriving (Generic)

data MetaCtx = MetaCtx
  {
    _sensVars :: KindedNameCtx SVarOf,
    _typeVars :: KindedNameCtx TVarOf,
    -- _constraintVars :: NameCtx,
    _sensSubs :: Subs SVarOf SensitivityOf,
    _typeSubs :: Subs TVarOf DMTypeOf,
    _constraints :: ConstraintCtx -- MonCom (Solvable'' TCT) Symbol,
  }
  deriving (Generic)

data TCState = TCState
  {
    _watcher :: Watcher
  }
  deriving (Generic)

data Full = Full
  {
    -- _meta1 :: Meta1Ctx,
    -- _meta0 :: Meta0Ctx extra
    _tcstate :: TCState,
    _meta :: MetaCtx,
    _types :: Either (TypeCtx Sensitivity) (TypeCtx Privacy)
  }
  deriving (Generic)

newtype TCT m a = TCT {runTCT :: (StateT Full (ExceptT DMException m) a)}
  deriving (Functor, Applicative, Monad, MonadState Full, MonadError DMException)

class LiftTC t where
  liftTC :: TC a -> t a

type TC = TCT Identity

-- type STC a = TC Sensitivity a
-- type PTC a = TC Privacy a

-- $(makeLenses ''Meta1Ctx)
-- $(makeLenses ''Meta0Ctx)
$(makeLenses ''MetaCtx)
$(makeLenses ''Full)
$(makeLenses ''TCState)


-- instance Show Meta1Ctx where
--   show (Meta1Ctx s t c) =  "- sens vars: " <> show s <> "\n"
--                         <> "- type vars: " <> show t <> "\n"
--                         <> "- cnst vars: " <> show c <> "\n"

-- instance Show e => Show (Meta0Ctx e) where
--   show (Meta0Ctx sσ tσ cs γ) = "- sens subs:   " <> show sσ <> "\n"
--                             <> "- type subs:   " <> show tσ <> "\n"
--                             <> "- constraints: " <> show cs <> "\n"
--                             <> "- types:       " <> show γ <> "\n"

instance Show (MetaCtx) where
  show (MetaCtx s t sσ tσ cs) =
       "- sens vars: " <> show s <> "\n"
    <> "- type vars: " <> show t <> "\n"
    -- <> "- cnst vars: " <> show c <> "\n"
    <> "- sens subs:   " <> show sσ <> "\n"
    <> "- type subs:   " <> show tσ <> "\n"
    <> "- constraints: " <> show cs <> "\n"
    -- <> "- types:       " <> show γ <> "\n"

instance Show Watcher where
  show (Watcher changed) = show changed

instance Show (TCState) where
  show (TCState w) = "- watcher: " <> show w <> "\n"

instance Show (Full) where
  show (Full tcs m γ) = "\nState:\n" <> show tcs <> "\nMeta:\n" <> show m <> "\nTypes:\n" <> show γ <> "\n"


-- modify02 :: MonadDMTC t => (Meta0Ctx e -> Meta0Ctx e) -> t e
-- modify02 f = modify (\s -> s {meta0 = f (meta0 s)})

-- modify0 :: MonadDMTC t => (Meta0Ctx e -> Meta0Ctx e) -> t ()
-- modify0 f = modify (\s -> s {meta0 = f (meta0 s)})

-- modify1 :: MonadDMTC t => (Meta1Ctx -> Meta1Ctx) -> t ()
-- modify1 f = modify (\s -> s {meta1 = f (meta1 s)})

-- state0 :: MonadDMTC t => (Meta0Ctx e -> (a, Meta0Ctx e)) -> t a
-- state0 f = state (\s -> let (a,b) = f (meta0 s)
--                         in (a, s {meta0 = b}))

-- state1 :: MonadDMTC t => (Meta1Ctx -> (a, Meta1Ctx)) -> t a
-- state1 f = state (\s -> let (a,b) = f (meta1 s)
--                         in (a, s {meta1 = b}))

-- instance Default (Meta1Ctx) where
-- instance Default (Meta0Ctx e) where
instance Default (Watcher) where
instance Default (TCState) where
instance Default (MetaCtx) where
instance Default (Full) where
  def = Full def def (Left def)

  -- Full ::  NameCtx -> NameCtx -> NameCtx -> Subs DMType -> ConstraintOlds -> Ctx extra -> Full extra
  -- deriving (Generic, Show)

-- type TC extra = StateT (Full extra) (Except DMException)
-- newtype TC extra a = TC {runTC :: (StateT (Full extra) (Except DMException) a)}
--   deriving (Functor, Applicative, Monad, MonadState (Full extra), MonadError DMException)



instance Monad m => MonadTerm DMTypeOf (TCT m) where
  type VarFam DMTypeOf = TVarOf
  getSubs = view (meta.typeSubs) <$> get
  addSub σ = do
    σs <- use (meta.typeSubs)
    σs' <- σs ⋆ singletonSub σ
    meta.typeSubs .= σs'
  newVar = TVar <$> newTVar "τ"

instance Monad m => MonadTerm SensitivityOf (TCT m) where
  type VarFam SensitivityOf = SVarOf
  getSubs = view (meta.sensSubs) <$> get
  addSub σ = do
    σs <- use (meta.sensSubs)
    traceM ("I have the subs " <> show σs <> ", and I want to add: " <> show σ)
    σs' <- σs ⋆ singletonSub σ
    meta.sensSubs .= σs'
  newVar = coerce <$> svar <$> newSVar "τ"

-- getUnsolved :: MonCom (Solvable' TC) Symbol -> Maybe (Symbol, Solvable' TC)
-- getUnsolved = undefined

instance Monad m => MonadConstraint (MonadDMTC) (TCT m) where
  addConstraint c = meta.constraints %%= (newAnnName "constr" (Watched IsChanged c))
  getUnsolvedConstraintMarkNormal = do
    (AnnNameCtx _ (Ctx (MonCom constrs))) <- use (meta.constraints)
    let constrs2 = H.toList constrs
    let changed = filter (\(a, Watched state constr) -> state == IsChanged) constrs2
    case changed of
      [] -> return Nothing
      ((name,Watched _ constr):_) -> do
        meta.constraints %= (\(AnnNameCtx names cs) -> AnnNameCtx names (setValue name (Watched NotChanged constr) cs))
        return (Just (name, constr))

  dischargeConstraint name = meta.constraints %= (\(AnnNameCtx n c) -> AnnNameCtx n (deleteValue name c))
  failConstraint name = do
    (AnnNameCtx n cs) <- use (meta.constraints)
    let c = getValue name cs
    throwError (UnsatisfiableConstraint (show c))

  updateConstraint name c = do
    meta.constraints %= (\(AnnNameCtx n cs) -> AnnNameCtx n (setValue name (Watched IsChanged c) cs))

    -- (AnnNameCtx n cs) <- use (meta.constraints)






  {-
instance Monad m => MonadConstraint' Symbol TC (TCT m) where
  -- type ConstrVar TC = Symbol
  addConstraint' c = meta.constraints %%= newAnnName "constr" (DMSolvable c)
  -- modify0 (\f -> f {constraints = MonCom [(c,"hello")]}) -- --modify0 (\s -> s {constraints = _}) -- 
  getUnsolvedConstraint' = undefined -- getUnsolved <$> view (meta0.constraints) <$> get
  -- addConstraint'2 c = return ()
-}
-- instance MonadConstraint'' Symbol TCT where
--   addConstraint'' c = meta0.constraints %%= newAnnName "" (Solvable'' c)

-- instance Monad t => MonadConstraintTag DM Symbol (TCT t e) where
--   addConstraintTag c = meta0.constraints %%= newAnnName "" (SolvableTag c)

-- instance Monad t => MonadConstraintDiff Symbol (TC e) (TCT t e) where
--   addConstraintDiff c = _ -- meta0.constraints %%= newAnnName "" (SolvableTag c)




instance Monad m => MonadWatch (TCT m) where
  -- startWatch = tcstate.watcher %= (\(Watcher _ _) -> Watcher IsWatching NotChanged)
  -- stopWatch = tcstate.watcher %= (\(Watcher _ s) -> Watcher NotWatching s)
  resetChanged = tcstate.watcher %= (\(Watcher _) -> Watcher NotChanged)
  notifyChanged = tcstate.watcher %= (\(Watcher _) -> Watcher IsChanged)
  getChanged = do (Watcher c) <- use (tcstate.watcher)
                  return c





-- instance MonadWatch m => MonadWatch (TCT m) where
--   notifyChanged = TCT (lift (lift notifyChanged))


-- supremum :: forall isT t a k. (Normalize (t) (a k), IsT isT t, MonadTerm a (t), MonadConstraint isT (t), Solve isT IsSupremum (a k, a k, a k)) => (a k) -> (a k) -> t (a k)


supremum :: (IsT isT t, HasNormalize isT (a k, a k, a k), MonadConstraint isT (t), MonadTerm a (t), Solve isT IsSupremum (a k, a k, a k), SingI k, Typeable k) => (a k) -> (a k) -> t (a k)
supremum x y = do
  (z :: a k) <- newVar
  addConstraint (Solvable (IsSupremum (x, y, z)))
  return z
instance Monad m => MonadInternalError (TCT m) where
  internalError = throwError . InternalError

-- instance MonadDMTC e (TC) where
instance Monad m => MonadDMTC (TCT m) where

-- instance MonadDMTC t => Normalize (t) (Solvable' TC) where
--   normalize solv = liftTC (normalize solv)

instance Monad m => LiftTC (TCT m) where
  liftTC (TCT v) = -- TCT (v >>= (lift . lift . return))
    let x = StateT (\s -> ExceptT (return $ runExcept (runStateT v s)))
    in TCT (x) -- TCT (return v)

  {-
-}
instance Monad m => MonadImpossible (TCT m) where
  impossible err = throwError (ImpossibleError err)

instance MonadDMTC t => Normalize (t) (DMTypeOf k) where
  normalize n =
    do σ <- getSubs @_ @DMTypeOf
       n₂ <- σ ↷ n
       σ <- getSubs @_ @SensitivityOf
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

instance MonadDMTC t => Normalize (t) Sensitivity where
  normalize n =
    do σ <- getSubs @_ @SensitivityOf
       σ ↷ n

instance Monad t => Normalize t (SymbolOf k) where
  normalize = pure


instance MonadDMTC t => Normalize (t) DMTypeOp where
  normalize (UnaryNum op τ res) = UnaryNum op <$> normalize τ <*> normalize res
  normalize (BinaryNum op τ res) = BinaryNum op <$> normalize τ <*> normalize res
  -- normalize (Ternary op τ res) = Ternary op <$> normalize τ <*> normalize res

-- instance MonadDMTC t :=> Normalize (t) DMTypeOp where
--   ins = Sub Dict

instance (MonadDMTC t => Normalize (t) a) => MonadDMTC t :=> Normalize (t) a where
-- instance (IsT isT t, isT e t => Normalize (t) a) => isT e t :=> Normalize (t) a where
  ins = Sub Dict


instance Monad m => IsT MonadDMTC (TCT m) where
-- instance (forall e. MonadDMTC t) => IsT MonadDMTC (t) where

  -- normalize (Binary op σ τ) = Binary op <$> normalize σ <*> normalize τ
  -- normalize (Ternary op ρ σ τ) = Ternary op <$> normalize ρ <*> normalize σ <*> normalize τ


-- instance (forall e t. (MonadDMTC t => Normalize (t) a)) => HasNormalize MonadDMTC a where



  -- solve_ (Constr (Binary op σ τ)) = undefined
  -- solve_ (Constr (Ternary op ρ σ τ)) = undefined




newTVar :: forall k e t. (MonadDMTC t, SingI k) => Text -> t (TVarOf k)
newTVar hint = meta.typeVars %%= ((newKindedName hint))

newSVar :: forall k e t. (SingI k, MonadDMTC t) => Text -> t (SVarOf k)
newSVar hint = meta.sensVars %%= (newKindedName hint)

  -- where f names = let (τ , names') = newName hint names
  --                 in (TVar τ, names')


  -- state (over meta0 f)
  -- where f (Meta1Ctx s t c) =
  --         let (τ , s') = newName hint s
  --         in (TVar τ , Meta1Ctx s t c)






-- Maps julia num types to DMtypes (of basenumkind)
createDMTypeNum :: JuliaNumType -> DMTypeOf BaseNumKind
createDMTypeNum JTNumInt = DMInt
createDMTypeNum JTNumReal = DMReal

-- Maps julia types to DMTypes (of main kind)
-- (`JTAny` is turned into a new type variable.)
createDMType :: MonadDMTC t => JuliaType -> t (DMTypeOf MainKind)
createDMType JTAny = TVar <$> newTVar "any"
 -- NOTE: defaulting to non-const might or might not be what we want to do here.
createDMType (JTNum τ) = pure (Numeric (NonConst (createDMTypeNum τ)))








