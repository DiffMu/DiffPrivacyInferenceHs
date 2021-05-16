
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}


module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Symbolic
import {-# SOURCE #-} DiffMu.Typecheck.Subtyping

import qualified Data.HashMap.Strict as H

import Debug.Trace

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



instance (Substitute v x a, Substitute v x b) => Substitute v x (a :& b) where
  substitute σs (a :@ b) = (:@) <$> substitute σs a <*> substitute σs b

instance Substitute v x a => Substitute v x [a] where
  substitute σs xs = mapM (substitute σs) xs

instance Substitute v x a => Substitute v x (Maybe a) where
  substitute σs (Just a) = Just <$> substitute σs a
  substitute σs (Nothing) = pure Nothing

instance Substitute TVarOf DMTypeOf JuliaType where
  substitute σs jt = pure jt

instance Substitute SVarOf SensitivityOf JuliaType where
  substitute σs jt = pure jt

instance Substitute TVarOf DMTypeOf Sensitivity where
  substitute σs η = pure η

-- instance (Substitute v a x, Substitute v a DMType) => Substitute v a (WithRelev x) where
  -- substitute σs (WithRelev i x) = WithRelev i <$> substitute σs x
instance (Typeable a, Typeable v, Substitute v a DMType) => Substitute v a (WithRelev x) where
  substitute σs (WithRelev i x) = undefined

--instance Substitute TVarOf DMTypeOf Privacy where
--  substitute σs η = pure η

instance Substitute TVarOf DMTypeOf (RealizeAnn a) where
  substitute σs (RealS s) = RealS <$> (substitute σs s)
  substitute σs (RealP s) = RealP <$> (substitute σs s)

instance Substitute TVarOf DMTypeOf (DMTypeOf k) where
  substitute σs L1 = pure L1
  substitute σs L2 = pure L2
  substitute σs LInf = pure LInf
  substitute σs U = pure U
  substitute σs (Clip n) = Clip <$> substitute σs n
  substitute σs DMInt = pure DMInt
  substitute σs DMReal = pure DMReal
  substitute σs DMData = pure DMData
  substitute σs (Numeric τ) = Numeric <$> substitute σs τ
  substitute σs (NonConst τ) = NonConst <$> substitute σs τ
  substitute σs (Const η τ) = Const <$> substitute σs η <*> substitute σs τ
  substitute σs (TVar x) = σs x
  substitute σs (τ1 :->: τ2) = (:->:) <$> substitute σs τ1 <*> substitute σs τ2
  substitute σs (τ1 :->*: τ2) = (:->*:) <$> substitute σs τ1 <*> substitute σs τ2
  substitute σs (DMTup τs) = DMTup <$> substitute σs τs
  substitute σs (DMMat nrm clp n m τ) = DMMat nrm clp <$> substitute σs n <*> substitute σs m <*> substitute σs τ
  substitute σs (DMChoice xs) = DMChoice <$> substitute σs xs
  substitute σs (NoFun (x :@ a)) = (\x -> NoFun (x :@ a)) <$> substitute σs x
  substitute σs (Fun xs) = Fun <$> substitute σs xs
  substitute σs (a :↷: x) = (a :↷:) <$> substitute σs x
  substitute σs (x :∧: y) = (:∧:) <$> substitute σs x <*> substitute σs y
  substitute σs (Trunc a x) = Trunc a <$> substitute σs x
  substitute σs (TruncFunc a x) = TruncFunc a <$> substitute σs x
  substitute σs (Return τ) = Return <$> substitute σs τ


instance Substitute SVarOf SensitivityOf (RealizeAnn a) where
  substitute σs (RealS s) = RealS <$> (substitute σs s)
  substitute σs (RealP s) = RealP <$> (substitute σs s)

instance Substitute SVarOf SensitivityOf (DMTypeOf k) where
  substitute σs L1 = pure L1
  substitute σs L2 = pure L2
  substitute σs LInf = pure LInf
  substitute σs U = pure U
  substitute σs (Clip n) = Clip <$> substitute σs n
  substitute σs DMInt = pure DMInt
  substitute σs DMReal = pure DMReal
  substitute σs DMData = pure DMData
  substitute σs (Numeric τ) = Numeric <$> substitute σs τ
  substitute σs (NonConst τ) = NonConst <$> substitute σs τ
  substitute σs (Const η τ) = Const <$> substitute σs η <*> substitute σs τ
  substitute σs (TVar x) = pure (TVar x)
  substitute σs (τ1 :->: τ2) = (:->:) <$> substitute σs τ1 <*> substitute σs τ2
  substitute σs (τ1 :->*: τ2) = (:->*:) <$> substitute σs τ1 <*> substitute σs τ2
  substitute σs (DMTup τs) = DMTup <$> substitute σs τs
  substitute σs (DMMat nrm clp n m τ) = DMMat nrm clp <$> substitute σs n <*> substitute σs m <*> substitute σs τ
  substitute σs (DMChoice xs) = DMChoice <$> substitute σs xs
  substitute σs (NoFun x) = NoFun <$> substitute σs x
  substitute σs (Fun xs) = Fun <$> substitute σs xs
  substitute σs (a :↷: x) = (:↷:) <$> substitute σs a <*> substitute σs x
  substitute σs (x :∧: y) = (:∧:) <$> substitute σs x <*> substitute σs y
  substitute σs (Trunc a x) = Trunc <$> substitute σs a <*> substitute σs x
  substitute σs (TruncFunc a x) = TruncFunc <$> substitute σs a <*> substitute σs x
  substitute σs (Return τ) = Return <$> substitute σs τ


instance Term TVarOf DMTypeOf where
  var x = TVar x
  isVar (TVar x) = Just x
  isVar _        = Nothing

instance FreeVars v a => FreeVars v [a] where
  freeVars [] = []
  freeVars (τ:τs) = freeVars τ <> freeVars τs

instance (FreeVars v a, FreeVars v b) => FreeVars v (a :& b) where
  freeVars (a :@ b) = freeVars a <> freeVars b

instance (FreeVars v a, FreeVars v b) => FreeVars v (a , b) where
  freeVars (a, b) = freeVars a <> freeVars b

instance (FreeVars v a) => FreeVars v (Maybe a) where
  freeVars (Just a) = freeVars a
  freeVars (Nothing) = mempty

instance FreeVars TVarOf Sensitivity where
  freeVars _ = mempty

instance FreeVars TVarOf JuliaType where
  freeVars _ = mempty

instance Typeable a => FreeVars TVarOf (RealizeAnn a) where
  freeVars (RealS s) = freeVars s
  freeVars (RealP s) = freeVars s

instance Typeable k => FreeVars TVarOf (DMTypeOf k) where
  freeVars DMInt = []
  freeVars DMReal = []
  freeVars DMData = []
  freeVars L1 = []
  freeVars L2 = []
  freeVars LInf = []
  freeVars U = []
  freeVars (Clip τ) = freeVars τ
  freeVars (Numeric τ) = freeVars τ
  freeVars (NonConst τ) = freeVars τ
  freeVars (Const _ τ) = freeVars τ
  freeVars (TVar x) = [SomeK x]
  freeVars (τ1 :->: τ2) = freeVars (τ1) <> freeVars τ2
  freeVars (τ1 :->*: τ2) = freeVars (τ1) <> freeVars τ2
  freeVars (DMTup τs) = freeVars τs
  freeVars (DMMat nrm clp n m τ) = freeVars nrm <> freeVars clp <> freeVars τ
  freeVars (DMChoice choices) = freeVars choices
  freeVars (NoFun x) = freeVars x
  freeVars (Fun xs) = freeVars xs
  freeVars (a :↷: x) = freeVars x
  freeVars (x :∧: y) = freeVars x <> freeVars y
  freeVars (Trunc a x) = freeVars x
  freeVars (TruncFunc a x) = freeVars x
  freeVars (Return x) = freeVars x







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

instance (Substitute v a x, Substitute v a y) => Substitute v a (x,y) where
  substitute σs (x,y) = (,) <$> substitute σs x <*> substitute σs y

-- TODO: implement isVar and freeVars
instance Term SVarOf SensitivityOf where
  var (v) = var (HonestVar v)
  isVar s = case isVar s of
    Just (HonestVar v) -> Just v
    _ -> Nothing

type TSubs = Subs DMTypeOf
type SSubs = Subs SensitivityOf














class (MonadImpossible (t), MonadWatch (t),
       MonadTerm DMTypeOf (t), MonadTerm SensitivityOf (t),
       MonadState (Full) (t),
       MonadError DMException (t),
       MonadInternalError t,
       -- MonadConstraint' Symbol (TC) (t),
       -- MonadConstraint Symbol (MonadDMTC) (t),
       MonadConstraint (MonadDMTC) (t),
       MonadNormalize t
       -- LiftTC t
      ) => MonadDMTC t where

data Tag = DM

data AnnNameCtx ks = AnnNameCtx
  {
    _annnames :: NameCtx,
    _anncontent :: ks
  }
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

data CtxStack v a = CtxStack
  {
    _topctx :: Ctx v a,
    _otherctxs :: [Ctx v a]
  }
type ConstraintCtx = AnnNameCtx (CtxStack Symbol (Watched (Solvable MonadDMTC)))
instance DictKey v => DictLike v x (CtxStack v x) where
  setValue k v (CtxStack d other) = CtxStack (setValue k v d) other
  getValue k (CtxStack d _) = getValue k d
  deleteValue k (CtxStack d other) = CtxStack (deleteValue k d) other
  emptyDict = CtxStack emptyDict []
  isEmptyDict (CtxStack top others) = isEmptyDict top
instance Normalize t a => Normalize t (CtxStack v a) where
  normalize (CtxStack top other) = CtxStack <$> normalize top <*> normalize other

instance (Show v, Show a, DictKey v) => Show (CtxStack v a) where
  show (CtxStack top other) = "   - top:\n" <> show top <> "\n"
                              <> "   - others:\n" <> show other

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

-- type DMExtra = Cast (Either Sensitivity Privacy)

-- class DMExtra e where
--   castExtra :: MonadDMTC t => Either Sensitivity Privacy -> t e

instance Cast (Either Sensitivity Privacy) Sensitivity where
  cast (Left e) = return e
  cast (Right e) = error $ "Expected a sensitivity but got a privacy (" <> show e <> ")."

instance Cast (Either Sensitivity Privacy) Privacy where
  cast (Left e) = error $ "Expected a privacy but got a sensitivity (" <> show e <> ")."
  cast (Right e) = return e

instance Typeable x => Cast (Either (DMTypeOf (AnnKind AnnS)) (DMTypeOf (AnnKind AnnP))) (DMTypeOf (AnnKind x)) where
  cast e =
    let case1 = testEquality (typeRep @x) (typeRep @AnnS)
        case2 = testEquality (typeRep @x) (typeRep @AnnP)
    in case (case1,case2) of
      (Just Refl, _) -> case e of
                          Left e -> return e
                          Right _ -> error "Expected a sensitivity but got a privacy."
      (_ , Just Refl) -> case e of
                          Right e -> return e
                          Left _ -> error "Expected a privacy but got a sensitivity."
      _    -> impossible "Found an AnnKind which was neither AnnS nor AnnP."
-- instance Cast (Either (DMTypeOf (AnnKind AnnS)) (DMTypeOf (AnnKind AnnP))) (DMTypeOf (AnnKind x)) where

instance Typeable x => Cast (Either (WithRelev AnnS) (WithRelev AnnP)) (WithRelev x) where
  cast (Left (WithRelev i x)) = WithRelev i <$> cast @(Either (DMTypeOf (AnnKind AnnS)) (DMTypeOf (AnnKind AnnP))) (Left x)
  cast (Right (WithRelev i x)) = WithRelev i <$> cast @(Either (DMTypeOf (AnnKind AnnS)) (DMTypeOf (AnnKind AnnP))) (Right x)
  -- cast (Left (WithRelev i (x :@ e))) = WithRelev i <$> (x :@) <$> cast @(Either (RealizeAnn a) (RealizeAnn b)) (Left e)
  -- cast (Right (WithRelev i (x :@ e))) = WithRelev i <$> (x :@) <$> cast @(Either (RealizeAnn a) (RealizeAnn b)) (Right e)

-- instance (Cast (Either a b) x) => Cast (Either (WithRelev a) (WithRelev b)) (WithRelev x) where
--   cast (Left (WithRelev i (x :@ e))) = WithRelev i <$> (x :@) <$> cast @(Either a b) (Left e)
--   cast (Right (WithRelev i (x :@ e))) = WithRelev i <$> (x :@) <$> cast @(Either a b) (Right e)


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

instance (MonadDMTC t) => Normalize t (WithRelev e) where
  normalize (WithRelev i x) = WithRelev i <$> normalize x

-- instance (MonadDMTC t, Normalize t e) => Normalize t (WithRelev e) where
--   normalize (WithRelev i x) = WithRelev i <$> normalize x


type TypeCtx extra = Ctx Symbol (WithRelev extra)
type TypeCtxSP = Either (TypeCtx AnnS) (TypeCtx AnnP)

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
    _types :: TypeCtxSP
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
$(makeLenses ''AnnNameCtx)
$(makeLenses ''CtxStack)
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
    <> "- constraints:\n" <> show cs <> "\n"
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
instance Default (CtxStack v a) where
  def = CtxStack def []
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
instance (SemigroupM t a) => SemigroupM t (Watched a) where
  (⋆) (Watched x a) (Watched y b) = Watched (x <> y) <$> a ⋆ b

instance (MonoidM t a) => MonoidM t (Watched a) where
  neutral = Watched NotChanged <$> neutral
-- instance MonadInternalError t => MonoidM t (Watched a) where

instance (CheckNeutral t a) => CheckNeutral t (Watched a) where
  checkNeutral a = pure False

instance Monad t => (SemigroupM t (Solvable a)) where
  (⋆) (Solvable a) (Solvable b) = error "Trying to combine two constraints with the same name."
instance Monad t => (MonoidM t (Solvable a)) where
  neutral = error "Trying to get neutral of solvable"
instance Monad t => (CheckNeutral t (Solvable a)) where
  checkNeutral a = pure False


instance Monad m => MonadTerm DMTypeOf (TCT m) where
  type VarFam DMTypeOf = TVarOf
  getSubs = view (meta.typeSubs) <$> get
  addSub σ = do
    σs <- use (meta.typeSubs)
    σs' <- σs ⋆ singletonSub σ
    meta.typeSubs .= σs'
    meta.typeVars %= (removeNameBySubstitution σ)
  newVar = TVar <$> newTVar "τ"

instance Monad m => MonadTerm SensitivityOf (TCT m) where
  type VarFam SensitivityOf = SVarOf
  getSubs = view (meta.sensSubs) <$> get
  addSub σ = do
    σs <- use (meta.sensSubs)
    traceM ("I have the subs " <> show σs <> ", and I want to add: " <> show σ)
    σs' <- σs ⋆ singletonSub σ
    meta.sensSubs .= σs'
    meta.sensVars %= (removeNameBySubstitution σ)
  newVar = coerce <$> svar <$> newSVar "s"

-- getUnsolved :: MonCom (Solvable' TC) Symbol -> Maybe (Symbol, Solvable' TC)
-- getUnsolved = undefined

instance Monad m => MonadConstraint (MonadDMTC) (TCT m) where
  type ConstraintBackup (TCT m) = (Ctx Symbol (Watched (Solvable MonadDMTC)))
  addConstraint c = meta.constraints %%= (newAnnName "constr" (Watched IsChanged c))
  getUnsolvedConstraintMarkNormal = do
    (Ctx (MonCom constrs)) <- use (meta.constraints.anncontent.topctx)
    let constrs2 = H.toList constrs
    let changed = filter (\(a, Watched state constr) -> state == IsChanged) constrs2
    case changed of
      [] -> return Nothing
      ((name,Watched _ constr):_) -> do
        meta.constraints.anncontent.topctx %= (setValue name (Watched NotChanged constr))
        return (Just (name, constr))

  dischargeConstraint name = meta.constraints.anncontent.topctx %= (deleteValue name)
  failConstraint name = do
    (AnnNameCtx n cs) <- use (meta.constraints)
    let c = getValue name cs
    throwError (UnsatisfiableConstraint (show c))

  updateConstraint name c = do
    meta.constraints %= (\(AnnNameCtx n cs) -> AnnNameCtx n (setValue name (Watched IsChanged c) cs))

  openNewConstraintSet = do
    (CtxStack top other) <- use (meta.constraints.anncontent)
    meta.constraints.anncontent .= (CtxStack emptyDict (top:other))
    return ()

  mergeTopConstraintSet = do
    (CtxStack (Ctx (MonCom top)) other) <- use (meta.constraints.anncontent)
    case other of
      ((Ctx o):os) -> case null top of
        False -> do
          o' <- MonCom top ⋆ o
          meta.constraints.anncontent .= (CtxStack (Ctx o') os)
          return ConstraintSet_WasNotEmpty
        True -> do
          meta.constraints.anncontent .= (CtxStack (Ctx o) os)
          return ConstraintSet_WasEmpty
      [] -> error "Trying to merge top constraint set, but there are non in the stack."

  getConstraintsByType (Proxy :: Proxy (c a)) = do
    (Ctx (MonCom cs)) <- use (meta.constraints.anncontent.topctx)
    let f :: (Watched (Solvable MonadDMTC)) -> Maybe (c a)
        f (Watched _ (Solvable (c :: c' a'))) = case testEquality (typeRep @(c a)) (typeRep @(c' a')) of
          Just Refl -> Just c
          Nothing -> Nothing

    let cs' = H.toList cs
        cs'' = second f <$> cs'
    return [(name,c) | (name, Just c) <- cs'' ]

  tracePrintConstraints = do
    ctrs <- use (meta.constraints.anncontent)
    traceM $ "## Constraints ##"
    traceM $ show ctrs
    traceM $ "## ----------- ##"

    -- case null top of
    --   True  -> 
    --   False -> return Failure_WasNotEmpty

  -- clearConstraints = undefined
  --   -- (AnnNameCtx ns ctx) <- use (meta.constraints)
  --   -- meta.constraints .= AnnNameCtx ns emptyDict
  --   -- return ctx
  -- restoreConstraints ctx1 = undefined --do
    -- (AnnNameCtx ns _) <- use (meta.constraints)
    -- meta.constraints .= AnnNameCtx ns ctx1

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

infimum :: (IsT isT t, HasNormalize isT (a k, a k, a k), MonadConstraint isT (t), MonadTerm a (t), Solve isT IsInfimum (a k, a k, a k), SingI k, Typeable k) => (a k) -> (a k) -> t (a k)
infimum x y = do
  (z :: a k) <- newVar
  addConstraint (Solvable (IsInfimum (x, y, z)))
  return z



instance Monad m => MonadInternalError (TCT m) where
  internalError = throwError . InternalError




-- Normalizes all contexts in our typechecking monad, i.e., applies all available substitutions.
normalizeContext :: (MonadDMTC t) => t ()
normalizeContext = do
  types %=~ normalize
  meta.constraints %=~ normalize



instance Monad m => MonadNormalize (TCT m) where
  normalizeState = normalizeContext

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

instance (MonadDMTC t) => Normalize t (DMTypeOf k) where
  normalize n =
    do -- we apply all type variable substitutions
       σ <- getSubs @_ @DMTypeOf
       n₂ <- σ ↷ n

       -- and all sensitivity variables substitutions
       σ <- getSubs @_ @SensitivityOf
       n₃ <- σ ↷ n₂

       -- finally we normalize the uppermost "annotation" layer (if there is one)
       -- , i.e., compute {↷,∧,Trunc}-terms
       normalizeAnn n₃

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

instance MonadDMTC t => Normalize t (RealizeAnn a) where
  normalize (RealS s) = RealS <$> normalize s
  normalize (RealP s) = RealP <$> normalize s

instance (Monad t, Normalize t a) => Normalize t (Maybe a) where
  normalize Nothing = pure Nothing
  normalize (Just a) = Just <$> normalize a


-- instance (Solve MonadDMTC IsInfimum (DMType,DMType,DMType), IsT MonadDMTC t, Monad t) => Normalize (t) DMTypeOp where
instance (MonadDMTC t) => Normalize (t) DMTypeOp where
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




newTVar :: forall k e t. (MonadDMTC t, SingI k, Typeable k) => Text -> t (TVarOf k)
newTVar hint = meta.typeVars %%= ((newKindedName hint))

newSVar :: forall k e t. (SingI k, MonadDMTC t, Typeable k) => Text -> t (SVarOf k)
newSVar hint = meta.sensVars %%= (newKindedName hint)

  -- where f names = let (τ , names') = newName hint names
  --                 in (TVar τ, names')


  -- state (over meta0 f)
  -- where f (Meta1Ctx s t c) =
  --         let (τ , s') = newName hint s
  --         in (TVar τ , Meta1Ctx s t c)


------------------------------------------------------------------------
-- unification of sensitivities

-- Before we can unify dmtypes, we have to proof that we can unify
-- sensitivities.
-- We unify them simply by adding an equality constraint. That this
-- constraint is solvable in any class of monads, in particular in MonadDMTC,
-- is shown in Abstract.Data.MonadicPolynomial.
--
instance Unify MonadDMTC Sensitivity where
  unify_ s1 s2 = do
    c <- addConstraint @MonadDMTC (Solvable (IsEqual (s1, s2)))
    return s1

instance (Unify t a, Unify t b) => Unify t (a,b) where
  unify_ (a1,b1) (a2,b2) = (,) <$> (unify_ a1 a2) <*> (unify_ b1 b2)

instance (Show a, Unify MonadDMTC a) => Unify MonadDMTC (Maybe a) where
  unify_ Nothing Nothing = pure Nothing
  unify_ (Just a) (Just b) = Just <$> unify_ a b
  unify_ t s = throwError (UnificationError t s)

-- instance Unify MonadDMTC Privacy where
--   unify_ (a1,b1) (a2,b2) = (,) <$> (unify_ a1 a2) <*> (unify_ b1 b2)





-- Maps julia num types to DMtypes (of basenumkind)
-- createDMTypeNum :: JuliaNumType -> DMTypeOf BaseNumKind
-- createDMTypeNum JTNumInt = DMInt
-- createDMTypeNum JTNumReal = DMReal
createDMTypeNum :: MonadDMTC t => JuliaType -> t (DMTypeOf BaseNumKind)
createDMTypeNum (JuliaType "Integer") = pure DMInt
createDMTypeNum (JuliaType "Real")  = pure  DMReal
createDMTypeNum (JuliaType str)  = throwError (TypeMismatchError $ "expected " <> show str <> " to be either Integer or Real.")

-- Maps julia types to DMTypes (of main kind)
-- (`JTAny` is turned into a new type variable.)
-- createDMType :: MonadDMTC t => JuliaType -> t (DMTypeOf NoFunKind)
--  -- NOTE: defaulting to non-const might or might not be what we want to do here.
-- createDMType (JuliaType "Integer") = pure $ Numeric (NonConst DMInt)
-- createDMType (JuliaType "Real") = pure $ Numeric (NonConst DMReal)
-- -- TODO: is it correct to create tvars for anything else?
-- createDMType _ = TVar <$> newTVar "any"

createDMType :: MonadDMTC t => JuliaType -> t (DMTypeOf (AnnKind AnnS))
 -- NOTE: defaulting to non-const might or might not be what we want to do here.
createDMType (JuliaType "Integer") = do
  s <- newVar
  return (NoFun (Numeric (NonConst DMInt) :@ RealS s))
createDMType (JuliaType "Real") = do
  s <- newVar
  return (NoFun (Numeric (NonConst DMReal) :@ RealS s))
-- TODO: is it correct to create tvars for anything else?
createDMType _ = TVar <$> newTVar "any"





----------------------------------------------------------
-- normalization for annotated dmtypes

-- This is for evaluating the ∧, Trunc, ↷ constructors when it is known whether
-- we have a function or non function type.
-- We do not need a monad here.
truncateExtra :: (Eq e, CMonoidM Identity e, CMonoidM Identity f) => f -> e -> f
truncateExtra η η_old =
  (case η_old == zeroId of
      True -> zeroId
      _    -> η)
-- truncateExtra :: RealizeAnn f -> RealizeAnn e -> RealizeAnn f
-- truncateExtra η (RealS η_old) = 
--   (case η_old == zeroId of
--       True -> zeroId
--       _    -> η)
-- truncateExtra η η_old =

scaleExtra :: forall (a :: Annotation). Sensitivity -> RealizeAnn a -> RealizeAnn a
scaleExtra η (RealS s) = RealS (η ⋅! s)
scaleExtra η (RealP (ε, δ)) = RealP (η ⋅! ε , η ⋅! δ)

-- scaleSens :: forall (a :: Annotation). Sensitivity -> Sensitivi -> RealizeAnn a
-- scaleSens = undefined

normalizeAnn :: forall t k. (MonadDMTC t) => DMTypeOf k -> t (DMTypeOf k)
normalizeAnn (TVar a) = pure $ TVar a
normalizeAnn (Fun as) = do
  let normalizeInside (f :@ annot) = (:@ annot) <$> normalizeAnn f
  Fun <$> mapM normalizeInside as
normalizeAnn (NoFun fs) = pure $ NoFun fs
normalizeAnn (Trunc η a) = do
  a' <- normalizeAnn a
  case a' of
    NoFun (x :@ η_old) -> pure $ NoFun (x :@ truncateExtra η η_old)
    Fun xs             -> pure $ Trunc η (Fun xs)
    other              -> pure $ Trunc η other
normalizeAnn (η :↷: a) = do
  a' <- normalizeAnn a
  case a' of
    NoFun (x :@ η_old) -> pure $ NoFun (x :@ scaleExtra η η_old)
    Fun xs             -> pure $ Fun ((\(x :@ (jt , a)) -> (x :@ (jt , η ⋅! a))) <$> xs)
    other              -> pure $ (η :↷: other)
normalizeAnn (a :∧: b) = do
  a' <- normalizeAnn a
  b' <- normalizeAnn b
  case (a', b') of
    (Fun xs, Fun ys) -> pure $ Fun (xs <> ys)
    (NoFun (x :@ ηx), NoFun (y :@ ηy)) -> do -- z <- infimum @MonadDMTC @t x y
                                             z <- newVar
                                             addConstraint (Solvable (IsInfimum (x, y, z)))
                                             return (NoFun (z :@ (ηx ⋆! ηy)))
    (_ , _) -> return (a' :∧: b')
normalizeAnn (xs :->: y) = (:->:) <$> mapM normalizeAnn xs <*> normalizeAnn y
normalizeAnn (xs :->*: y) = (:->*:) <$> mapM normalizeAnn xs <*> normalizeAnn y
normalizeAnn x = pure x

-- normalizeInsideAnn :: MonadDMTC t => DMTypeOf (AnnKind a) -> t (DMTypeOf (AnnKind a))
-- normalizeInsideAnn (TVar a) = undefined

-- normalizeRewritingDMType :: MonadDMTC t -> 
-- normalizeRewritingDMType :: (IsT MonadDMTC t, (Solve MonadDMTC IsInfimum (DMType, DMType, DMType))) => DMTypeOf k -> t (DMTypeOf k)
-- normalizeRewritingDMType (TVar a) = pure $ TVar a
-- normalizeRewritingDMType (TVar a) = pure $ TVar a
-- normalizeRewritingDMType (TVar a) = pure $ TVar a
-- normalizeRewritingDMType (TVar a) = pure $ TVar a
-- normalizeRewritingDMType (TVar a) = pure $ TVar a




