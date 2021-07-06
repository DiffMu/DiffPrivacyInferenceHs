
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}


module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Symbolic
import DiffMu.Core.Logging
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

inftyS :: Sensitivity
inftyS = constCoeff Infty

inftyP :: Privacy
inftyP = (constCoeff Infty, constCoeff Infty)

instance (Substitute v x a, Substitute v x b, Substitute v x c) => Substitute v x (a, b, c) where
  substitute σs (a, b, c) = (,,) <$> substitute σs a <*> substitute σs b <*> substitute σs c

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

instance Substitute v a x => Substitute v a (H.HashMap k x) where
  substitute σs h = mapM (substitute σs) h

instance Substitute TVarOf DMTypeOf (SVarOf k) where
  substitute σs = pure

instance Substitute TVarOf DMTypeOf DMTypeOp where
  substitute σs (UnaryNum op arg res) = (UnaryNum op <$> substitute σs arg <*> substitute σs res)
  substitute σs (BinaryNum op args res) = (BinaryNum op <$> substitute σs args <*> substitute σs res)

instance Substitute TVarOf DMTypeOf (Annotation a) where
  substitute σs (SensitivityAnnotation s) = SensitivityAnnotation <$> (substitute σs s)
  substitute σs (PrivacyAnnotation s) = PrivacyAnnotation <$> (substitute σs s)


removeVars :: forall t. Monad t => (forall k. (IsKind k) => TVarOf k -> t (DMTypeOf k)) -> [SomeK (TVarOf)] -> t [SomeK (TVarOf)]
removeVars σs vs = do
  let f :: SomeK (TVarOf) -> t (Maybe (SomeK TVarOf))
      f (SomeK var) = do
        replacement <- σs var
        case (replacement) of
          TVar rep | rep == var -> return (Just (SomeK var))
          _ -> return Nothing
  newvs <- mapM f vs
  return [v | (Just v) <- newvs]

instance Substitute TVarOf DMTypeOf (DMTypeOf k) where
  substitute σs Deleted = pure Deleted
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
  substitute σs (ForAll vs τ) = ForAll <$> (removeVars σs vs) <*> substitute σs τ
  substitute σs (DMTup τs) = DMTup <$> substitute σs τs
  substitute σs (DMMat nrm clp n m τ) = DMMat nrm clp <$> substitute σs n <*> substitute σs m <*> substitute σs τ
  substitute σs (DMChoice xs) = DMChoice <$> substitute σs xs
  substitute σs (NoFun (x)) = NoFun <$> substitute σs x
  substitute σs (Fun xs) = Fun <$> substitute σs xs
  substitute σs (x :∧: y) = (:∧:) <$> substitute σs x <*> substitute σs y


instance Substitute SVarOf SensitivityOf (Annotation a) where
  substitute σs (SensitivityAnnotation s) = SensitivityAnnotation <$> (substitute σs s)
  substitute σs (PrivacyAnnotation s) = PrivacyAnnotation <$> (substitute σs s)

instance Substitute SVarOf SensitivityOf (DMTypeOf k) where
  substitute σs Deleted = pure Deleted
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
  substitute σs (ForAll vs τ) = ForAll vs <$> substitute σs τ
  substitute σs (DMTup τs) = DMTup <$> substitute σs τs
  substitute σs (DMMat nrm clp n m τ) = DMMat nrm clp <$> substitute σs n <*> substitute σs m <*> substitute σs τ
  substitute σs (DMChoice xs) = DMChoice <$> substitute σs xs
  substitute σs (NoFun x) = NoFun <$> substitute σs x
  substitute σs (Fun xs) = Fun <$> substitute σs xs
  substitute σs (x :∧: y) = (:∧:) <$> substitute σs x <*> substitute σs y


instance Term TVarOf DMTypeOf where
  var x = TVar x
  isVar (TVar x) = Just x
  isVar _        = Nothing

instance DMExtra a => FreeVars TVarOf (WithRelev a) where
  freeVars (WithRelev _ a) = freeVars a

instance FreeVars TVarOf Symbol where
   freeVars a = []

instance (FreeVars v a, FreeVars v b) => FreeVars v (Either a b) where
  freeVars (Left aa) = freeVars aa
  freeVars (Right bb) = freeVars bb

instance (FreeVars v a, FreeVars v b) => FreeVars v (a :& b) where
  freeVars (a :@ b) = freeVars a <> freeVars b

instance FreeVars TVarOf Sensitivity where
  freeVars _ = mempty

instance FreeVars TVarOf JuliaType where
  freeVars _ = mempty

instance Typeable k => FreeVars TVarOf (SVarOf k) where
  freeVars = mempty

instance FreeVars TVarOf DMTypeOp where
  freeVars (UnaryNum op arg res) = freeVars arg <> freeVars res
  freeVars (BinaryNum op arg res) = freeVars arg <> freeVars res

instance Typeable a => FreeVars TVarOf (Annotation a) where
  freeVars (SensitivityAnnotation s) = freeVars s
  freeVars (PrivacyAnnotation s) = freeVars s

instance Typeable k => FreeVars TVarOf (DMTypeOf k) where
  freeVars Deleted = []
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
  freeVars (ForAll vs τ) = freeVars τ \\ vs
  freeVars (DMTup τs) = freeVars τs
  freeVars (DMMat nrm clp n m τ) = freeVars nrm <> freeVars clp <> freeVars τ
  freeVars (DMChoice choices) = freeVars choices
  freeVars (NoFun x) = freeVars x
  freeVars (Fun xs) = freeVars xs
  freeVars (x :∧: y) = freeVars x <> freeVars y


-- Given a list of "multi substitutions", i.e. substitutions of the form
-- [a := ListK [a1, a2, a3], b := ListK [b1, b2, b3], ...] and type τ,
-- it returns (Just [τ1, τ2, τ3]) where
--   τ1 = τ[a := a1, b := b1, ...]
--   τ2 = τ[a := a2, b := b2, ...]
-- And it returns Nothing if none of the substitutions could be applied.
--
-- NOTE: The given lists of replacements must all have the same length,
--       otherwise an error will be thrown.
duplicateTerm :: forall a v x t. (MonadInternalError t, MonadImpossible t, MonadWatch t, MonadTerm a t,  Substitute v a x, (v ~ VarFam a), FreeVars v x, KHashable v, KShow a, KShow v) => [SomeK (Sub v (ListK a))] -> x -> t (Maybe [x])
duplicateTerm subs τ = do
  let vars = [SomeK v | (SomeK (v := _)) <- subs]
  -- first we check if the term we want to duplicate actually contains any
  -- of the variables which we duplicate
  let (free :: [SomeK (VarFam a)]) = freeVars τ
  let noVarInFree = length (vars `intersect` free) == 0

  case noVarInFree of
    -- if it does not contain variables to duplicate we simply return it
    True -> return Nothing

    -- else we replace the given variables by new ones
    False -> do
      -- `f` takes a term x and replaces all occurences of `vars` by the i'th substitutions
      let f :: x -> Int -> t x
          f t i = do
            -- we extract the i'th substitutions from subs
            let varSubs = [(SomeK v , SomeK (xs !! i)) | SomeK (v := ListK xs) <- subs]
            -- we have to wrap this list of substitutions into a `Subs` container, since this is
            -- the format which is expected by the `↷` function which executes the actual substitution
            let varSubs' = Subs (H.fromList varSubs)
            varSubs' ↷ t

      -- we get the length of the substitions
      let sub_lengths = [length xs | SomeK (_ := ListK xs) <- subs]
      case sub_lengths of
        [] -> return Nothing
        (n:ns) -> case and ((== n) <$> ns) of
          False -> internalError $ "Encountered a 'duplication substitution' whose entries had different lengths:\n" <> show subs
          True -> do
            -- we execute the function f on τ, while taking the subs number {0, ..., n-1}
            τs <- mapM (f τ) [0..n-1]
            return (Just τs)


instance Substitute SVarOf SensitivityOf (SensitivityOf k) where
  substitute (σs :: forall k. (IsKind k) => SVarOf k -> t (SensitivityOf k)) s = substitute f s
    where f :: (IsKind l) => SymVar l -> t (SensitivityOf l)
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










class (FixedVars TVarOf x) => GoodConstraint (x :: *) where
instance (FixedVars TVarOf x) => GoodConstraint x where

class (FreeVars TVarOf x, Substitute TVarOf DMTypeOf x) => GoodConstraintContent (x :: *) where
instance (FreeVars TVarOf x, Substitute TVarOf DMTypeOf x) => GoodConstraintContent x where


class (MonadImpossible (t), MonadWatch (t), MonadLog t,
       MonadTerm DMTypeOf (t),
       MonadTermDuplication DMTypeOf (t),
       MonadTerm SensitivityOf (t),
       MonadState (Full) (t),
       MonadError DMException (t),
       MonadInternalError t,
       -- MonadConstraint' Symbol (TC) (t),
       -- MonadConstraint Symbol (MonadDMTC) (t),
       MonadConstraint (MonadDMTC) (t),
       MonadNormalize t,
       ContentConstraintOnSolvable t ~ GoodConstraintContent,
       ConstraintOnSolvable t ~ GoodConstraint
       -- LiftTC t
      ) => MonadDMTC (t :: * -> *) where

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

data NormalizationLevel = NormalForMode SolvingMode | NotNormal
  deriving (Eq)

data Watched a = Watched NormalizationLevel a

-- this is the action of Changed on NormalizationLevel
updateNormalizationLevel :: Changed -> NormalizationLevel -> NormalizationLevel
updateNormalizationLevel NotChanged a = a
updateNormalizationLevel IsChanged _ = NotNormal

instance Show a => Show (Watched a) where
  show (Watched NotNormal a) = "*" <> show a
  show (Watched (NormalForMode m) a) = "<" <> show m <> ">" <> show a

instance (MonadWatch t, Normalize t a) => Normalize t (Watched a) where
  normalize (Watched c a) =
    do resetChanged
       a' <- normalize a
       newc <- getChanged
       return (Watched (updateNormalizationLevel newc c) a')

data CtxStack v a = CtxStack
  {
    _topctx :: Ctx v a,
    _otherctxs :: [Ctx v a]
  }
type ConstraintCtx = AnnNameCtx (CtxStack Symbol (Watched (Solvable GoodConstraint GoodConstraintContent MonadDMTC)))
instance DictKey v => DictLike v x (CtxStack v x) where
  setValue k v (CtxStack d other) = CtxStack (setValue k v d) other
  getValue k (CtxStack d _) = getValue k d
  getAllKeys (CtxStack d _) = getAllKeys d
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


instance Typeable x => Cast (Either (Annotation SensitivityK) (Annotation PrivacyK)) (Annotation x) where
  cast e =
    let case1 = testEquality (typeRep @x) (typeRep @SensitivityK)
        case2 = testEquality (typeRep @x) (typeRep @PrivacyK)
    in case (case1,case2) of
      (Just Refl, _) -> case e of
                          Left e -> return e
                          Right _ -> error "Expected a sensitivity but got a privacy."
      (_ , Just Refl) -> case e of
                          Right e -> return e
                          Left _ -> error "Expected a privacy but got a sensitivity."
      _    -> impossible "Found an AnnotatedKind which was neither SensitivityK nor PrivacyK."

instance Typeable x => Cast (Either (WithRelev SensitivityK) (WithRelev PrivacyK)) (WithRelev x) where
  cast (Left (WithRelev i x)) = WithRelev i <$> cast @ (Either (DMTypeOf MainKind :& Annotation SensitivityK) (DMTypeOf MainKind :& Annotation PrivacyK)) (Left x)
  cast (Right (WithRelev i x)) = WithRelev i <$> cast @(Either (DMTypeOf MainKind :& Annotation SensitivityK) (DMTypeOf MainKind :& Annotation PrivacyK))  (Right x)



instance (Cast (Either a b) x) => Cast (Either (z :& a) (z :& b)) (z :& x) where
  cast (Left (x :@ e)) = (x :@) <$> cast @(Either a b) (Left e)
  cast (Right (x :@ e)) = (x :@) <$> cast @(Either a b) (Right e)

instance (Cast a b) => Cast (Maybe a) (Maybe b) where
  cast Nothing = pure Nothing
  cast (Just a) = Just <$> cast a


instance (MonadDMTC t) => Normalize t (WithRelev e) where
  normalize (WithRelev i x) = WithRelev i <$> normalize x



type TypeCtx extra = Ctx Symbol (WithRelev extra)
type TypeCtxSP = Either (TypeCtx SensitivityK) (TypeCtx PrivacyK)



data Watcher = Watcher Changed
  deriving (Generic)

data MetaCtx = MetaCtx
  {
    _sensVars :: KindedNameCtx SVarOf,
    _typeVars :: KindedNameCtx TVarOf,
    _sensSubs :: Subs SVarOf SensitivityOf,
    _typeSubs :: Subs TVarOf DMTypeOf,
    _constraints :: ConstraintCtx,
    -- cached state
    _fixedTVars :: [SingSomeK TVarOf]
  }
  deriving (Generic)

data TCState = TCState
  {
    _watcher :: Watcher,
    _logger :: DMLogger
  }
  deriving (Generic)

data Full = Full
  {
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


$(makeLenses ''AnnNameCtx)
$(makeLenses ''CtxStack)
$(makeLenses ''MetaCtx)
$(makeLenses ''Full)
$(makeLenses ''TCState)



forceLogStart :: MonadDMTC t => t ()
forceLogStart = do
  old <- (tcstate.logger.loggerCurrentSeverity) %%= (\old -> (old,Force))
  (tcstate.logger.loggerBackupSeverity) %= (\_ -> old)

forceLogEnd :: MonadDMTC t => t ()
forceLogEnd = do
  old <- use (tcstate.logger.loggerBackupSeverity)
  (tcstate.logger.loggerCurrentSeverity) %= (\_ -> old)


dmWithLogLocation :: MonadDMTC t => DMLogLocation -> t a -> t a
dmWithLogLocation l action = do
  oldloc <- use (tcstate.logger.loggerCurrentLocation)
  (tcstate.logger.loggerCurrentLocation) %= (\_ -> l)
  res <- action
  (tcstate.logger.loggerCurrentLocation) %= (\_ -> oldloc)
  return res

forceLog :: MonadDMTC t => String -> t ()
forceLog text = do
  loc <- use (tcstate.logger.loggerCurrentLocation)
  -- here we split the messages at line breaks (using `lines`)
  -- in order to get consistent looking output (every line has a header)
  let messages = DMLogMessage Force loc <$> lines text
  tcstate.logger.loggerMessages %= (messages <>)

dmlog :: MonadDMTC t => String -> t ()
dmlog text = do
  loc <- use (tcstate.logger.loggerCurrentLocation)
  sev <- use (tcstate.logger.loggerCurrentSeverity)
  -- here we split the messages at line breaks (using `lines`)
  -- in order to get consistent looking output (every line has a header)
  let messages = DMLogMessage sev loc <$> lines text
  tcstate.logger.loggerMessages %= (messages <>)

instance Monad m => MonadLog (TCT m) where
  log = dmlog
  withLogLocation loc action = dmWithLogLocation (fromString_DMLogLocation loc) action


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
  show (MetaCtx s t sσ tσ cs fixedT) =
       "- sens vars: " <> show s <> "\n"
    <> "- type vars: " <> show t <> "\n"
    -- <> "- cnst vars: " <> show c <> "\n"
    <> "- sens subs:   " <> show sσ <> "\n"
    <> "- type subs:   " <> show tσ <> "\n"
    <> "- fixed TVars: " <> show fixedT <> "\n"
    <> "- constraints:\n" <> show cs <> "\n"
    -- <> "- types:       " <> show γ <> "\n"

instance Show Watcher where
  show (Watcher changed) = show changed

instance Show (TCState) where
  show (TCState w l) = "- watcher: " <> show w <> "\n"
                       <> "- messages: " <> show l <> "\n"

instance Show (Full) where
  show (Full tcs m γ) = "\nState:\n" <> show tcs <> "\nMeta:\n" <> show m <> "\nTypes:\n" <> show γ <> "\n"


instance Default (CtxStack v a) where
  def = CtxStack def []
instance Default (Watcher) where
instance Default (TCState) where
instance Default (MetaCtx) where
instance Default (Full) where
  def = Full def def (Left def)



instance Semigroup NormalizationLevel where
  NotNormal <> a = NotNormal
  a <> NotNormal = NotNormal
  NormalForMode a <> NormalForMode b = NormalForMode (min a b)

instance Ord (NormalizationLevel) where
  NotNormal <= _ = True
  NormalForMode a <= NotNormal = False
  NormalForMode a <= NormalForMode b = a <= b

instance (SemigroupM t a) => SemigroupM t (Watched a) where
  (⋆) (Watched x a) (Watched y b) = Watched (x <> y) <$> a ⋆ b

instance (MonoidM t a) => MonoidM t (Watched a) where
  neutral = Watched (NormalForMode SolveAssumeWorst) <$> neutral

-- instance MonadInternalError t => MonoidM t (Watched a) where

instance (CheckNeutral t a) => CheckNeutral t (Watched a) where
  checkNeutral a = pure False

instance Monad t => (SemigroupM t (Solvable eC eC2 a)) where
  (⋆) (Solvable a) (Solvable b) = error "Trying to combine two constraints with the same name."
instance Monad t => (MonoidM t (Solvable eC eC2 a)) where
  neutral = error "Trying to get neutral of solvable"
instance Monad t => (CheckNeutral t (Solvable eC eC2 a)) where
  checkNeutral a = pure False


instance Monad m => MonadTerm DMTypeOf (TCT m) where
  type VarFam DMTypeOf = TVarOf
  getSubs = view (meta.typeSubs) <$> get
  addSub σ = do
    σs <- use (meta.typeSubs)
    -- traceM ("/ Type: I have the subs " <> show σs <> ", and I want to add: " <> show σ)
    σs' <- σs ⋆ singletonSub σ
    -- traceM ("\\ Type: I now have: " <> show σs')
    meta.typeSubs .= σs'
    meta.typeVars %= (removeNameBySubstitution σ)

    -- remove fixed var
    meta.fixedTVars %= removeKindedNameBySubstitution σ
  newVar = TVar <$> newTVar "τ"
  getFixedVars _ = do
    vars <- use (meta.fixedTVars)
    let somes = [SomeK v | SingSomeK v <- vars]
    return (filterSomeK somes)

instance Monad m => MonadTerm SensitivityOf (TCT m) where
  type VarFam SensitivityOf = SVarOf
  getSubs = view (meta.sensSubs) <$> get
  addSub σ = do
    σs <- use (meta.sensSubs)
    -- traceM ("I have the subs " <> show σs <> ", and I want to add: " <> show σ)
    σs' <- σs ⋆ singletonSub σ
    meta.sensSubs .= σs'
    meta.sensVars %= (removeNameBySubstitution σ)
  newVar = coerce <$> svar <$> newSVar "s"
  getFixedVars _ = return mempty

instance Monad m => MonadTermDuplication DMTypeOf (TCT m) where
  duplicateAllConstraints subs = do

    ------------------------------------
    -- duplicating all constraints which contain the given vars
    --
    -- NOTE: We only duplicate in the top ConstraintCtx in the CtxStack.
    --       We might want to check that the vars actually do
    --       not appear in the lower ConstraintCtx's.
    --       (Or duplicate them there too?)
    --
    -- 1. get all the constraint (names) from the ctx stack
    (AnnNameCtx _ ctrs) <- use (meta.constraints)
    let ctr_names = getAllKeys ctrs

    -- 2. Build a function which takes a constraint name,
    --    and duplicates the corresponding constraint if necessary
    let f :: Symbol -> TCT m ()
        f name = do
          case getValue name ctrs of
            Nothing -> return ()
            Just (Watched _ (Solvable (ctr :: c a))) -> do
              duplicated <- duplicateTerm subs (runConstr ctr)
              case duplicated of
                -- if the constraint was not actually duplicated,
                -- this means that the variables did not occur inside
                -- and we do not have to change this constraint
                Nothing -> return ()

                -- if we do get duplicated constraints, we discharge the
                -- actual constraint, and add a new constraint for every copy
                Just duplicated -> do dischargeConstraint name
                                      mapM_ (\newctr -> addConstraint (Solvable (constr @c newctr))) duplicated

    --
    -- 3. Apply the function to all constraint names
    mapM f ctr_names


    ------------------------------------
    -- set all variables to `Deleted`:
    --
    -- 1. build subs which set them to deleted, and put the actions of doing so into a list
    let σ = [addSub (x := Deleted) | SomeK (x := _) <- subs]

    -- 2. execute all these (monadic) actions
    sequence σ

    -- And we are done.
    return ()

getFixedVarsOfSolvable :: Solvable GoodConstraint GoodConstraintContent MonadDMTC -> [SingSomeK TVarOf]
getFixedVarsOfSolvable (Solvable c) =
      -- compute the fixed vars of this constraint
      -- and add them to the cached list
      let newFixed = fixedVars @_ @TVarOf c
      in [SingSomeK v | SomeK v <- newFixed]

-- Recompute fixed vars
-- NOTE: We only look at the topmost constraintctx in the ctxstack.
recomputeFixedVars :: MonadDMTC t => t ()
recomputeFixedVars = do
  (Ctx (MonCom constrs)) <- use (meta.constraints.anncontent.topctx)
  let constrs2 = H.toList constrs
  let constrs3 = [c | (_ , Watched _ c) <- constrs2]
  meta.fixedTVars %= (\_ -> constrs3 >>= getFixedVarsOfSolvable)
  return ()


instance Monad m => MonadConstraint (MonadDMTC) (TCT m) where
  type ConstraintBackup (TCT m) = (Ctx Symbol (Watched (Solvable GoodConstraint GoodConstraintContent MonadDMTC)))
  type ContentConstraintOnSolvable (TCT m) = GoodConstraintContent
  type ConstraintOnSolvable (TCT m) = GoodConstraint
  addConstraint (Solvable c) = do
      -- compute the fixed vars of this constraint
      -- and add them to the cached list
      let newFixed = fixedVars @_ @TVarOf c
      meta.fixedTVars <>= [SingSomeK v | SomeK v <- newFixed]

      -- add the constraint to the constraint list
      meta.constraints %%= (newAnnName "constr" (Watched NotNormal (Solvable c)))

  getUnsolvedConstraintMarkNormal mode = do
    (Ctx (MonCom constrs)) <- use (meta.constraints.anncontent.topctx)
    let constrs2 = H.toList constrs
    let changed = filter (\(a, Watched state constr) -> (state < NormalForMode mode)) constrs2
    case changed of
      [] -> return Nothing
      ((name,Watched _ constr):_) -> do
        meta.constraints.anncontent.topctx %= (setValue name (Watched (NormalForMode mode) constr))
        return (Just (name, constr))

  dischargeConstraint name = do
    meta.constraints.anncontent.topctx %= (deleteValue name)
    recomputeFixedVars

  failConstraint name = do
    (AnnNameCtx n cs) <- use (meta.constraints)
    let c = getValue name cs
    throwError (UnsatisfiableConstraint (show c))

  updateConstraint name c = do
    meta.constraints %= (\(AnnNameCtx n cs) -> AnnNameCtx n (setValue name (Watched NotNormal c) cs))
    recomputeFixedVars

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
    let f :: (Watched (Solvable GoodConstraint GoodConstraintContent MonadDMTC)) -> Maybe (c a)
        f (Watched _ (Solvable (c :: c' a'))) = case testEquality (typeRep @(c a)) (typeRep @(c' a')) of
          Just Refl -> Just c
          Nothing -> Nothing

    let cs' = H.toList cs
        cs'' = second f <$> cs'
    return [(name,c) | (name, Just c) <- cs'' ]

  logPrintConstraints = do
    ctrs <- use (meta.constraints.anncontent)
    log $ "## Constraints ##"
    log $ show ctrs
    log $ "## ----------- ##"

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










supremum :: (IsT isT t, HasNormalize isT (a k, a k, a k), MonadConstraint isT (t), MonadTerm a (t), Solve isT IsSupremum (a k, a k, a k), SingI k, Typeable k, ContentConstraintOnSolvable t (a k, a k, a k), ConstraintOnSolvable t (IsSupremum (a k, a k, a k))) => (a k) -> (a k) -> t (a k)
supremum x y = do
  (z :: a k) <- newVar
  addConstraint (Solvable (IsSupremum (x, y, z)))
  return z

infimum :: (IsT isT t, HasNormalize isT (a k, a k, a k), MonadConstraint isT (t), MonadTerm a (t), Solve isT IsInfimum (a k, a k, a k), SingI k, Typeable k, ContentConstraintOnSolvable t (a k, a k, a k), ConstraintOnSolvable t (IsInfimum (a k, a k, a k))) => (a k) -> (a k) -> t (a k)
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

instance MonadDMTC t => Normalize t (Annotation a) where
  normalize (SensitivityAnnotation s) = SensitivityAnnotation <$> normalize s
  normalize (PrivacyAnnotation s) = PrivacyAnnotation <$> normalize s

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

newPVar = do
   p1 ::Sensitivity <- newVar
   p2 :: Sensitivity <- newVar
   return (p1, p2)


  -- where f names = let (τ , names') = newName hint names
  --                 in (TVar τ, names')


  -- state (over meta0 f)
  -- where f (Meta1Ctx s t c) =
  --         let (τ , s') = newName hint s
  --         in (TVar τ , Meta1Ctx s t c)

-- instance (MonadDMTC t, GoodConstraintContent a) => ConstraintOnSolvable t a where

------------------------------------------------------------------------
-- unification of sensitivities

instance FixedVars (TVarOf) (IsEqual (Sensitivity,Sensitivity)) where
  fixedVars = mempty

instance FixedVars (TVarOf) (IsLessEqual (Sensitivity,Sensitivity)) where
  fixedVars = mempty

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

createDMType :: MonadDMTC t => JuliaType -> t (DMTypeOf MainKind)
 -- NOTE: defaulting to non-const might or might not be what we want to do here.
createDMType (JuliaType "Integer") = do
  return (NoFun (Numeric (NonConst DMInt)))
createDMType (JuliaType "Real") = do
  return (NoFun (Numeric (NonConst DMReal)))
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
-- truncateExtra :: Annotation f -> Annotation e -> Annotation f
-- truncateExtra η (SensitivityAnnotation η_old) = 
--   (case η_old == zeroId of
--       True -> zeroId
--       _    -> η)
-- truncateExtra η η_old =

scaleExtra :: forall (a :: AnnotationKind). Sensitivity -> Annotation a -> Annotation a
scaleExtra η (SensitivityAnnotation s) = SensitivityAnnotation (η ⋅! s)
scaleExtra η (PrivacyAnnotation (ε, δ)) = PrivacyAnnotation (η ⋅! ε , η ⋅! δ)

-- scaleSens :: forall (a :: AnnotationKind). Sensitivity -> Sensitivi -> Annotation a
-- scaleSens = undefined

normalizeAnn :: forall t k. (MonadDMTC t) => DMTypeOf k -> t (DMTypeOf k)
normalizeAnn (TVar a) = pure $ TVar a
normalizeAnn (Fun as) = do
  let normalizeInside (f :@ annot) = (:@ annot) <$> normalizeAnn f
  Fun <$> mapM normalizeInside as
normalizeAnn (NoFun fs) = pure $ NoFun fs
normalizeAnn (a :∧: b) = do
  a' <- normalizeAnn a
  b' <- normalizeAnn b
  case (a', b') of
    (Fun xs, Fun ys) -> pure $ Fun (xs <> ys)
    (NoFun x, NoFun y) -> do -- z <- infimum @MonadDMTC @t x y
                                             z <- newVar
                                             addConstraint (Solvable (IsInfimum (x, y, z)))
                                             return (NoFun z)
    (_ , _) -> return (a' :∧: b')
normalizeAnn (xs :->: y) = do
  let normalizeInside (x :@ annot) = (:@ annot) <$> normalizeAnn x
  (:->:) <$> mapM normalizeInside xs <*> normalizeAnn y
normalizeAnn (xs :->*: y) = do
  let normalizeInside (x :@ annot) = (:@ annot) <$> normalizeAnn x
  (:->*:) <$> mapM normalizeInside xs <*> normalizeAnn y
normalizeAnn x = pure x

-- normalizeInsideAnn :: MonadDMTC t => DMTypeOf (AnnotatedKind a) -> t (DMTypeOf (AnnotatedKind a))
-- normalizeInsideAnn (TVar a) = undefined

-- normalizeRewritingDMType :: MonadDMTC t -> 
-- normalizeRewritingDMType :: (IsT MonadDMTC t, (Solve MonadDMTC IsInfimum (DMType, DMType, DMType))) => DMTypeOf k -> t (DMTypeOf k)
-- normalizeRewritingDMType (TVar a) = pure $ TVar a
-- normalizeRewritingDMType (TVar a) = pure $ TVar a
-- normalizeRewritingDMType (TVar a) = pure $ TVar a
-- normalizeRewritingDMType (TVar a) = pure $ TVar a
-- normalizeRewritingDMType (TVar a) = pure $ TVar a




