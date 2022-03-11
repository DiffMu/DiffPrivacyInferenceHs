
{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Core.Unification where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Abstract.Data.ErrorReporting
import DiffMu.Core.Definitions
import DiffMu.Core.TC
import DiffMu.Core.Logging

import DiffMu.Core.Symbolic

import Data.HashMap.Strict as H
import Control.Monad.Trans.Except (throwE)

default (String)

-------------------------------------------------------------------
-- Unification of dmtypes
--


newtype WrapMessageINC e a = WrapMessageINC a

instance Show a => Show (WrapMessageINC e a) where show (WrapMessageINC a) = show a
instance ShowPretty a => ShowPretty (WrapMessageINC e a) where showPretty (WrapMessageINC a) = showPretty a

instance (Show e, MonadInternalError m, MonadLog m, Normalize (INCResT e m) a) => Normalize m (WrapMessageINC e a) where
  normalize e (WrapMessageINC x) = do
    let n :: INCResT e m a
        n = normalize e x
    n' <- runExceptT (runINCResT n)
    case n' of
      Left sr -> case sr of
        Wait' -> return (WrapMessageINC x)
        Fail' e' -> internalError ("While normalizing inside INCRes got a fail :" <> show e')
      Right a -> return (WrapMessageINC a)

    -- return (WrapMessageINC n')


newtype WrapMessageINCRev e a = WrapMessageINCRev a

instance Show a => Show (WrapMessageINCRev e a) where show (WrapMessageINCRev a) = show a
instance ShowPretty a => ShowPretty (WrapMessageINCRev e a) where showPretty (WrapMessageINCRev a) = showPretty a

instance (Show e, MonadInternalError m, MonadLog m, Normalize m a) => Normalize (INCResT e m) (WrapMessageINCRev e a) where
  normalize e (WrapMessageINCRev x) =
    let y = normalize @m e x
    in INCResT (ExceptT (fmap (Right . WrapMessageINCRev) y))


-------------------------------------------
-- INC functionality needed for
-- unification.
--

class HasUnificationError e a where
  unificationError' :: Show a => a -> a -> e


data StoppingReason e = Wait' | Fail' e

newtype INCResT e m a = INCResT {runINCResT :: ExceptT (StoppingReason e) m a}
  -- Finished' (m a) | Wait' | Fail' e
  deriving (Functor, Applicative, Monad, MonadError (StoppingReason e))

instance (Show e, MonadInternalError m, MonadLog m) => MonadLog (INCResT e m) where
  log             = liftINC . log 
  debug           = liftINC . debug
  info            = liftINC . info
  warn            = liftINC . warn
  logForce        = liftINC . logForce
  withLogLocation = \a b -> b
  -- persistentError = \(DMPersistentMessage msg) -> liftINC (persistentError $ DMPersistentMessage $ WrapMessageINC @e (msg))

-- instance MonadInternalError m => MonadInternalError (INCResT e m) where
--   internalError str = undefined



instance HasUnificationError DMException a where
  unificationError' = UnificationError

instance HasUnificationError e a => HasUnificationError (StoppingReason e) a where
  unificationError' a b = Fail' (unificationError' a b)

-- instance MonadLog m => MonadLog (ExceptT e m) where
--   log a = ExceptT (log a >> pure (Right ()))
--   debug a = ExceptT (debug a >> pure (Right ()))
--   info a = ExceptT (info a >> pure (Right ()))
--   warn a = ExceptT (warn a >> pure (Right ()))
--   logForce a = ExceptT (logForce a >> pure (Right ()))
--   withLogLocation s a = a -- TODO: Make this proper?
--   persistentError = undefined



---------------------------------
-- The actual unification
--
-- | The reason for the implementation using incremental computation is
--   that unification does not always succeed:
--   When terms such as `(v :∧: w)` are unified,  usually we cannot do anything,
--   but have to wait for `v` or `w` to be known in more detail.
--

normalizeᵢ :: Normalize t a => a -> INCResT e t a
normalizeᵢ a = liftINC (normalizeExact a)

class Monad t => Unifyᵢ t a where
  unifyᵢ_Msg :: MessageLike t m => m -> a -> a -> t a

unifyᵢMsg :: (Unifyᵢ (INCResT e t) a, Normalize (t) a, MessageLike (INCResT e t) msg) => msg -> a -> a -> (INCResT e t a)
unifyᵢMsg name a b = (chainM2 (unifyᵢ_Msg name) (normalizeᵢ a) (normalizeᵢ b))

unifyᵢ :: (Unifyᵢ (INCResT e t) a, Normalize (t) a) => a -> a -> (INCResT e t a)
unifyᵢ = unifyᵢMsg ()

liftINC :: Functor m => m a -> INCResT e m a
liftINC a = INCResT (ExceptT (fmap Right a))

-- we define the 'incremental' version of unification

instance (Monad t, HasUnificationError e JuliaType, MonadError e t, MonadLog t) => Unifyᵢ t JuliaType where
  unifyᵢ_Msg name a b | a == b = pure a
  unifyᵢ_Msg name t s = throwError (unificationError' t s)

instance (Show e, MonadDMTC t) => Unifyᵢ (INCResT e t) Sensitivity where
  unifyᵢ_Msg name a b = liftINC $ unify (WrapMessageINC @e name) a b

instance (Monad t, Unifyᵢ t a, Unifyᵢ t b) => Unifyᵢ t (a,b) where
  unifyᵢ_Msg name (a1,b1) (a2,b2) = (,) <$> (unifyᵢ_Msg name a1 a2) <*> (unifyᵢ_Msg name b1 b2)

instance (Unifyᵢ isT a, Unifyᵢ isT b) => Unifyᵢ isT (a :@ b) where
  unifyᵢ_Msg name (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unifyᵢ_Msg name a₁ a₂ <*> unifyᵢ_Msg name e₁ e₂

instance (HasUnificationError e [a], MonadLog t, MonadError e t, Show a, Unifyᵢ t a) => Unifyᵢ t [a] where
  unifyᵢ_Msg name xs ys | length xs == length ys = mapM (uncurry (unifyᵢ_Msg name)) (zip xs ys)
  unifyᵢ_Msg name xs ys = throwError (unificationError' xs ys)

instance (HasUnificationError e (Maybe a), MonadLog t, MonadError e t, Show a, Unifyᵢ t a) => Unifyᵢ t (Maybe a) where
  unifyᵢ_Msg name Nothing Nothing = pure Nothing
  unifyᵢ_Msg name (Just a) (Just b) = Just <$> unifyᵢ_Msg name a b
  unifyᵢ_Msg name t s = throwError (unificationError' t s)


instance MonadDMTC t => Unifyᵢ (INCResT DMException t) (DMTypeOf k) where
  unifyᵢ_Msg name DMAny DMAny                   = pure DMAny
  unifyᵢ_Msg name DMReal DMReal                 = pure DMReal
  unifyᵢ_Msg name DMBool DMBool                 = pure DMBool
  unifyᵢ_Msg name DMInt DMInt                   = pure DMInt
  unifyᵢ_Msg name DMData DMData                 = pure DMData
  unifyᵢ_Msg name (Numeric t) (Numeric s)       = Numeric <$> unifyᵢMsg name t s
  unifyᵢ_Msg name (NonConst) (NonConst)         = pure NonConst
  unifyᵢ_Msg name (Const η₁) (Const η₂)         = Const <$> liftINC (unify (WrapMessageINC @DMException name) η₁ η₂)
  unifyᵢ_Msg name (Num a0 c0) (Num a1 c1)       = Num <$> unifyᵢMsg name a0 a1 <*> unifyᵢMsg name c0 c1
  unifyᵢ_Msg name (as :->: a) (bs :->: b)       = (:->:) <$> unifyᵢMsg name as bs <*> unifyᵢMsg name a b
  unifyᵢ_Msg name (as :->*: a) (bs :->*: b)     = (:->*:) <$> unifyᵢMsg name as bs <*> unifyᵢMsg name a b
  unifyᵢ_Msg name (DMTup as) (DMTup bs)         = DMTup <$> unifyᵢMsg name as bs
  unifyᵢ_Msg name (TVar x) (TVar y) | x == y    = pure $ TVar x
  unifyᵢ_Msg name (TVar x) t                    = liftINC (addSub (x := t)) >> pure t
  unifyᵢ_Msg name t (TVar x)                    = liftINC (addSub (x := t)) >> pure t
  unifyᵢ_Msg name L1 L1                         = pure L1
  unifyᵢ_Msg name L2 L2                         = pure L2
  unifyᵢ_Msg name LInf LInf                     = pure LInf
  unifyᵢ_Msg name U U                           = pure U
  unifyᵢ_Msg name Vector Vector                 = pure Vector
  unifyᵢ_Msg name Gradient Gradient             = pure Gradient
  unifyᵢ_Msg name (Matrix r1) (Matrix r2)       = Matrix <$> unifyᵢMsg name r1 r2
  unifyᵢ_Msg name (Clip k) (Clip s)             = Clip <$> unifyᵢMsg name k s
  unifyᵢ_Msg name (DMContainer k1 nrm1 clp1 n1 τ1) (DMContainer k2 nrm2 clp2 n2 τ2) =
      DMContainer <$> unifyᵢMsg name k1 k2 <*> unifyᵢMsg name nrm1 nrm2 <*> unifyᵢMsg name clp1 clp2 <*> unifyᵢMsg name n1 n2 <*> unifyᵢMsg name τ1 τ2
  unifyᵢ_Msg name (DMModel m1) (DMModel m2) =
      DMModel <$> unifyᵢMsg name m1 m2
  unifyᵢ_Msg name (NoFun a) (v :∧: w)              = do
    res0 <- unifyᵢMsg name (NoFun a) v
    res1 <- unifyᵢMsg name res0 w
    return res1
  unifyᵢ_Msg name (v :∧: w) (NoFun b)              = do
    res0 <- unifyᵢMsg name (NoFun b) v
    res1 <- unifyᵢMsg name res0 w
    return res1
  unifyᵢ_Msg name (NoFun x) (NoFun y)              = NoFun <$> unifyᵢMsg name x y
  unifyᵢ_Msg name (Fun xs) (Fun ys)                = Fun <$> unifyᵢMsg name xs ys
  unifyᵢ_Msg name (Fun _) (v :∧: w)                = throwError Wait'
  unifyᵢ_Msg name (v :∧: w) (Fun _)                = throwError Wait'
  unifyᵢ_Msg name (_ :∧: _) (v :∧: w)              = throwError Wait'
  unifyᵢ_Msg name t s                              = throwError (Fail' $ UnificationError t s)


instance Monad t => Normalize t JuliaType where
  normalize nt = pure


instance Monad t => Unify t () where
  unify_ _ _ _ = return ()


instance MonadDMTC t => Unify t JuliaType where
  unify_ name a b | a == b = pure a
  unify_ name t s = throwUnlocatedError (UnificationError t s)


instance MonadDMTC t => Unify t (Annotation e) where
  -- NOTE: we can use the unify_ (with underscore) function here,
  -- because we do not have to normalize the just normalized arguments
  unify_ name (SensitivityAnnotation s) (SensitivityAnnotation t) = SensitivityAnnotation <$> unify_ name s t
  unify_ name (PrivacyAnnotation s) (PrivacyAnnotation t) = PrivacyAnnotation <$> unify_ name s t

-- TODO: Check, is i <> j what we want to do here?
-- instance Unify MonadDMTC e => Unify MonadDMTC (WithRelev e) where
--   unify_ (WithRelev i e) (WithRelev j f)  = WithRelev (i <> j) <$> unify_ e f

instance MonadDMTC t => Unify t (WithRelev e) where
  unify_ name (WithRelev i e) (WithRelev j f)  = WithRelev (i <> j) <$> unify_ name e f

-- Unification of DMTypes (of any kind k) is given by:
instance (Typeable k, MonadDMTC t) => Unify t (DMTypeOf k) where
  unify_ name a b = do
    withLogLocation "Unification" $ debug ("Unifying " <> show a <> " ==! "<> show b)
    res <- runExceptT $ runINCResT $ unifyᵢ_Msg @(INCResT DMException t) (WrapMessageINCRev @DMException name) a b
    case res of
      Left (Wait')   -> do
        withLogLocation "Unification" $ debug ("Got wait in unify on " <> show a <> " ==! "<> show b)
        liftTC ((a ==! b) (WrapMessageRevId name))
        return a
      Left (Fail' e) -> throwUnlocatedError e
      Right a -> return a

-- Above we implictly use unification of terms of the type (a :@ b).
-- These are unified entry-wise:
instance (Unify isT a, Unify isT b) => Unify isT (a :@ b) where
  unify_ name (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unify_ name a₁ a₂ <*> unify_ name e₁ e₂

-- Similarly, lists of terms are unified elements wise,
-- but they only match if they are of the same lenght:
instance (HasUnificationError e [a], MonadError e t, Show a, Unify t a, MonadLog t) => Unify t [a] where
  unify_ name xs ys | length xs == length ys = mapM (uncurry (unify_ name)) (zip xs ys)
  unify_ name xs ys = throwError (unificationError' xs ys)

instance Typeable k => FixedVars TVarOf (IsEqual (DMTypeOf k, DMTypeOf k)) where
  fixedVars _ = mempty

-- Using the unification instance, we implement solving of the `IsEqual` constraint for DMTypes.
instance Solve MonadDMTC IsEqual (DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ name (IsEqual (a,b)) = do
    res <- runExceptT $ runINCResT $ unifyᵢ_Msg @(INCResT DMException _) (Just name) a b
    case res of
      Left (Wait')   -> return ()
      Left (Fail' e) -> throwUnlocatedError e
      Right a -> dischargeConstraint name


instance Solve MonadDMTC IsLessEqual (Sensitivity, Sensitivity) where
  solve_ Dict _ name (IsLessEqual (s1, s2)) = solveLessEqualSensitivity s1 s2
    where
      getVal :: Sensitivity -> Maybe SymVal
      getVal a@(SingleKinded (LinCom (MonCom as))) = case H.toList as of
         [(MonCom aterm, av)] -> case H.toList aterm of
                                      [] -> (Just av)
                                      _ -> Nothing
         [] -> (Just zeroId)
         _ -> Nothing
      solveLessEqualSensitivity :: IsT MonadDMTC t => Sensitivity -> Sensitivity -> t ()
      solveLessEqualSensitivity a b | a == b = dischargeConstraint name
      solveLessEqualSensitivity a b = case getVal a of
         Just av -> case getVal b of
                         Just bv -> case av == Infty of
                                         True -> (b ==! constCoeff Infty) (Just name) >> dischargeConstraint name
                                         False -> case (av <= bv) of
                                                       True -> dischargeConstraint name
                                                       False -> failConstraint name
                         Nothing -> return ()
         Nothing -> return ()
         

-------------------------------------------------------------------
-- Monadic monoid structure on dmtypes
--

-- monoid structure using infimum

instance (IsT MonadDMTC t) => SemigroupM (t) (DMTypeOf MainKind) where
  (⋆) x y = return (x :∧: y)

instance (IsT MonadDMTC t) => MonoidM (t) (DMTypeOf MainKind) where
  neutral = newVar


-- An optimized check for whether a given DMType is a neutral does not create new typevariables,
-- but simply checks if the given DMType is one.
instance (SingI k, Typeable k, IsT MonadDMTC t) => (CheckNeutral (t) (DMTypeOf k)) where
  checkNeutral (TVar x) = return True
  checkNeutral (_) = return False

-- Old semigroup structure by unification

