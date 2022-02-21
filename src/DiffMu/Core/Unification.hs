
{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Core.Unification where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.TC
import DiffMu.Core.Logging

import DiffMu.Core.Symbolic

import Data.HashMap.Strict as H

-------------------------------------------------------------------
-- Unification of dmtypes
--


-------------------------------------------
-- INC functionality needed for
-- unification.
--

class HasUnificationError e a where
  unificationError' :: Show a => a -> a -> e


data StoppingReason e = Wait' | Fail' e

newtype INCResT e m a = INCResT {runINCResT :: ExceptT (StoppingReason e) m a}
  -- Finished' (m a) | Wait' | Fail' e
  deriving (Functor, Applicative, Monad, MonadError (StoppingReason e), MonadLog)

instance HasUnificationError DMException a where
  unificationError' = UnificationError

instance HasUnificationError e a => HasUnificationError (StoppingReason e) a where
  unificationError' a b = Fail' (unificationError' a b)

instance MonadLog m => MonadLog (ExceptT e m) where
  log a = ExceptT (log a >> pure (Right ()))
  debug a = ExceptT (debug a >> pure (Right ()))
  info a = ExceptT (info a >> pure (Right ()))
  warn a = ExceptT (warn a >> pure (Right ()))
  logForce a = ExceptT (logForce a >> pure (Right ()))
  withLogLocation s a = a -- TODO: Make this proper?



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
  unifyᵢ_ :: a -> a -> t a

unifyᵢ :: (Unifyᵢ (INCResT e t) a, Normalize (t) a) => a -> a -> (INCResT e t a)
unifyᵢ a b = (chainM2 unifyᵢ_ (normalizeᵢ a) (normalizeᵢ b))

liftINC :: Functor m => m a -> INCResT e m a
liftINC a = INCResT (ExceptT (fmap Right a))

-- we define the 'incremental' version of unification

instance (Monad t, HasUnificationError e JuliaType, MonadError e t, MonadLog t) => Unifyᵢ t JuliaType where
  unifyᵢ_ a b | a == b = pure a
  unifyᵢ_ t s = throwError (unificationError' t s)

instance MonadDMTC t => Unifyᵢ (INCResT e t) Sensitivity where
  unifyᵢ_ a b = liftINC $ unify a b

instance (Monad t, Unifyᵢ t a, Unifyᵢ t b) => Unifyᵢ t (a,b) where
  unifyᵢ_ (a1,b1) (a2,b2) = (,) <$> (unifyᵢ_ a1 a2) <*> (unifyᵢ_ b1 b2)

instance (Unifyᵢ isT a, Unifyᵢ isT b) => Unifyᵢ isT (a :@ b) where
  unifyᵢ_ (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unifyᵢ_ a₁ a₂ <*> unifyᵢ_ e₁ e₂

instance (HasUnificationError e [a], MonadLog t, MonadError e t, Show a, Unifyᵢ t a) => Unifyᵢ t [a] where
  unifyᵢ_ xs ys | length xs == length ys = mapM (uncurry unifyᵢ_) (zip xs ys)
  unifyᵢ_ xs ys = throwError (unificationError' xs ys)

instance (HasUnificationError e (Maybe a), MonadLog t, MonadError e t, Show a, Unifyᵢ t a) => Unifyᵢ t (Maybe a) where
  unifyᵢ_ Nothing Nothing = pure Nothing
  unifyᵢ_ (Just a) (Just b) = Just <$> unifyᵢ_ a b
  unifyᵢ_ t s = throwError (unificationError' t s)


instance MonadDMTC t => Unifyᵢ (INCResT DMException t) (DMTypeOf k) where
  unifyᵢ_ DMAny DMAny                   = pure DMAny
  unifyᵢ_ DMReal DMReal                 = pure DMReal
  unifyᵢ_ DMBool DMBool                 = pure DMBool
  unifyᵢ_ DMInt DMInt                   = pure DMInt
  unifyᵢ_ DMData DMData                 = pure DMData
  unifyᵢ_ (Numeric t) (Numeric s)       = Numeric <$> unifyᵢ t s
  unifyᵢ_ (NonConst) (NonConst)         = pure NonConst
  unifyᵢ_ (Const η₁) (Const η₂)         = Const <$> liftINC (unify η₁ η₂)
  unifyᵢ_ (Num a0 c0) (Num a1 c1)       = Num <$> unifyᵢ a0 a1 <*> unifyᵢ c0 c1
  unifyᵢ_ (as :->: a) (bs :->: b)       = (:->:) <$> unifyᵢ as bs <*> unifyᵢ a b
  unifyᵢ_ (as :->*: a) (bs :->*: b)     = (:->*:) <$> unifyᵢ as bs <*> unifyᵢ a b
  unifyᵢ_ (DMTup as) (DMTup bs)         = DMTup <$> unifyᵢ as bs
  unifyᵢ_ (TVar x) (TVar y) | x == y    = pure $ TVar x
  unifyᵢ_ (TVar x) t                    = liftINC (addSub (x := t)) >> pure t
  unifyᵢ_ t (TVar x)                    = liftINC (addSub (x := t)) >> pure t
  unifyᵢ_ L1 L1                         = pure L1
  unifyᵢ_ L2 L2                         = pure L2
  unifyᵢ_ LInf LInf                     = pure LInf
  unifyᵢ_ U U                           = pure U
  unifyᵢ_ Vector Vector                 = pure Vector
  unifyᵢ_ Gradient Gradient             = pure Gradient
  unifyᵢ_ (Matrix r1) (Matrix r2)       = Matrix <$> unifyᵢ r1 r2
  unifyᵢ_ (Clip k) (Clip s)             = Clip <$> unifyᵢ k s
  unifyᵢ_ (DMContainer k1 nrm1 clp1 n1 τ1) (DMContainer k2 nrm2 clp2 n2 τ2) =
      DMContainer <$> unifyᵢ k1 k2 <*> unifyᵢ nrm1 nrm2 <*> unifyᵢ clp1 clp2 <*> unifyᵢ n1 n2 <*> unifyᵢ τ1 τ2
  unifyᵢ_ (DMModel m1 τ1) (DMModel m2 τ2) =
      DMModel <$> unifyᵢ m1 m2 <*> unifyᵢ τ1 τ2
  unifyᵢ_ (NoFun a) (v :∧: w)              = do
    res0 <- unifyᵢ (NoFun a) v
    res1 <- unifyᵢ res0 w
    return res1
  unifyᵢ_ (v :∧: w) (NoFun b)              = do
    res0 <- unifyᵢ (NoFun b) v
    res1 <- unifyᵢ res0 w
    return res1
  unifyᵢ_ (NoFun x) (NoFun y)              = NoFun <$> unifyᵢ x y
  unifyᵢ_ (Fun xs) (Fun ys)                = Fun <$> unifyᵢ xs ys
  unifyᵢ_ (Fun _) (v :∧: w)                = throwError Wait'
  unifyᵢ_ (v :∧: w) (Fun _)                = throwError Wait'
  unifyᵢ_ (_ :∧: _) (v :∧: w)              = throwError Wait'
  unifyᵢ_ t s                              = throwError (Fail' $ UnificationError t s)


instance Monad t => Normalize t JuliaType where
  normalize nt = pure


instance Monad t => Unify t () where
  unify_ _ _ = return ()


instance MonadDMTC t => Unify t JuliaType where
  unify_ a b | a == b = pure a
  unify_ t s = throwError (UnificationError t s)


instance MonadDMTC t => Unify t (Annotation e) where
  -- NOTE: we can use the unify_ (with underscore) function here,
  -- because we do not have to normalize the just normalized arguments
  unify_ (SensitivityAnnotation s) (SensitivityAnnotation t) = SensitivityAnnotation <$> unify_ s t
  unify_ (PrivacyAnnotation s) (PrivacyAnnotation t) = PrivacyAnnotation <$> unify_ s t

-- TODO: Check, is i <> j what we want to do here?
-- instance Unify MonadDMTC e => Unify MonadDMTC (WithRelev e) where
--   unify_ (WithRelev i e) (WithRelev j f)  = WithRelev (i <> j) <$> unify_ e f

instance MonadDMTC t => Unify t (WithRelev e) where
  unify_ (WithRelev i e) (WithRelev j f)  = WithRelev (i <> j) <$> unify_ e f

-- Unification of DMTypes (of any kind k) is given by:
instance (Typeable k, MonadDMTC t) => Unify t (DMTypeOf k) where
  unify_ a b = do
    withLogLocation "Unification" $ debug ("Unifying " <> show a <> " ==! "<> show b)
    res <- runExceptT $ runINCResT $ unifyᵢ_ @(INCResT DMException t) a b
    case res of
      Left (Wait')   -> do
        withLogLocation "Unification" $ debug ("Got wait in unify on " <> show a <> " ==! "<> show b)
        liftTC (a ==! b)
        return a
      Left (Fail' e) -> throwError e
      Right a -> return a

-- Above we implictly use unification of terms of the type (a :@ b).
-- These are unified entry-wise:
instance (Unify isT a, Unify isT b) => Unify isT (a :@ b) where
  unify_ (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unify_ a₁ a₂ <*> unify_ e₁ e₂

-- Similarly, lists of terms are unified elements wise,
-- but they only match if they are of the same lenght:
instance (HasUnificationError e [a], MonadError e t, Show a, Unify t a, MonadLog t) => Unify t [a] where
  unify_ xs ys | length xs == length ys = mapM (uncurry unify_) (zip xs ys)
  unify_ xs ys = throwError (unificationError' xs ys)

instance Typeable k => FixedVars TVarOf (IsEqual (DMTypeOf k, DMTypeOf k)) where
  fixedVars _ = mempty

-- Using the unification instance, we implement solving of the `IsEqual` constraint for DMTypes.
instance Solve MonadDMTC IsEqual (DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ name (IsEqual (a,b)) = do
    res <- runExceptT $ runINCResT $ unifyᵢ_ @(INCResT DMException _) a b
    case res of
      Left (Wait')   -> return ()
      Left (Fail' e) -> throwError e
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
                                         True -> b ==! constCoeff Infty >> dischargeConstraint name
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

