
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


class HasUnificationError e a where
  unificationError' :: Show a => a -> a -> e


-- data INCResT m e a = Finished' (m a) | Wait' | Fail' e
--   deriving (Show, Functor)

data StoppingReason e = Wait' | Fail' e

newtype INCResT e m a = INCResT {runINCResT :: ExceptT (StoppingReason e) m a}
  -- Finished' (m a) | Wait' | Fail' e
  deriving (Functor, Applicative, Monad, MonadError (StoppingReason e))

instance HasUnificationError DMException a where
  unificationError' = UnificationError

instance HasUnificationError e a => HasUnificationError (StoppingReason e) a where
  unificationError' a b = Fail' (unificationError' a b)

-- instance HasUnificationError e a => HasUnificationError (e) [a] where
--   unificationError' a b = unificationError' a b


-- newtype INCResT m e a = INCResT {runINCResT :: Either (StoppingReason e) (m a)} 
  -- deriving (Functor, Applicative, Monad)


{-
instance Functor m => Functor (INCResT m e) where
  fmap f (Finished' a) = Finished' (fmap f a)
  -- fmap f (Partial' a) = Partial' (fmap f a)
  fmap f Wait' = Wait'
  fmap f (Fail' e) = Fail' e

instance Applicative m => Applicative (INCResT m e) where
  pure a = Finished' (pure a)
  Finished' f <*> Finished' x = Finished' (f <*> x)
  Finished' f <*> Wait' = Wait'
  Wait' <*> Finished' x = Wait'
  Wait' <*> Wait' = Wait'
  Fail' e <*> _ = Fail' e
  _ <*> Fail' e = Fail' e
  -- Finished' f <*> Partial' x = Partial' (f <*> x)
  -- Partial' f <*> Partial' x = Partial' (f <*> x)

-- instance Monad m => Monad (INCResT m e) where
--   Finished' x >>= f = (x >>=) <*> f
-}

normalizeᵢ :: Normalize t a => a -> INCResT e t a
normalizeᵢ a = liftINC (normalize a)

class Monad t => Unifyᵢ t a where
  unifyᵢ_ :: a -> a -> t a

unifyᵢ :: (Unifyᵢ (INCResT e t) a, Normalize (t) a) => a -> a -> (INCResT e t a)
unifyᵢ a b = (chainM2 unifyᵢ_ (normalizeᵢ a) (normalizeᵢ b))

liftINC :: Functor m => m a -> INCResT e m a
liftINC a = INCResT (ExceptT (fmap Right a))

-- we define the 'incremental' version of unification

instance (Monad t, HasUnificationError e JuliaType, MonadError e t) => Unifyᵢ t JuliaType where
  unifyᵢ_ (JuliaType a) (JuliaType b) | a == b = pure (JuliaType a)
  unifyᵢ_ t s = throwError (unificationError' t s)

instance MonadDMTC t => Unifyᵢ (INCResT e t) Sensitivity where
  unifyᵢ_ a b = liftINC $ unify a b

instance (Monad t, Unifyᵢ t a, Unifyᵢ t b) => Unifyᵢ t (a,b) where
  unifyᵢ_ (a1,b1) (a2,b2) = (,) <$> (unifyᵢ_ a1 a2) <*> (unifyᵢ_ b1 b2)

instance (Unifyᵢ isT a, Unifyᵢ isT b) => Unifyᵢ isT (a :@ b) where
  unifyᵢ_ (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unifyᵢ_ a₁ a₂ <*> unifyᵢ_ e₁ e₂

instance (HasUnificationError e [a], MonadError e t, Show a, Unifyᵢ t a) => Unifyᵢ t [a] where
  unifyᵢ_ xs ys | length xs == length ys = mapM (uncurry unifyᵢ_) (zip xs ys)
  unifyᵢ_ xs ys = throwError (unificationError' xs ys)

instance (HasUnificationError e (Maybe a), MonadError e t, Show a, Unifyᵢ t a) => Unifyᵢ t (Maybe a) where
  unifyᵢ_ Nothing Nothing = pure Nothing
  unifyᵢ_ (Just a) (Just b) = Just <$> unifyᵢ_ a b
  unifyᵢ_ t s = throwError (unificationError' t s)

-- instance Normalize t a => Normalize (INCResT e t) a where
--   normalize a = liftINC (normalize a)

renameVarsWithNew :: MonadDMTC t => ([SomeK TVarOf], DMTypeOf k) -> t ([SomeK TVarOf], DMTypeOf k)
renameVarsWithNew ([] , x) = return ([] , x)
renameVarsWithNew ((SomeK v:vs), x) = do
  -- call myself recursively with the rest of the list
  (ws,y) <- renameVarsWithNew (vs, x)

  -- create a name for the copy of `v`
  let vname (SymbolOf (Symbol a)) = a

  -- the copy of `v` is `w`
  w <- newTVar ("r" <> vname v)

  -- substitute the occurences of `v` with `w` in y
  let y' = substituteSingle (v := TVar w) y

  -- combine the new result with the recursively gotten one
  return ((SomeK w : ws), y')


unifyForAll :: MonadDMTC t => ([SomeK TVarOf], DMFun) -> ([SomeK TVarOf], DMFun) -> t ([SomeK TVarOf], DMFun)
unifyForAll (vx , x) (vy , y) = do
  (vx' , x') <- renameVarsWithNew (vx , x)
  (vy' , y') <- renameVarsWithNew (vy , y)

  -- all variables which we potentially still abstract over
  let vall = nub (vx' <> vy')

  -- notify the monad to open these abstracted variables (such that substitutions of them are allowed)
  openAbstractVars (Proxy @DMTypeOf) vall

  -- notify the monad that we want to track newly added substitutions
  newSubstitutionVarSet (Proxy @DMTypeOf)

  -- unify the terms with renamed variables
  z <- unify x' y'

  -- remove and get the new substitutions
  Subs σ <- removeTopmostSubstitutionVarSet @_ @DMTypeOf
  -- make them well kinded
  σ' <- mapM (\(SomeK v, SomeK a) -> SomeK <$> wellkindedSub (v :=~ a)) (H.toList σ)

  -- a substitution is good if either
  --  1. its lhs is a new var
  --  2. its rhs does not contain new vars
  --  3. its rhs is exactly a new var (this can happen if the unification chose the wrong direction for the sub)
  -- (in the other cases we have unifications of outside vars with inner vars)
  --
  -- we return a list of variables which we no longer abstract over (wrt the given substitution)
  let isGoodSub :: IsKind k => Sub TVarOf DMTypeOf k -> Either String [SomeK TVarOf]
      isGoodSub (v := a)      | SomeK v `elem` vall                      = Right [SomeK v]
      isGoodSub (v := a)      | and [w `notElem` vall | w <- freeVars a] = Right []
      isGoodSub (v := TVar a) | SomeK a `elem` vall                      = Right [SomeK a]
      isGoodSub (v := a)                                                 = Left ("While unifying foralls (" <> show (ForAll vx x) <> ") == ("
                                                                                 <> show (ForAll vy y) <> ").\n Encountered an illegal substitution " <> show (v := a))

  let isGoodSub' :: SomeK (Sub TVarOf DMTypeOf) -> Either String [SomeK TVarOf]
      isGoodSub' (SomeK s) = isGoodSub s

  let remVars = mapM isGoodSub' σ'
  case remVars of
    Left err -> throwError (UnsatisfiableConstraint err)
    Right remVars -> do
      -- the variables which we still abstract over are the ones not in remVars
      let zs = vall \\ (join remVars)

      -- notify the monad to close these abstracted variables (such that substitutions of them are again now longer allowed)
      closeAbstractVars (Proxy @DMTypeOf) zs

      -- the term is the one given by unification
      return (zs,z)

instance MonadDMTC t => Unifyᵢ (INCResT DMException t) (DMTypeOf k) where
  unifyᵢ_ Deleted a                     = liftINC $ internalError "A deleted variable reappeared and tried to escape via unification."
  unifyᵢ_ a Deleted                     = liftINC $ internalError "A deleted variable reappeared and tried to escape via unification."
  unifyᵢ_ DMReal DMReal                 = pure DMReal
  unifyᵢ_ DMInt DMInt                   = pure DMInt
  unifyᵢ_ DMData DMData                 = pure DMData
  unifyᵢ_ (Numeric t) (Numeric s)       = Numeric <$> unifyᵢ t s
  unifyᵢ_ (NonConst τ₁) (NonConst τ₂)   = NonConst <$> unifyᵢ τ₁ τ₂
  unifyᵢ_ (Const η₁ τ₁) (Const η₂ τ₂)   = Const <$> liftINC (unify η₁ η₂) <*> unifyᵢ τ₁ τ₂
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
  unifyᵢ_ (Clip k) (Clip s)             = Clip <$> unifyᵢ k s
  unifyᵢ_ (DMMat nrm1 clp1 n1 m1 τ1) (DMMat nrm2 clp2 n2 m2 τ2) =
      DMMat <$> unifyᵢ nrm1 nrm2 <*> unifyᵢ clp1 clp2 <*> unifyᵢ n1 n2 <*> unifyᵢ m1 m2 <*> unifyᵢ τ1 τ2


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
  unifyᵢ_ (ForAll xs t) (ForAll ys s)      = do
    -- NOTE: we actually have to remove all variables which were substituted
    --       from the merged list (xs <> ys). But luckily this is done
    --       automatically by the definition of substitution, and will happen
    --       when the returned type is being normalized
    --
    -- ForAll (xs <> ys) <$> unifyᵢ t s
    (zs,r) <- liftINC $ unifyForAll (xs,t) (ys,s)
    return (ForAll zs r)
  unifyᵢ_ t s                              = throwError (Fail' $ UnificationError t s)


instance Monad t => Normalize t JuliaType where
  normalize = pure


instance Monad t => Unify t () where
  unify_ _ _ = return ()


instance MonadDMTC t => Unify t JuliaType where
  unify_ (JuliaType a) (JuliaType b) | a == b = pure (JuliaType a)
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
instance (HasUnificationError e [a], MonadError e t, Show a, Unify t a) => Unify t [a] where
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


solveLessEqualSensitivity :: Sensitivity -> Sensitivity -> Maybe Bool
solveLessEqualSensitivity (SingleKinded (LinCom (MonCom as))) (SingleKinded (LinCom (MonCom bs))) = case (H.toList as, H.toList bs) of
  ([(MonCom a,av)],[(MonCom b, bv)]) -> case (H.toList a, H.toList b) of
    ([],[]) -> Just (av <= bv)
    _ -> Nothing
  _ -> Nothing

instance Solve MonadDMTC IsLessEqual (Sensitivity, Sensitivity) where
  solve_ Dict _ name (IsLessEqual (s1, s2)) = case solveLessEqualSensitivity s1 s2 of
    Just True -> dischargeConstraint name
    Just False -> failConstraint name
    Nothing -> return ()

-------------------------------------------------------------------
-- Monadic monoid structure on dmtypes
--

-- new monoid structure using infimum

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
{-
-- We define a monadic semigroup structure on `DMTypeOf k`,
-- which is simply unification.
instance (IsT MonadDMTC t) => SemigroupM (t) (DMTypeOf k) where
  (⋆) = unify

-- This is even a monadic monoid, with the neutral element given by a new type variable.
instance (SingI k, Typeable k, IsT MonadDMTC t) => MonoidM (t) (DMTypeOf k) where
  neutral = TVar <$> newTVar ""

-- An optimized check for whether a given DMType is a neutral does not create new typevariables,
-- but simply checks if the given DMType is one.
instance (SingI k, Typeable k, IsT MonadDMTC t) => (CheckNeutral (t) (DMTypeOf k)) where
  checkNeutral (TVar x) = return True
  checkNeutral (_) = return False
-}


