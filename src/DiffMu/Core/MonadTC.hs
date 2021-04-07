
-- {-# LANGUAGE UndecidableInstances #-}

module DiffMu.Core.MonadTC where

import DiffMu.Prelude
-- import DiffMu.Core.Definitions
import DiffMu.Core.Term

-- class (TermSubstitute x a) => MonadSubstitute x a t where

class (Monad t, Term v a) => MonadTC v a t where
  addSub :: (Typeable k) => Sub v a k -> t ()
  getSubs :: t (Subs v a)

class TCConstraint c where
  constr :: a -> c a
  runConstr :: c a -> a

  insideConstr :: (Monad t) => (a -> t a) -> c a -> t (c a)
  insideConstr f c = constr <$> f (runConstr c)


-- data Discharged = IsDischarged | NotDischarged



class TCConstraint c => Solve (isT :: * -> (* -> * -> *) -> Constraint) c a where
  solve_ :: Dict ((isT e t)) -> c a -> t e ()

-- class HasNormalize (isT :: * -> (* -> * -> *) -> Constraint) a where
--   hasNormalize :: (isT e t :- Normalize (t e) a)

-- class (Normalize t a, TCConstraint c) => Solve t c a where
--   solve_ :: c a -> t ()


-- class (Normalize t a) => Unify t a where
--   unify_ :: a -> a -> t a

class (forall e. isT e t, forall e. Monad (t e)) => IsT (isT :: * -> (* -> * -> *) -> Constraint) (t :: * -> * -> *) | t -> isT where

-- class (forall e. isT e t, forall e. Monad (t e)) => HasNormalize (isT :: * -> (* -> * -> *) -> Constraint) (t :: * -> * -> *) | t -> isT where

class Unify isT a where
  unify_ :: (IsT isT t) => a -> a -> t e a

-- class (forall t e. IsT isT t => Normalize (t e) a) => Unify isT a where
--   unify_ :: (IsT isT t, Normalize (t e) a) => a -> a -> t e a

  -- unify_ :: Dict (isT e t) -> a -> a -> t a

unify :: (IsT isT t, Unify isT a, Normalize (t e) a) => a -> a -> t e a
unify a b = (chainM2 unify_ (normalize a) (normalize b))

-- unify :: (IsT isT t, Unify isT a) => a -> a -> t e a
-- unify a b = withDict (ins @(isT e t) @(Normalize (t e) a)) (chainM2 unify_ (normalize a) (normalize b))

-- unify :: (Unify t a) => a -> a -> t a
-- unify a b = chainM2 unify_ (normalize a) (normalize b)

instance (Normalize t a, Normalize t b) => Normalize t (a,b) where
  normalize (a,b) = (,) <$> normalize a <*> normalize b

-- instance (Normalize (t e) a, ((isT :: * -> (* -> * -> *) -> Constraint) e t => Unify (t e) a)) => Solve isT IsEqual (a,a) where
-- instance ((forall e t. isT e t :=> Unify (t e) a)) => Solve isT IsEqual (a,a) where
--   solve_ (IsEqual (a,b)) = unify a b >> pure ()

-- solve :: (Solve t c a) => c a -> t ()
-- solve c = insideConstr normalize c >>= solve_


data Solvable isT where
  Solvable :: (Solve isT c a, (forall t e. isT e t :=> Normalize (t e) a), Show (c a)) => c a -> Solvable isT

-- data Solvable' isT where
--   Solvable' :: (Solve isT c a, (forall t e. IsT isT t => Normalize (t e) a)) => c a -> Solvable' isT


instance (isT e t, Monad (t e)) => Normalize (t e) (Solvable isT) where
  normalize (Solvable (c :: c a)) = withDict (ins @(isT e t) @(Normalize (t e) a)) (Solvable @isT <$> insideConstr (normalize @(t e)) c)
  -- normalize (Solvable (c :: c a)) = withDict (hasNormalize @isT @a @e @t) (Solvable @isT <$> insideConstr (normalize @(t e)) c)

instance Show (Solvable isT) where
  show (Solvable c) = show c

class (Monad t) => MonadConstraint v isT t | t -> v isT where
  addConstraint :: Solvable isT -> t v
  -- getUnsolvedConstraint :: t (v , Solvable t)


type TCConstraint' c = (forall a. Newtype (c a) a)

-- => TCConstraint c where

newtype Constr a = On a
instance TCConstraint (Constr) where
  constr = On
  runConstr (On c) = c

newtype IsTypeOpResult a = IsTypeOpResult a
  deriving (Show)
instance Newtype (IsTypeOpResult a) a
instance TCConstraint IsTypeOpResult where
  constr = IsTypeOpResult
  runConstr (IsTypeOpResult c) = c
  -- deriving (TCConstraint)

newtype IsEqual a = IsEqual a
--   deriving (TCConstraint)
instance TCConstraint IsEqual where
  constr = IsEqual
  runConstr (IsEqual c) = c

newtype IsLessEqual a = IsLessEqual a
  deriving (Show)
instance TCConstraint IsLessEqual where
  constr = IsLessEqual
  runConstr (IsLessEqual c) = c

-- class Solve t IsEqual (a,a) => Unifiable t a

-- instance Unifiable 
-- type UnifiableTerm = 
-- class Term a => UnifiableTerm a where


-- normalizeTerm :: (MonadTC a x t) => a -> t a
-- normalizeTerm a = do
--     σs <- getSubs
--     σs ↷ a


  {-

-}

