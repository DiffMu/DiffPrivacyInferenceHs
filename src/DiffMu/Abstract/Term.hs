{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Abstract.Term where

import DiffMu.Prelude

import Data.HashMap.Strict as H

import Debug.Trace

data Sub x a k = (:=) (x k) (a k)
data Sub' x a k j = (:=~) (x k) (a j)

instance (KShow x, KShow a) => Show (Sub x a k) where
  show (x := a) = show x <> " := " <> show a

instance (KShow x, KShow a) => Show (Sub' x a k j) where
  show (x :=~ a) = show x <> " := " <> show a


data Changed = IsChanged | NotChanged
  deriving (Generic, Show, Eq)

instance Default Changed where
  def = NotChanged

type Watch = Writer Changed

instance Semigroup Changed where
  (<>) IsChanged a = IsChanged
  (<>) a IsChanged = IsChanged
  (<>) NotChanged NotChanged = NotChanged

instance Monoid Changed where
  mempty = NotChanged

class Monad t => MonadWatch t where
  -- startWatch :: t ()
  -- stopWatch :: t ()
  resetChanged :: t ()
  notifyChanged :: t ()
  getChanged :: t Changed

-- instance MonadWatch Watch where
--   notifyChanged = tell IsChanged

-- instance MonadWatch Identity where
--   startWatch = pure ()
--   notifyChanged = pure ()

-- class Subs x a s where
--   getTerm :: s -> x -> Maybe a

-- type SubMap x a = HashMap x a

-- instance (Eq x, Hashable x) => Subs x a (HashMap x a) where
--   getTerm s x = H.lookup x s

class Monad t => MonadImpossible t where
  impossible :: String -> t a

class (Typeable v, Typeable a, forall k. Eq (v k)) => Substitute (v :: j -> *) (a :: j -> *) x where
  substitute :: (Monad t) => (forall k. (Typeable k) => v k -> t (a k)) -> (x -> t x)





-- class (Hashable (Var a), Show (Var a), Show a, Substitute (Var a) a a) => Term a where
--   type Var a :: *
--   -- substituteAll :: Monad t => (Var a -> t a) -> a -> t a
--   var :: Var a -> a

-- class (KHashable v, KShow v, KShow a, KEq v, forall k. Substitute v a (a k)) => Term v a where
-- class (KHashable v, KShow v, KShow a, KEq v, forall k. SingI k => Substitute v a (a k)) => Term v a where
class (KHashable v, KShow v, KShow a, KEq v, forall k. (Substitute v a (a k))) => Term v a where
  var :: Typeable k => v k -> a k

data SomeK (v :: j -> *) where
  SomeK :: (Typeable v, Typeable k) => v k -> SomeK v
-- deriving instance Generic (SomeK v)


instance (KHashable v) => Hashable (SomeK v) where
  hashWithSalt salt (SomeK x) = hashWithSalt salt x

instance (KShow v) => Show (SomeK (v :: j -> *)) where
  show (SomeK (x :: v k)) = show x <> show (someTypeRep x)
    -- let pP = someTypeRep x
    -- in _





instance KEq v => Eq (SomeK v) where
  SomeK (a) == SomeK (b) = case testEquality (typeOf a) (typeOf b) of
    Nothing -> False
    Just Refl -> a == b


data Subs v a where
  -- Subs :: Term v a => (HashMap (SomeK v) (SomeK a)) -> Subs v a
  Subs :: Term v a => (HashMap (SomeK v) (SomeK a)) -> Subs v a


instance Term v a => Default (Subs v a) where
  def = Subs empty

singletonSub :: (Term x a, Typeable k) => Sub x a k -> Subs x a
singletonSub ((x :: x k) := a) = Subs (singleton (SomeK @_ @k x) (SomeK a))


instance Show (Subs v a) where
  show (Subs s) = intercalate ", " ((\(SomeK x, SomeK a) -> show (x :=~ a)) <$> toList s)


-- class Substitute (Var a) a x => VSubstitute a x where
-- instance Substitute (Var a) a x => VSubstitute a x where



trySubstitute :: (MonadImpossible t, MonadWatch t, Term v a, Typeable k) => Subs v a -> v k -> t (a k)
trySubstitute (Subs m) (x :: v k) = case H.lookup (SomeK x) m of
  Just (SomeK (a :: a k2))  -> do
    case testEquality (typeRep @k) (typeRep @k2) of
      Nothing -> impossible $ "Encountered a wrongly kinded substitution: " <> show (typeRep @k) <> " ≠ " <> show (typeRep @k2)
      Just Refl -> notifyChanged >> pure a

  Nothing -> pure (var x)

-- trySubstitute :: (MonadImpossible t, MonadWatch t, Term v a, Typeable k) => Subs v a -> v k -> t (a k)

substituteSingle :: (Typeable k, Term v a) => Sub v a k -> a k -> a k
substituteSingle ((x :: v k) := (a :: a k)) b = runIdentity (substitute f b)
  where f :: (forall k. (Typeable k) => v k -> Identity (a k))
        f (v :: v k2) = case testEquality (typeRep @k) (typeRep @k2) of
          Nothing -> pure (var v)
          Just Refl -> g v
            where g v | v == x    = pure a
                  g v | otherwise = pure (var v)




wellkindedSub :: (Typeable k, Typeable j, Term v a, MonadImpossible t) => Sub' v a k j -> t (Sub v a k)
wellkindedSub ((x :: v k) :=~ (a :: a j)) =
    case testEquality (typeRep @k) (typeRep @j) of
      Nothing -> impossible $ "Encountered a wrongly kinded substitution: " <> show (typeRep @k) <> " ≠ " <> show (typeRep @j)
      Just Refl -> return (x := a)


substituteSingle' :: (Typeable k, Term v a) => Sub v a k -> SomeK a -> SomeK a
substituteSingle' ((x :: v k) := (a :: a k)) (SomeK (a0 :: a j)) =
    case testEquality (typeRep @k) (typeRep @j) of
      Nothing -> (SomeK a0)
      Just Refl -> SomeK (substituteSingle (x := a) a0)


--       Nothing -> impossible $ "Encountered a wrongly kinded substitution: " <> show (typeRep @j) <> " ≠ " <> show (typeRep @j0)
--       Just Refl -> notifyChanged >> pure a
-- substituteSingle' (x := a) b = runIdentity (substitute f b)
--   where f v | v == x    = pure a
--         f v | otherwise = pure (var v)
  -- undefined -- runIdentity . substitute (trySubstitute (Subs (H.singleton x a)))


instance (MonadImpossible t, Term v a) => SemigroupM t (Subs v a) where
  (⋆) (Subs m) (Subs n) = Subs <$> H.foldlWithKey f (pure m) n
    where f mm (SomeK x) (SomeK a) = do
            mm' <- mm
            case H.lookup (SomeK x) mm' of
              Just (SomeK a') -> impossible $ "Tried to extend a set of substitutions which already contains " <> show (x :=~ a') <> " with a new substitution of the same variable, " <> show (x :=~ a) <> "."
              Nothing -> do σ <- wellkindedSub (x :=~ a)
                            let mm1 = H.map (substituteSingle' σ) mm'
                            return (H.insert (SomeK x) (SomeK a) mm1)


instance (MonadImpossible t, Term v a) => MonoidM t (Subs v a) where
  neutral = pure (Subs H.empty)

instance (MonadImpossible t, MonadWatch t, Term v a, Substitute v a x) => ModuleM t (Subs v a) x where
  (↷) σs a = substitute (trySubstitute σs) a





