
module DiffMu.Core.Term where

import DiffMu.Prelude

import Data.HashMap.Strict as H

data Sub x a = (:=) x a
  deriving (Show)


data Changed = IsChanged | NotChanged
  deriving (Generic, Show)

type Watch = Writer Changed

instance Semigroup Changed where
  (<>) IsChanged a = IsChanged
  (<>) a IsChanged = IsChanged
  (<>) NotChanged NotChanged = NotChanged

instance Monoid Changed where
  mempty = NotChanged

class Monad t => MonadWatch t where
  notifyChanged :: t ()

instance MonadWatch Watch where
  notifyChanged = tell IsChanged

instance MonadWatch Identity where
  notifyChanged = pure ()

-- class Subs x a s where
--   getTerm :: s -> x -> Maybe a

-- type SubMap x a = HashMap x a

-- instance (Eq x, Hashable x) => Subs x a (HashMap x a) where
--   getTerm s x = H.lookup x s

class Monad t => MonadImpossible t where
  impossible :: String -> t a

class Eq v => Substitute v a x where
  substitute :: Monad t => (v -> t a) -> x -> t x

-- class (Hashable (Var a), Show (Var a), Show a, Substitute (Var a) a a) => Term a where
--   type Var a :: *
--   -- substituteAll :: Monad t => (Var a -> t a) -> a -> t a
--   var :: Var a -> a

class (Hashable v, Show v, Show a, Substitute v a a) => Term v a where
  var :: v -> a

data Subs v a where
  Subs :: Term v a => (HashMap v a) -> Subs v a

instance Term v a => Default (Subs v a) where
  def = Subs empty
instance Show (Subs v a) where
  show (Subs s) = "some subs"
-- class Substitute (Var a) a x => VSubstitute a x where
-- instance Substitute (Var a) a x => VSubstitute a x where


trySubstitute :: (MonadWatch t, Term v a) => Subs v a -> v -> t a
trySubstitute (Subs m) x = case H.lookup x m of
  Just a  -> notifyChanged >> pure a
  Nothing -> pure (var x)

substituteSingle :: Term v a => Sub v a -> a -> a
substituteSingle (x := a) b = runIdentity (substitute f b)
  where f v | v == x    = pure a
        f v | otherwise = pure (var v)
  -- undefined -- runIdentity . substitute (trySubstitute (Subs (H.singleton x a)))

instance (MonadImpossible t, Term v a) => SemigroupM t (Subs v a) where
  (⋆) (Subs m) (Subs n) = Subs <$> H.foldlWithKey f (pure m) n
    where f mm x a = do
            mm' <- mm
            case H.lookup x mm' of
              Just a' -> impossible $ "Tried to extend a set of substitutions which already contains " <> show (x := a') <> " with a new substitution of the same variable, " <> show (x := a) <> "."
              Nothing -> let mm1 = H.map (substituteSingle (x := a)) mm'
                         in return (H.insert x a mm1)

instance (MonadImpossible t, Term v a) => MonoidM t (Subs v a) where
  neutral = pure (Subs H.empty)

instance (MonadImpossible t, MonadWatch t, Term v a, Substitute v a x) => ModuleM t (Subs v a) x where
  (↷) σs a = substitute (trySubstitute σs) a



