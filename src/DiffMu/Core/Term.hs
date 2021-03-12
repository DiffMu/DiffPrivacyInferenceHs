
module DiffMu.Core.Term where

import DiffMu.Prelude

import Data.HashMap.Strict as H
import Data.Hashable

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

class (Eq (Var a), Hashable (Var a), Show (Var a), Show a) => Term a where
  type Var a :: *
  substituteAll :: Monad t => (Var a -> t a) -> a -> t a
  var :: Var a -> a

data Subs a where
  Subs :: Term a => (HashMap (Var a) a) -> Subs a



trySubstitute :: (MonadWatch t, Term a) => Subs a -> (Var a) -> t a
trySubstitute (Subs m) x = case H.lookup x m of
  Just a  -> notifyChanged >> pure a
  Nothing -> pure (var x)


substitute :: Term a => Sub (Var a) a -> a -> a
substitute (x := a) = runIdentity . substituteAll (trySubstitute (Subs (H.singleton x a)))

instance (MonadImpossible t, Term a) => SemigroupM t (Subs a) where
  (⋆) (Subs m) (Subs n) = Subs <$> H.foldlWithKey f (pure m) n
    where f mm x a = do
            mm' <- mm
            case H.lookup x mm' of
              Just a' -> impossible $ "Tried to extend a set of substitutions which already contains " <> show (x := a') <> " with a new substitution of the same variable, " <> show (x := a) <> "."
              Nothing -> let mm1 = H.map (substitute (x := a)) mm'
                         in return (H.insert x a mm1)

instance (MonadImpossible t, Term a) => MonoidM t (Subs a) where
  neutral = pure (Subs H.empty)

instance (MonadImpossible t, Term a) => ModuleM t (Subs a) a where
  (↷) σs a = undefined



