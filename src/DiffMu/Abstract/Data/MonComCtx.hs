
{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Abstract.Data.MonComCtx where

import DiffMu.Prelude
import DiffMu.Abstract.Data.MonadicPolynomial

import Data.HashMap.Strict as H

newtype Ctx v x = Ctx (MonCom x v)
  deriving (Generic, DictLike v x)
instance (Normalize t x) => Normalize t (Ctx v x) where
  normalize (Ctx m) = Ctx <$> normalize m

instance Functor (Ctx v) where
  fmap f (Ctx (MonCom m)) = Ctx (MonCom (H.map f m))

instance (SemigroupM m x, HasMonCom m x v) => SemigroupM m (Ctx v x) where
  (⋆) (Ctx c) (Ctx d) = Ctx <$> (c ⋆ d)

instance (Show v, Show x, DictKey v) => Show (Ctx v x) where
  show (Ctx γ) = showWith ", " (\x τ -> show x <> " : " <> show τ) γ

instance Default (Ctx v x)


class DictKey k => DictLikeM t k v d | d -> k v where
  setValueM :: k -> v -> d -> t d
  getValueM :: k -> d -> t (Maybe v)
  deleteValueM :: k -> d -> t d

instance (MonadInternalError t,
          DictLike k v1 d1, DictLike k v2 d2,
          Show k, Show v1, Show v2, Show d1, Show d2
         ) => DictLikeM t k (Either v1 v2) (Either d1 d2) where
  setValueM k (Left v) (Left d) = return $ Left (setValue k v d)
  setValueM k (Right v) (Right d) = return $ Right (setValue k v d)
  setValueM k v d = internalError $ "Trying to set " <> show k <> " := " <> show v <> " in dict " <> show d
  getValueM k (Left d) = case getValue k d of
    Just x  -> return $ Just (Left (x))
    Nothing -> return $ Nothing
  getValueM k (Right d) = case getValue k d of
    Just x  -> return $ Just (Right (x))
    Nothing -> return $ Nothing
  deleteValueM k (Left d)  = return (Left (deleteValue k d))
  deleteValueM k (Right d) = return (Right (deleteValue k d))

