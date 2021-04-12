
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

