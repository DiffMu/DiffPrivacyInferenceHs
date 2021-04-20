
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module DiffMu.Abstract.Class.IsT where

import DiffMu.Prelude

class (isT t, Monad t) => IsT (isT :: (* -> *) -> Constraint) (t :: * -> *) | t -> isT where

type HasNormalize :: ((* -> *) -> Constraint) -> (*) -> Constraint
type HasNormalize isT a = forall t. isT t => Normalize (t) a





