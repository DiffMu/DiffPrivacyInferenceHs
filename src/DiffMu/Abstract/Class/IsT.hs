
{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Abstract.Class.IsT where

import DiffMu.Prelude

class (forall e. isT e t, forall e. Monad (t e)) => IsT (isT :: * -> (* -> * -> *) -> Constraint) (t :: * -> * -> *) | t -> isT where

type HasNormalize :: (* -> (* -> * -> *) -> Constraint) -> (* -> * -> *) -> * -> Constraint
type HasNormalize isT t a = forall t e. isT e t => Normalize (t e) a





