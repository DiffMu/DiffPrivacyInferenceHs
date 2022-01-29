
module DiffMu.Abstract.Class.Unify where

import DiffMu.Prelude
import DiffMu.Abstract.Class.Term
import DiffMu.Abstract.Class.IsT
-- import DiffMu.Abstract.Class.MonadTerm



-- class Unify isT a where
--   unify_ :: (IsT isT t) => a -> a -> t a

-- unify :: (IsT isT t, Unify isT a, Normalize (t) a) => a -> a -> t a
-- unify a b = (chainM2 unify_ (normalize a) (normalize b))

class Monad t => Unify t a where
  unify_ :: a -> a -> t a

unify :: (Unify t a, Normalize (t) a) => a -> a -> t a
unify a b = (chainM2 unify_ (normalizeExact a) (normalizeExact b))


