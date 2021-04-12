
module DiffMu.Abstract.Class.Unify where

import DiffMu.Prelude
import DiffMu.Abstract.Class.Term
import DiffMu.Abstract.Class.IsT
-- import DiffMu.Abstract.Class.MonadTerm



class Unify isT a where
  unify_ :: (IsT isT t) => a -> a -> t e a

unify :: (IsT isT t, Unify isT a, Normalize (t e) a) => a -> a -> t e a
unify a b = (chainM2 unify_ (normalize a) (normalize b))


