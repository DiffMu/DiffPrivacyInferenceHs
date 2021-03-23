
module DiffMu.Core.Unification where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.MonadTC
import DiffMu.Core.TC
import DiffMu.Core.Term


-- class Monad t => UnificationMonad t where


-- class Unify (TC e) a where
--   unify_ :: a -> a -> TC e a

-- unify_ a b = solve (a,b)

-- instance Unify (TC e) DMNumType where
--   unify_ a b | a == b    = pure a
--   unify_ a b | otherwise = throwError (UnificationError a b)

instance Unify (TC e) Sensitivity where
  unify_ = undefined

instance (Unify (TC e) a, Unify (TC e) b) => Unify (TC e) (a :& b) where
  unify_ (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unify_ a₁ a₂ <*> unify_ e₁ e₂

instance (Show a, Unify (TC e) a) => Unify (TC e) [a] where
  unify_ xs ys | length xs == length ys = mapM (uncurry unify_) (zip xs ys)
  unify_ xs ys = throwError (WrongNumberOfArgs xs ys)

instance Unify (TC e) DMType where
  unify_ DMReal DMReal                 = pure DMReal
  unify_ DMInt DMInt                   = pure DMInt
  unify_ (Const η₁ τ₁) (Const η₂ τ₂)   = Const <$> unify_ η₁ η₂ <*> unify_ τ₁ τ₂
  unify_ (as :->: a) (bs :->: b)       = (:->:) <$> unify_ as bs <*> unify_ a b
  unify_ (TVar x) (TVar y) | x == y    = pure $ TVar x
  unify_ (TVar x) t                    = addSub (x := t) >> pure t
  unify_ t (TVar x)                    = addSub (x := t) >> pure t
  unify_ t s                           = throwError (UnificationError t s)

-- instance Unify (TC e) DMType where

instance SemigroupM (TC e) DMType where
  (⋆) = unify


testabc :: DMType -> DMType -> TC e ()
testabc a b = solve (IsEqual (a,b))


