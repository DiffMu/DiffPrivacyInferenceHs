
module DiffMu.Core.Unification where

import DiffMu.Prelude
import DiffMu.Core.Definitions
-- import DiffMu.Core.Context
import DiffMu.Core.MonadTC
import DiffMu.Core.TC
import DiffMu.Core.Term


instance Unify MonadDMTC Sensitivity where
  unify_ = undefined

-- instance (MonadDMTC e t, Unify (TC e) a, Unify (TC e) b) => Unify (TC e) (a :& b) where
instance (Unify isT a, Unify isT b) => Unify isT (a :& b) where
  unify_ (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unify_ a₁ a₂ <*> unify_ e₁ e₂

instance (Show a, Unify MonadDMTC a) => Unify MonadDMTC [a] where
  unify_ xs ys | length xs == length ys = mapM (uncurry unify_) (zip xs ys)
  unify_ xs ys = throwError (WrongNumberOfArgs xs ys)

instance Unify MonadDMTC DMType where
  unify_ DMReal DMReal                 = pure DMReal
  unify_ DMInt DMInt                   = pure DMInt
  unify_ (Const η₁ τ₁) (Const η₂ τ₂)   = Const <$> unify_ η₁ η₂ <*> unify_ τ₁ τ₂
  unify_ (as :->: a) (bs :->: b)       = (:->:) <$> unify_ as bs <*> unify_ a b
  unify_ (TVar x) (TVar y) | x == y    = pure $ TVar x
  unify_ (TVar x) t                    = addSub (x := t) >> pure t
  unify_ t (TVar x)                    = addSub (x := t) >> pure t
  unify_ t s                           = throwError (UnificationError t s)

-- instance (MonadDMTC e t) => Unify (TC e) DMType where

instance (IsT MonadDMTC t) => SemigroupM (t e) DMType where
  (⋆) = unify

instance (IsT MonadDMTC t) => MonoidM (t e) DMType where
  neutral = TVar <$> newTVar ""

instance (IsT MonadDMTC t) => (CheckNeutral (t e) DMType) where
  checkNeutral (TVar x) = return True
  checkNeutral (_) = return False





  {-

-- class Monad t => UnificationMonad t where


-- class Unify (TC e) a where
--   unify_ :: a -> a -> TC e a

-- unify_ a b = solve (a,b)

-- instance (MonadDMTC e t) => Unify (TC e) DMNumType where
--   unify_ a b | a == b    = pure a
--   unify_ a b | otherwise = throwError (UnificationError a b)

instance (MonadDMTC e t) => Unify (t e) Sensitivity where
  unify_ = undefined

-- instance (MonadDMTC e t, Unify (TC e) a, Unify (TC e) b) => Unify (TC e) (a :& b) where
instance (MonadDMTC e t, Unify (t e) a, Unify (t e) b) => Unify (t e) (a :& b) where
  unify_ (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unify_ a₁ a₂ <*> unify_ e₁ e₂

instance (MonadDMTC e t, Show a, Unify (t e) a) => Unify (t e) [a] where
  unify_ xs ys | length xs == length ys = mapM (uncurry unify_) (zip xs ys)
  unify_ xs ys = throwError (WrongNumberOfArgs xs ys)

instance (MonadDMTC e t) => Unify (t e) DMType where
  unify_ DMReal DMReal                 = pure DMReal
  unify_ DMInt DMInt                   = pure DMInt
  unify_ (Const η₁ τ₁) (Const η₂ τ₂)   = Const <$> unify_ η₁ η₂ <*> unify_ τ₁ τ₂
  unify_ (as :->: a) (bs :->: b)       = (:->:) <$> unify_ as bs <*> unify_ a b
  unify_ (TVar x) (TVar y) | x == y    = pure $ TVar x
  unify_ (TVar x) t                    = addSub (x := t) >> pure t
  unify_ t (TVar x)                    = addSub (x := t) >> pure t
  unify_ t s                           = throwError (UnificationError t s)

-- instance (MonadDMTC e t) => Unify (TC e) DMType where

instance (MonadDMTC e t) => SemigroupM (t e) DMType where
  (⋆) = unify

instance (MonadDMTC e t) => MonoidM (t e) DMType where
  neutral = TVar <$> newTVar ""

instance (MonadDMTC e t) => (CheckNeutral (t e) DMType) where
  checkNeutral (TVar x) = return True
  checkNeutral (_) = return False

-- testabc :: DMType -> DMType -> TC e ()
-- testabc a b = solve (IsEqual (a,b))

-}

