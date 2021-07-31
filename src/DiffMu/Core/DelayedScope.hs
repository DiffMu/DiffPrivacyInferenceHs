
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Core.DelayedScope where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC

import qualified Data.HashMap.Strict as H

import Debug.Trace

------------------------------------------------------------------------
-- a computation that might be delayed

-- We define a monad transformer DelayedT which adds the ability to delay
-- computations until more input is given.
-- I.e., basically, a value of type `Delayed x a` is either already existant: `Done a`
-- or it needs further input of type `x` (possibly multiple times).
-- Combinining two values of type `Delayed x a` (using `<*>` or `bind`/`join`) creates
-- a value which waits for the maximum needed input between those two, i.e. the same input
-- is distributed over all "monadic components".


-- We define this as monad transformer, it seems that the definition needs
-- to be mutually recursive.
-- `Done` just holds the result of a finished computation, `Later` holds a computation
-- mapping an input of type x to another possibly delayed computation.
data DelayedT_ x m a = Done a | Later (x -> (DelayedT x m a))
newtype DelayedT x m a = DelayedT (m (DelayedT_ x m a))


-- we expose the original constructors as shortcuts
done :: Monad m => a -> DelayedT x m a
done = return

later :: Monad m => (x -> DelayedT x m a) -> DelayedT x m a
later f = DelayedT (pure (Later f))


-- Delayed is a Functor
instance Monad m => Functor (DelayedT x m) where
  fmap f (DelayedT ma) = DelayedT $ do
    a <- ma
    case a of
      Done a -> return $ Done (f a)
      Later g -> return $ Later $ \x -> fmap f (g x)

-- Delayed is Applicative
instance Monad m => Applicative (DelayedT x m) where
  pure = return
  mf <*> ma = do
    f <- mf
    a <- ma
    return (f a)

-- Delayed is a Monad
instance Monad m => Monad (DelayedT x m) where
  return a = DelayedT (return (Done a))
  x >>= f = insideDelayed x f

-- `DelayedT m` is a MonadState if `m` is
instance MonadState s m => MonadState s (DelayedT x m) where
  state (f :: (s -> (a,s))) = let x :: m a = state f
                              in DelayedT $ do
                                    x' <- x
                                    return (Done x')


-- the actual implementation of `bind` for DelayedT
insideDelayed :: Monad m => DelayedT x m a -> (a -> (DelayedT x m b)) -> (DelayedT x m b)
insideDelayed (DelayedT ma) f = DelayedT $ do
  a <- ma
  case a of
    Done a -> let (DelayedT mx) = f a in mx
    Later g -> return $ Later (\x -> insideDelayed (g x) (\a -> applyDelayedLayer x (f a)))

-- applying one layer of input
applyDelayedLayer :: Monad m => x -> DelayedT x m a -> DelayedT x m a
applyDelayedLayer x (DelayedT ma) = DelayedT $ do
  a <- ma
  case a of
    Done a -> return (Done a)
    Later g -> let (DelayedT mx) = g x in mx

-- applying the same input value to all layers,
-- in order to retrieve the value inside
extractDelayed :: Monad m => x -> DelayedT x m a -> m a
extractDelayed x (DelayedT ma) = do
  a <- ma
  case a of
    Done a -> return a
    Later g -> extractDelayed x (g x)

applyAllDelayedLayers :: Monad m => x -> DelayedT x m a -> DelayedT x m a
applyAllDelayedLayers x d = DelayedT $ do
  res <- extractDelayed x d
  return (Done $ res)

-- throwing an error finishes a computation
throwDelayedError e = DelayedT (pure $ Done $ (throwError e))


------------------------------------------------------------------------
-- the additional state monad during the typechecking process

-- We need to create unique term variable names during the process of
-- typechecking, outside of the TC monad.
-- For this we use a state monad with the following state type, and
-- wrapped around it is the DelayedT transformer.

data DelayedState = DelayedState
  {
    _termVars :: NameCtx
  }

$(makeLenses ''DelayedState)

instance Default DelayedState where
  def = DelayedState def


-- in order to create a unique term variable, call this function.
newTeVar :: (MonadState DelayedState m) => Text -> m (TeVar)
newTeVar hint = termVars %%= (first GenTeVar . (newName hint))



------------------------------------------------------------------------
-- the scope used by the typechecker

-- julia resolves the variables within a functoin upon function application, not upon
-- function definition. we hence have to delay the checking of a function-valued variable
-- until said function is applied, and then check it in the scope that is current at
-- application time. a scope for our typechecker hence maps variable names to delayed computation
-- of their type. to be precise, non-function variables have their type wrapped in a `Done`.
-- function variables have a map takes a DMScope and computes another delayed computation,
-- wrapping the type of the function wrt to the input scope. note that that can be a `Later`
-- too in case the function returns another function


-- the type of our typechecking is `TC DMMain`, inside of a `DelayedT` & `State` monad
type DMDelayed = DelayedT DMScope (State DelayedState) (TC DMMain)

newtype DMScope = DMScope (H.HashMap TeVar (DMDelayed))
  deriving Generic

-- our scopes are `DictLike`
instance DictLike TeVar (DMDelayed) (DMScope) where
  setValue v m (DMScope h) = DMScope (H.insert v m h)
  deleteValue v (DMScope h) = DMScope (H.delete v h)
  getValue k (DMScope h) = h H.!? k
  emptyDict = DMScope H.empty
  isEmptyDict (DMScope h) = H.null h
  getAllKeys (DMScope h) = H.keys h

instance Default (DMScope) where
  def = DMScope H.empty


-- pushing choices (multiple dispatch function variables) is different from pushing
-- normal variables because if another method of the same function was defined
-- earlier, their types have to be collected in one type using the `:∧:` operator
pushChoice :: TeVar -> (DMDelayed) -> DMScope -> DMScope
pushChoice name ma scope =
  let oldval = getValue name scope
      newval = case oldval of
        Nothing -> ma
        Just mb -> do
          a <- ma
          b <- mb
          return $ do
            a' <- a
            b' <- b
            return (a' :∧: b')
  in setValue name newval scope

