module DiffMu.Core.DelayedScope where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC

import qualified Data.HashMap.Strict as H

import Debug.Trace

-- Definition of the typechecking scope

------------------------------------------------------------------------
-- a computation that might be delayed

-- `Done` just holds the result of a finished computation, `Later` holds a computation
-- mapping an input of type x to another possibly delayed computation.
data Delayed x a = Done (a) | Later (x -> (Delayed x a))

-- throwing an error finishes a computation
throwDelayedError e = Done $ (throwError e)

-- execute a delayed computation given an input, using the input for all delay layers
-- until the end
extractDelayed :: x -> Delayed x a -> a
extractDelayed x (Done a) = a
extractDelayed x (Later f) = extractDelayed x (f x)

-- execute only one delay layer given an input
applyDelayedLayer :: x -> Delayed x a -> Delayed x a
applyDelayedLayer x (Done a) = Done a
applyDelayedLayer x (Later f) = f x

instance Functor (Delayed x) where
  fmap f (Done a) = Done (f a)
  fmap f (Later g) = Later (\x -> fmap f (g x))

instance Applicative (Delayed x) where
  pure a = Done a
  (<*>) (Done g) (Done a) = Done (g a)    -- f (a -> b) -> f a -> f b
  (<*>) (Done g) (Later g') = Later (\x -> (Done g) <*> (g' x))
  (<*>) (Later g) (Done a) = Later (\x -> (g x) <*> (Done a))
  (<*>) (Later g) (Later g') = Later (\x -> (g x) <*> (g' x))

instance Monad (Delayed x) where
  return = Done
  x >>= f = insideDelayed x f

-- bind appends the computation.
insideDelayed :: Delayed x a -> (a -> Delayed x b) -> (Delayed x b)
insideDelayed (Done a) f = (f a)
insideDelayed (Later g) f = Later (\x -> insideDelayed (g x) (\a -> applyDelayedLayer x (f a)))


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

type DMDelayed = Delayed DMScope (TC DMMain)

newtype DMScope = DMScope (H.HashMap Symbol (DMDelayed))
  deriving Generic

-- our scopes are `DictLike`
instance DictLike Symbol (DMDelayed) (DMScope) where
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
pushChoice :: Symbol -> (DMDelayed) -> DMScope -> DMScope
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
