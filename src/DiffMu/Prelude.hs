{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Prelude
  (
    -- module Prelude
    module All
  , Symbol (..)
  , SymbolOf (..)
  , DictKey (..)
  , KHashable (..)
  , KShow (..)
  , KEq (..)
  )
  where

import DiffMu.Imports as All hiding (msum)

-- import DiffMu.Prelude.Algebra as All
-- import DiffMu.Prelude.Polynomial as All

import DiffMu.Prelude.MonadicAlgebra as All
-- import DiffMu.Prelude.MonadicPolynomial as All

import qualified Prelude (String)
import Data.Text as T
newtype Symbol = Symbol Text
  deriving (Eq,Ord,Hashable)

-- data SymbolOf (k :: j) where
  -- SymbolOf :: Symbol -> SymbolOf k

data SymbolOf (k :: j) where
  SymbolOf :: SingI k => Symbol -> SymbolOf k
  -- deriving Eq via Symbol -- (Eq,Ord,Hashable)

instance Eq (SymbolOf (k :: j)) where
  (SymbolOf x) == (SymbolOf y) = x == y

instance Hashable (SymbolOf (k :: j)) where
  hashWithSalt salt (SymbolOf a) = hashWithSalt salt a
-- instance Eq (SymbolOf (k :: j)) where


instance (Show (Demote (KindOf k)), SingKind (KindOf k)) => Show (SymbolOf k) where
  show (SymbolOf s :: SymbolOf k) = show s <> " : " <> show (demote @k)

instance Show Symbol where
  show (Symbol t) = T.unpack t

class (Eq v, Hashable v) => DictKey v
instance DictKey Symbol

-- class (forall k. Hashable (v k)) => KHashable v
-- class (forall k. Show (v k)) => KShow v
-- class (forall k. Eq (v k)) => KEq v


type KHashable :: (j -> *) -> Constraint
type KHashable v = (forall k. Hashable (v k))

type KShow :: (j -> *) -> Constraint
type KShow v = (forall k. Show (v k))

type KEq :: (j -> *) -> Constraint
type KEq v = (forall k. Eq (v k))

-- import           Prelude                                 hiding
--                                                           (Fractional (..),
--                                                           Integral (..), (*),
--                                                           (+), (-), (^), (^^))

-- import Algebra.Prelude as All hiding (Symbol)

{-
import Control.Monad.State.Lazy as All
import Control.Monad.Except as All

import Data.Semigroup as All hiding (diff, Min, Max, Any, WrapMonoid)
import Data.Monoid as All hiding (Last, First, getLast, getFirst, WrapMonoid)

import Data.Default as All

import GHC.Generics as All (Generic)

import DiffMu.Prelude.Algebra as All
import DiffMu.Prelude.Polynomial as All

import Data.List as All

import qualified Prelude

import Prelude as All (Show, IO, putStrLn, undefined, otherwise, fst, snd)



-- import DiffMu.Imports.Sensitivity as All

-- import DiffMu.Imports as All -- hiding ((+), (-), (*), (<=))

-}


