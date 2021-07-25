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
  , FromSymbol (..)
  , composeFun
  , composeFunM
  , MonadImpossible (..)
  , MonadInternalError (..)
  , (:=:) (..)
  , TeVar (..)
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
  deriving (Eq,Ord,Hashable,Semigroup,Monoid)

class FromSymbol (v :: j -> *) where
  fromSymbol :: Symbol -> v k

-- data SymbolOf (k :: j) where
  -- SymbolOf :: Symbol -> SymbolOf k

newtype SymbolOf (k :: j) = SymbolOf Symbol
  deriving (Eq, Hashable)

-- data SymbolOf (k :: j) where
--   SymbolOf :: Symbol -> SymbolOf k
--   -- deriving Eq via Symbol -- (Eq,Ord,Hashable)

instance FromSymbol SymbolOf where
  fromSymbol v = SymbolOf v

-- instance Eq (SymbolOf (k :: j)) where
--   (SymbolOf x) == (SymbolOf y) = x == y

-- instance Hashable (SymbolOf (k :: j)) where
--   hashWithSalt salt (SymbolOf a) = hashWithSalt salt a
-- -- instance Eq (SymbolOf (k :: j)) where

instance Show (SymbolOf k) where
  show (SymbolOf s :: SymbolOf k) = show s --  <> " : " <> show (demote @k)

instance Show Symbol where
  show (Symbol t) = T.unpack t

data TeVar = UserTeVar Symbol | GenTeVar Symbol
  deriving (Eq,Generic, Ord)

instance Hashable TeVar
instance Show TeVar where
  show (UserTeVar x) = show x
  show (GenTeVar x) = "gen_" <> show x


class (Eq v, Hashable v) => DictKey v
instance DictKey Symbol
instance DictKey TeVar

-- class (forall k. Hashable (v k)) => KHashable v
-- class (forall k. Show (v k)) => KShow v
-- class (forall k. Eq (v k)) => KEq v


type KHashable :: (j -> *) -> Constraint
type KHashable v = (forall k. Hashable (v k))

type KShow :: (j -> *) -> Constraint
type KShow v = (forall k. Show (v k))

type KEq :: (j -> *) -> Constraint
type KEq v = (forall k. Eq (v k))

composeFun :: [a -> a] -> a -> a
composeFun [] a = a
composeFun (f:fs) a = f (composeFun fs a)

composeFunM :: Monad t => [a -> t a] -> a -> t a
composeFunM [] a = return a
composeFunM (f:fs) a = do
  rs <- composeFunM fs a
  f rs

class Monad t => MonadImpossible t where
  impossible :: String -> t a

class Monad t => MonadInternalError t where
  internalError :: String -> t a

data (:=:) a b = (:=:) a b

instance (Show a, Show b) => Show (a :=: b) where
  show (a :=: b) = show a <> " :=: " <> show b


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


