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
  , ProcVar (..)
  , TeVar (..)
  , ScopeVar (..)
  , MemVar (..)
  , throwOriginalError
  , blue, green, yellow, red, magenta
  )
  where

import DiffMu.Imports as All hiding (msum, throwError)
import qualified DiffMu.Imports as QUAL (throwError)

-- import DiffMu.Prelude.Algebra as All
-- import DiffMu.Prelude.Polynomial as All

import DiffMu.Prelude.MonadicAlgebra as All
import DiffMu.Prelude.Data as All

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

class (Eq v, Hashable v) => DictKey v

-- symbols

instance Show (SymbolOf k) where
  show (SymbolOf s :: SymbolOf k) = show s --  <> " : " <> show (demote @k)

instance Show Symbol where
  show (Symbol t) = T.unpack t

instance DictKey Symbol


-- proc variables

data ProcVar = UserProcVar Symbol
  deriving (Eq,Generic, Ord)

instance Hashable ProcVar
instance Show ProcVar where
  show (UserProcVar x) = show x

instance DictKey ProcVar

-- term variables

data TeVar = UserTeVar ProcVar | GenTeVar Symbol
  deriving (Eq,Generic, Ord)

instance Hashable TeVar
instance Show TeVar where
  show (UserTeVar x) = show x
  show (GenTeVar x) = "gen_" <> show x

instance DictKey TeVar



-- scope variables

data ScopeVar = ScopeVar Symbol
  deriving (Eq,Generic, Ord)

instance Hashable ScopeVar
instance Show ScopeVar where
  show (ScopeVar x) = show x
instance DictKey ScopeVar

-- memory variables

data MemVar = MemVarForProcVar ProcVar Symbol | StandaloneMemVar Symbol
  deriving (Eq,Generic, Ord)

instance Hashable MemVar
instance Show MemVar where
  show (MemVarForProcVar p x) = show p <> "#" <> show x
  show (StandaloneMemVar x) = show x

instance DictKey MemVar


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


throwOriginalError :: (MonadError e m) => e -> m a
throwOriginalError = QUAL.throwError

blue x = "\27[34m" <> x <> "\27[0m"
green x = "\27[32m" <> x <> "\27[0m"
yellow x = "\27[33m" <> x <> "\27[0m"
red x = "\27[31m" <> x <> "\27[0m"
magenta x = "\27[35m" <> x <> "\27[0m"




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


