
module DiffMu.Prelude
  (
    -- module Prelude
    module All
  , Symbol (..)
  , DictKey (..)
  )
  where

import DiffMu.Imports as All

-- import DiffMu.Prelude.Algebra as All
-- import DiffMu.Prelude.Polynomial as All

import DiffMu.Prelude.MonadicAlgebra as All
-- import DiffMu.Prelude.MonadicPolynomial as All

import qualified Prelude (String)
import Data.Text as T
newtype Symbol = Symbol Text
  deriving (Eq,Ord,Hashable)

instance Show Symbol where
  show (Symbol t) = T.unpack t

class (Eq v, Hashable v) => DictKey v
instance DictKey Symbol


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


