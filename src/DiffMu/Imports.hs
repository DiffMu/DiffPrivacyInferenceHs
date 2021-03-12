
module DiffMu.Imports
  (
    module All,
    PSemigroup(..),
    PMonoid(..)
  )
where

import Control.Monad.State.Strict as All
import Control.Monad.Except as All
import Control.Monad.Writer as All hiding (getLast, getFirst, Last, First)
import Control.Monad.Identity as All
import Control.Monad as All

import Data.Semigroup as All hiding (diff, Min, Max, Any, WrapMonoid)
import Data.Monoid as All hiding (Last, First, getLast, getFirst, WrapMonoid, Monoid)


import Data.Default as All


import GHC.Generics as All (Generic)

import Data.List as All
import Data.Text as All (Text)

import qualified Prelude

import Prelude as All (Show(..), IO, putStrLn, undefined, otherwise, fst, snd, ($))
import Prelude as All ((<$>), (<*>), pure, curry, uncurry, (.))

import Prelude as All (Float(..), Rational, Int, Ordering(..), Ord(..), Eq(..))
import Prelude as All (Bool(..), String(..), Maybe(..))

import qualified Data.Semigroup as PP
import qualified Data.Monoid as PP

type PSemigroup = PP.Semigroup
type PMonoid = PP.Monoid

