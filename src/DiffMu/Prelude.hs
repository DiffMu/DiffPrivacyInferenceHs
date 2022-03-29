{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Prelude
  (
    -- module Prelude
    module All
  , StringLike (..)
  , RawSource (..)
  , rawSourceFromString
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
  , MonadUnificationError (..)
  , ProcVar (..)
  , TeVar (..)
  , ScopeVar (..)
  , MemVar (..)
  , ShowPretty (..)
  , ShowLocated (..)
  , throwOriginalError
  , blue, green, yellow, red, magenta
  , (&&), (||)
  )
  where

import DiffMu.Imports as All hiding (msum, throwError)
import qualified DiffMu.Imports as QUAL (throwError)

-- import DiffMu.Prelude.Algebra as All
-- import DiffMu.Prelude.Polynomial as All

import DiffMu.Prelude.MonadicAlgebra as All
import DiffMu.Prelude.Data as All
import Data.List.Unicode as All
import Data.String as S
import Data.Array as All hiding (index, indices)

import Prelude ((&&),(||))
import qualified Prelude (String)
import qualified Data.Text as T


newtype RawSource = RawSource (Array Int Text)

rawSourceFromString :: String -> RawSource
rawSourceFromString input =
  let ls = T.pack <$> linesS input
  in RawSource $ listArray (1,length ls) (ls)


newtype Symbol = Symbol Text
  deriving (Eq,Ord,Hashable,Semigroup,Monoid)

instance Monad t => Normalize t Symbol where
  normalize nt a = pure a

instance Monad t => Normalize t Text where
  normalize nt a = pure a

-------------------------------------------------------------------------
-- StringLike

class (IsString t, Semigroup t) => StringLike t where
  wordsS :: t -> [t]
  linesS :: t -> [t]
  unlinesS :: [t] -> t
  intercalateS :: t -> [t] -> t

instance StringLike Text where
  wordsS = T.words
  linesS = T.lines
  unlinesS = T.unlines
  intercalateS = T.intercalate

instance StringLike String where
  wordsS = S.words
  linesS = S.lines
  unlinesS = S.unlines
  intercalateS = intercalate

-------------------------------------------------------------------------
-- ShowLocated

class ShowLocated a where
  showLocated :: MonadReader RawSource t => a -> t Text

instance ShowLocated () where
  showLocated _ = return ""

instance ShowLocated Text where
  showLocated a = return a

instance ShowLocated Symbol where
  showLocated (Symbol a) = return a

instance ShowLocated TeVar where
  showLocated = pure . T.pack . showPretty

instance ShowLocated ProcVar where
  showLocated = pure . T.pack . showPretty

instance ShowLocated a => ShowLocated [a] where
  showLocated as = do
    as' <- (mapM showLocated as)
    return $ "[" <> T.intercalate ", " as' <> "]"

-------------------------------------------------------------------------
-- ShowPretty

class ShowPretty a where
  showPretty :: a -> String

instance ShowPretty () where
  showPretty _ = ""

instance ShowPretty Text where
  showPretty s = T.unpack s

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

instance ShowPretty Symbol where
  showPretty = show

instance DictKey Symbol


-- proc variables

data ProcVar = UserProcVar Symbol | GenProcVar Symbol
  deriving (Eq,Generic, Ord)

instance Hashable ProcVar
instance Show ProcVar where
  show (UserProcVar x) = show x
  show (GenProcVar x) =  show x
instance ShowPretty ProcVar where
  showPretty (UserProcVar x) = showPretty x
  showPretty (GenProcVar x) =  showPretty x

instance DictKey ProcVar

-- term variables

data TeVar = UserTeVar ProcVar | GenTeVar Symbol (Maybe TeVar)
  deriving (Eq,Generic, Ord)

instance Hashable TeVar
instance Show TeVar where
  show (UserTeVar x) = show x
  show (GenTeVar x pv) = "gen_" <> show x
instance ShowPretty TeVar where
  showPretty (UserTeVar x) = showPretty x
  showPretty (GenTeVar x pv) = case pv of
    Just pv -> showPretty pv
    Nothing -> showPretty x

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

class Monad t => MonadUnificationError t where
  unificationError :: Show a => a -> a -> t b


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


