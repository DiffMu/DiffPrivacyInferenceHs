{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Prelude
  (
    -- module Prelude
    module All
  , StringLike (..)
  , RawSource (..)
  , SourceFile (..)
  , rawSourceFromString
  , NamePriority (..)
  , CompoundPriority (..)
  , Symbol (..)
  , IxSymbol (..)
  , SymbolOf (..)
  , DictKey (..)
  , KHashable (..)
  , KShow (..)
  , KEq (..)
  , IsKind (..)
  , HasVarPriority (..)
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
  , showT
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

import Prelude ((&&),(||),div,rem,(/),(!!))
import qualified Prelude (String)
import qualified Data.Text as T
import Data.HashMap.Strict as H
import System.IO (FilePath, readFile)
import GHC.IO (catchAny)

newtype SourceFile = SourceFile (Maybe FilePath)
  deriving (Eq, Hashable, DictKey, Ord)

instance Show SourceFile where
  show (SourceFile Nothing) = "none"
  show (SourceFile (Just fp)) = fp

newtype RawSource = RawSource (HashMap SourceFile (Array Int Text))
  deriving (Show)

rawSourceFromString :: String -> [FilePath] -> IO RawSource
rawSourceFromString input other_files = do
  let make_line_array file = let ls = (T.pack <$> linesS file)
                             in  listArray (1,length ls) (ls) 
  let tryReadFile f = (Just <$> readFile f) `catchAny` (\e -> return Nothing)

  let onlyJust xs = [(SourceFile (Just a), make_line_array b) | (a, Just b) <- xs]

  other_file_contents <- mapM tryReadFile other_files
  let good_other_file_contents = onlyJust ((other_files) `zip` (other_file_contents))
  return $ RawSource $ H.fromList $
    ((SourceFile Nothing, make_line_array input)
    :
    (good_other_file_contents)
    )

-- NOTE : Order is important
data NamePriority = GeneratedNamePriority | UserNamePriority
  deriving (Eq, Ord, Generic, Show)

instance Hashable NamePriority

newtype Symbol = Symbol Text
  deriving (Eq,Ord,Hashable,Semigroup,Monoid)

newtype IxSymbol = IxSymbol (Symbol,Int,NamePriority)
  deriving (Eq,Ord,Hashable)

instance Monad t => Normalize t IxSymbol where
  normalize nt a = pure a

instance Monad t => Normalize t Symbol where
  normalize nt a = pure a

instance Monad t => Normalize t Text where
  normalize nt a = pure a

instance Monad t => Normalize t ProcVar where
  normalize nt a = pure a

-------------------------------------------------------------------------
-- Var Priority

data CompoundPriority = CompoundPriority NamePriority Int
  deriving (Show, Eq)

instance Ord CompoundPriority where
  CompoundPriority n1 i1 <= CompoundPriority n2 i2 | n1 == n2 = i1 >= i2
  CompoundPriority n1 i1 <= CompoundPriority n2 i2 | n1 > n2  = False
  CompoundPriority n1 i1 <= CompoundPriority n2 i2 | otherwise = True


type IsKind k = (SingI k, Typeable k)

class HasVarPriority v where
  varPriority :: IsKind k => v k -> CompoundPriority

instance HasVarPriority SymbolOf where
  varPriority (SymbolOf (IxSymbol (_,ix,np))) = CompoundPriority np ix

-------------------------------------------------------------------------
-- StringLike

class (IsString t, Semigroup t, Ord t) => StringLike t where
  wordsS :: t -> [t]
  linesS :: t -> [t]
  unlinesS :: [t] -> t
  intercalateS :: t -> [t] -> t
  fromStringS :: String -> t
  toStringS :: t -> String
  lengthS :: t -> Int

instance StringLike Text where
  wordsS = T.words
  linesS = T.lines
  unlinesS = T.unlines
  intercalateS = T.intercalate
  fromStringS = T.pack
  toStringS = T.unpack
  lengthS = T.length

instance StringLike String where
  wordsS = S.words
  linesS = S.lines
  unlinesS = S.unlines
  intercalateS = intercalate
  fromStringS = \a -> a
  toStringS = \a -> a
  lengthS = length

showT :: Show a => a -> Text
showT = T.pack . show


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

instance ShowLocated IxSymbol where
  showLocated a = T.pack <$> (return $ show a)

instance ShowLocated TeVar where
  showLocated = pure . showPretty

instance ShowLocated ProcVar where
  showLocated = pure . showPretty

instance ShowLocated a => ShowLocated [a] where
  showLocated as = do
    as' <- (mapM showLocated as)
    return $ "[" <> T.intercalate ", " as' <> "]"

-------------------------------------------------------------------------
-- ShowPretty

class ShowPretty a where
  showPretty :: a -> Text

instance ShowPretty () where
  showPretty _ = ""

instance ShowPretty Int where
  showPretty = T.pack . show

instance ShowPretty Text where
  showPretty s = s

class FromSymbol (v :: j -> *) where
  fromSymbol :: Symbol -> Int -> NamePriority -> v k

-- data SymbolOf (k :: j) where
  -- SymbolOf :: Symbol -> SymbolOf k

newtype SymbolOf (k :: j) = SymbolOf IxSymbol
  deriving (Eq, Hashable)

-- data SymbolOf (k :: j) where
--   SymbolOf :: Symbol -> SymbolOf k
--   -- deriving Eq via Symbol -- (Eq,Ord,Hashable)

instance FromSymbol SymbolOf where
  fromSymbol v n p = SymbolOf (IxSymbol (v, n, p))

-- instance Eq (SymbolOf (k :: j)) where
--   (SymbolOf x) == (SymbolOf y) = x == y

-- instance Hashable (SymbolOf (k :: j)) where
--   hashWithSalt salt (SymbolOf a) = hashWithSalt salt a
-- -- instance Eq (SymbolOf (k :: j)) where

class (Eq v, Hashable v) => DictKey v

-- symbols

-- WARNING: Not total
showSubscriptDigit :: Int -> Char
showSubscriptDigit a | a <= 9 = ['₀' .. '₉'] !! a
showSubscriptDigit _ = undefined

showSubscriptInt :: Int -> String
showSubscriptInt a | a <= 9 = showSubscriptDigit a : []
showSubscriptInt a          =
  let last = (a `rem` 10)
      beforeLast = (a - last) `div` 10
  in showSubscriptInt beforeLast <> (showSubscriptDigit last : [])

showWithSubscript :: Show a => (a,Int) -> String
showWithSubscript (a,0) = show a
showWithSubscript (a,n) = show a <> showSubscriptInt n

instance Show IxSymbol where
  show (IxSymbol (x,n,p)) = showWithSubscript (x,n)

instance DictKey IxSymbol

instance ShowPretty IxSymbol where
  showPretty = T.pack . show

instance Show (SymbolOf k) where
  show (SymbolOf x :: SymbolOf k) = show x --  <> " : " <> show (demote @k)

instance Show Symbol where
  show (Symbol t) = T.unpack t

instance ShowPretty Symbol where
  showPretty = T.pack . show


instance DictKey Symbol


-- proc variables

data ProcVar = UserProcVar (Symbol) | GenProcVar (IxSymbol)
  deriving (Eq,Generic, Ord)

instance Hashable ProcVar
instance Show ProcVar where
  show (UserProcVar x) = show x
  show (GenProcVar x) =  show x

instance ShowPretty ProcVar where
  showPretty (UserProcVar x) = T.pack $ show x
  showPretty (GenProcVar x) =  T.pack $ show x

instance DictKey ProcVar

-- term variables

data TeVar = UserTeVar ProcVar | GenTeVar IxSymbol (Maybe TeVar)
  deriving (Eq,Generic, Ord)

instance Hashable TeVar
instance Show TeVar where
  show (UserTeVar x) = show x
  show (GenTeVar x pv) = "gen_" <> show x
instance ShowPretty TeVar where
  showPretty (UserTeVar x) = showPretty x
  showPretty (GenTeVar x pv) = case pv of
    Just pv -> showPretty pv
    Nothing -> T.pack $ show x

instance DictKey TeVar



-- scope variables

data ScopeVar = ScopeVar IxSymbol
  deriving (Eq,Generic, Ord)

instance Hashable ScopeVar
instance Show ScopeVar where
  show (ScopeVar x) = show x
instance DictKey ScopeVar

-- memory variables

data MemVar = MemVarForProcVar ProcVar IxSymbol | StandaloneMemVar IxSymbol
  deriving (Eq,Generic, Ord)

instance Hashable MemVar
instance Show MemVar where
  show (MemVarForProcVar p x) = show p <> "#" <> show x
  show (StandaloneMemVar x) = show x

instance ShowPretty MemVar where
  showPretty = showT

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
  impossible :: Text -> t a

class Monad t => MonadInternalError t where
  internalError :: Text -> t a

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


