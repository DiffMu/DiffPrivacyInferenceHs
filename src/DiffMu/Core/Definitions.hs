
module DiffMu.Core.Definitions where

import DiffMu.Prelude

import DiffMu.Core.Symbolic

-- import GHC.TypeLits

import           Data.Singletons.Prelude hiding (Symbol)
import           Data.Singletons.Prelude.Enum (SEnum (..))
import           Data.Singletons.Prelude.List hiding (Group)

-- import Algebra.Ring.Polynomial.Class

-- x :: Polynomial (Ratio Integer) 2
-- -- y, f, f1, f2 :: Polynomial (Ratio Integer) 2
-- x = var 0
-- g = x + x
-- test = show g

-- type Symbol = String


-- data Sensitivity = forall n. KnownNat n => Sens (Polynomial (Ratio Integer) n)

type Sensitivity = SymTerm

-- instance Show Sensitivity where
--   show (Sens s) = show s

newtype Privacy = Privacy ()

data JuliaType =
  JTAny
  deriving (Generic, Show)


data DMNum where
  DMInt :: DMNum
  DMReal :: DMNum
  deriving (Generic, Show)

-- type (:&) :: (k -> j -> *) -> (j -> *) -> k -> j -> *
-- data (:&) (f :: k -> j -> *) (x :: k -> *) a b = (:@) (f a b) (x a)
data (:&) f x = (:@) f x
  deriving (Generic, Show)

data DMType where
  VarNum :: DMNum -> DMType
  ConstNum :: DMNum -> Sensitivity -> DMType
  -- TVar :: forall t ηc τc. (KnownSymbol t, Elem t τc ~ 'True) => DMType
  TVar :: Symbol -> DMType
  (:->:) :: [DMType :& Sensitivity] -> DMType -> DMType
  deriving (Generic, Show)


data Asgmt a = (:-) Symbol a
  deriving (Generic, Show)

newtype Ctx extra = Ctx ([Asgmt (DMType :& extra)] )
  deriving (Generic, Show)

data DMTypeOp where
  Op1 :: DMTypeOp
  deriving (Generic, Show)

data Constraint =
  IsNumeric (DMType)
  | IsEqualSens Sensitivity Sensitivity
  | IsLessOrEqual Sensitivity Sensitivity
  | IsTypeOpResult [Sensitivity] (DMType) DMTypeOp
  -- a | IsEqualPriv (Privacy ηc) (Privacy ηc)
  | IsSubtypeOf (DMType) (DMType)
  | IsSupremumOf (DMType) (DMType) (DMType)
  | IsChoice (DMType) ([([JuliaType], Sensitivity , DMType)])
  deriving (Generic, Show)



type Constraints = [Constraint]

data NameCtx = NameCtx
  { names :: [Symbol]
  , currentCtr :: Int
  }
  deriving (Generic, Show)

data Full extra where
  Full ::  NameCtx -> NameCtx -> Constraints -> Ctx extra -> Full extra
  deriving (Generic, Show)

data DMException where
  UnsupportedTermE :: DMTerm -> DMException
  deriving (Generic, Show)

type TC extra = StateT (Full extra) (Except DMException)

type STC a = TC Sensitivity a
type PTC a = TC Privacy a


data Lam_ = Lam_ [Asgmt JuliaType] DMTerm
  deriving (Generic, Show)

data DMTerm =
  Ret DMTerm
  | Sng Rational DMNum
  | Var Symbol JuliaType
  | Arg Symbol JuliaType
  | Op Symbol [DMTerm]
  | Phi DMTerm DMTerm DMTerm
  | Lam Lam_
  | LamStar Lam_
  | DPhi [Lam_]
  | Apply DMTerm [DMTerm]
  | Iter DMTerm DMTerm DMTerm
  | FLet Symbol [JuliaType] Lam_ DMTerm
-- ....
  deriving (Generic, Show)


