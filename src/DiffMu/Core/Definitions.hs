
module DiffMu.Core.Definitions where

import DiffMu.Prelude

import DiffMu.Core.Symbolic
import DiffMu.Core.Term
import DiffMu.Core.MonadicPolynomial
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
  JTAny | JTInt | JTReal
  deriving (Generic, Show)


-- data DMNumType where
--   DMInt :: DMNumType
--   DMReal :: DMNumType
--   deriving (Generic, Show, Eq)

-- type (:&) :: (k -> j -> *) -> (j -> *) -> k -> j -> *
-- data (:&) (f :: k -> j -> *) (x :: k -> *) a b = (:@) (f a b) (x a)
infix 3 :@
data (:&) f x = (:@) f x
  deriving (Generic, Show)

data DMType where
  -- Num :: DMNumType -> DMType
  DMInt :: DMType
  DMReal :: DMType
  Const :: Sensitivity -> DMType -> DMType
  -- TVar :: forall t ηc τc. (KnownSymbol t, Elem t τc ~ 'True) => DMType
  TVar :: Symbol -> DMType
  (:->:) :: [DMType :& Sensitivity] -> DMType -> DMType
  deriving (Generic, Show)


data Asgmt a = (:-) Symbol a
  deriving (Generic, Show)

-- newtype Ctx extra = Ctx ([Asgmt (DMType :& extra)] )
newtype Ctx extra = Ctx (LinCom (DMType :& extra) Symbol)
-- ([Asgmt (DMType :& extra)] )
  deriving (Generic, Show)
instance Default (Ctx e)

data DMTypeOp where
  Op1 :: DMTypeOp
  deriving (Generic, Show)

data ConstraintOld = ConstraintOld
  -- IsNumeric (DMType)
  -- | IsEqualSens Sensitivity Sensitivity
  -- | IsEqual DMType DMType
  -- | Substitute Symbol DMType
  -- | IsLessOrEqual Sensitivity Sensitivity
  -- | IsTypeOpResult [Sensitivity] (DMType) DMTypeOp
  -- -- a | IsEqualPriv (Privacy ηc) (Privacy ηc)
  -- | IsSubtypeOf (DMType) (DMType)
  -- | IsSupremumOf (DMType) (DMType) (DMType)
  -- | IsChoice (DMType) ([([JuliaType], Sensitivity , DMType)])
  deriving (Generic, Show)


type ConstraintOlds = [Watch ConstraintOld]

data NameCtx = NameCtx
  { names :: [Symbol]
  , currentCtr :: Int
  }
  deriving (Generic, Show)
instance Default NameCtx

newName :: Symbol -> NameCtx -> (Symbol, NameCtx)
newName hint (NameCtx names ctr) =
  let name = hint <> "_" <> show ctr
  in (name , NameCtx (name : names) (ctr +! 1))

data DMException where
  UnsupportedTermError :: DMTerm -> DMException
  UnificationError :: Show a => a -> a -> DMException
  WrongNumberOfArgs :: Show a => a -> a -> DMException
  ImpossibleError :: String -> DMException
  -- deriving (Generic, Show)

instance Show DMException where
  show (UnsupportedTermError t) = "The term '" <> show t <> "' is currently not supported."
  show (UnificationError a b) = "Could not unify '" <> show a <> "' with '" <> show b <> "'."
  show (WrongNumberOfArgs a b) = "While unifying: the terms '" <> show a <> "' and '" <> show b <> "' have different numbers of arguments"
  show (ImpossibleError e) = "Something impossible happened: " <> show e




data Lam_ = Lam_ [Asgmt JuliaType] DMTerm
  deriving (Generic, Show)

data DMTerm =
  Ret DMTerm
  | Sng Float JuliaType
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


