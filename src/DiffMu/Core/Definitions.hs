
module DiffMu.Core.Definitions where

import DiffMu.Prelude

import DiffMu.Core.Symbolic
import DiffMu.Core.Term
import DiffMu.Core.MonadicPolynomial2
-- import GHC.TypeLits

import           Data.Singletons.Prelude hiding (Symbol)
import           Data.Singletons.Prelude.Enum (SEnum (..))
import           Data.Singletons.Prelude.List hiding (Group)

import qualified Data.Text as T

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
  deriving (Generic)

instance (Show a, Show b) => Show (a :& b) where
  show (a :@ b) = show a <> " @ " <> show b

data DMType where
  -- Num :: DMNumType -> DMType
  DMInt :: DMType
  DMReal :: DMType
  Const :: Sensitivity -> DMType -> DMType
  -- TVar :: forall t ηc τc. (KnownSymbol t, Elem t τc ~ 'True) => DMType
  TVar :: Symbol -> DMType
  (:->:) :: [DMType :& Sensitivity] -> DMType -> DMType
  deriving (Generic, Show)

-- instance Show DMType where
--   show (TVar x) = x
--   show (DMInt)


data Asgmt a = (:-) Symbol a
  deriving (Generic, Show)


newtype Ctx v x = Ctx (MonCom x v)
  deriving (Generic, DictLike v x)

instance (Show v, Show x, DictKey v) => Show (Ctx v x) where
  show (Ctx γ) = showWith ", " (\x τ -> x <> " : " <> τ) γ

instance Default (Ctx v x)
type TypeCtx extra = Ctx Symbol (DMType :& extra)

-- newtype TypeCtx extra = TypeCtx ([Asgmt (DMType :& extra)] )
-- newtype TypeCtx extra = TypeCtx (MonCom (DMType :& extra) Symbol)
-- ([Asgmt (DMType :& extra)] )
  -- deriving (Generic, Show, DictLike Symbol (DMType :& extra))
-- instance Default (TypeCtx e)

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
  deriving (Generic)
instance Default NameCtx
instance Show NameCtx where
  show (NameCtx names _) = "[" <> intercalate ", " (show <$> names) <> "]"

newName :: Text -> NameCtx -> (Symbol, NameCtx)
newName (hint) (NameCtx names ctr) =
  let name = Symbol (hint <> "_" <> T.pack (show ctr))
  in (name , NameCtx (name : names) (ctr +! 1))

data DMException where
  UnsupportedTermError :: DMTerm -> DMException
  UnificationError :: Show a => a -> a -> DMException
  WrongNumberOfArgs :: Show a => a -> a -> DMException
  ImpossibleError :: String -> DMException
  VariableNotInScope :: Show a => a -> DMException
  -- deriving (Generic, Show)

instance Show DMException where
  show (UnsupportedTermError t) = "The term '" <> show t <> "' is currently not supported."
  show (UnificationError a b) = "Could not unify '" <> show a <> "' with '" <> show b <> "'."
  show (WrongNumberOfArgs a b) = "While unifying: the terms '" <> show a <> "' and '" <> show b <> "' have different numbers of arguments"
  show (ImpossibleError e) = "Something impossible happened: " <> show e
  show (VariableNotInScope v) = "Variable not in scope: " <> show v




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


