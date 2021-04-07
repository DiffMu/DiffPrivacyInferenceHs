
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Core.Definitions where

import DiffMu.Prelude

import DiffMu.Core.Symbolic
import DiffMu.Core.Term
import DiffMu.Core.MonadTC
import DiffMu.Core.MonadicPolynomial2
-- import GHC.TypeLits

import Data.Singletons.TH

import           Data.Singletons.Prelude hiding (Symbol)
import           Data.Singletons.Prelude.Enum (SEnum (..))
import           Data.Singletons.Prelude.List hiding (Group)

import qualified Data.Text as T
import Data.HashMap.Strict as H

-- import Algebra.Ring.Polynomial.Class

-- x :: Polynomial (Ratio Integer) 2
-- -- y, f, f1, f2 :: Polynomial (Ratio Integer) 2
-- x = var 0
-- g = x + x
-- test = show g

-- type Symbol = String

type SVar = Symbol
type SensitivityOf = SymTerm
type Sensitivity = SymTerm MainSensKind
newtype Privacy = Privacy ()


-- data Sensitivity = forall n. KnownNat n => Sens (Polynomial (Ratio Integer) n)


data JuliaType =
  JTAny | JTInt | JTReal
  deriving (Generic, Show)

type TVar = Symbol
type TVarOf = SymbolOf @DMKind
type SVarOf = SymbolOf @SensKind



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

data DMKind = MainKind | NumericKind
  deriving (Typeable)

instance Show DMKind where
  show MainKind = "*"
  show NumericKind = "Num"

genSingletons [''DMKind]

type DMType = DMTypeOf MainKind
data DMTypeOf (k :: DMKind) where
  -- Num :: DMNumType -> DMType
  DMInt :: DMTypeOf NumericKind
  DMReal :: DMTypeOf NumericKind

  Const    :: Sensitivity -> DMTypeOf NumericKind -> DMType
  NonConst :: DMTypeOf NumericKind -> DMType
  -- TVar :: forall t ηc τc. (KnownSymbol t, Elem t τc ~ 'True) => DMType
  TVar :: Typeable k => SymbolOf k -> DMTypeOf k
  (:->:) :: [DMType :& Sensitivity] -> DMType -> DMType
  -- deriving (Show)

instance Show (DMTypeOf k) where
  show _ = "some type"


--------------------------------------------------------------------------
-- Type Operations
-- It is often the case that we cannot say what type a simple operation
-- such as `a + b` will have, since this depends on the types of `a` and `b`,
-- which apriori seldom are going to be known.
-- Thus we introduce 'type operations' encoding these unknown types,
-- If `a : A` and `b : B`, then `a + b : Binary(DMOpAdd(), A, B)`.
-- Further along while typechecking, we will compute the actual value of that type.

-- The type of all possible unary type operations.
data DMTypeOps_Unary =
   DMOpCeil
   | DMOpGauss

-- The type of all possible binary type operations.
data DMTypeOps_Binary =
   DMOpAdd
   | DMOpSub
   | DMOpMul
   | DMOpDiv
   | DMOpMod
   | DMOpEq

-- The type of all possible ternary type operations.
data DMTypeOps_Ternary =
   DMOpLoop

data DMTypeOp_Some = IsUnary DMTypeOps_Unary | IsBinary DMTypeOps_Binary | IsTernary DMTypeOps_Ternary
  deriving (Show, Generic)

instance Show DMTypeOps_Unary where
  show DMOpCeil = "ceil"
  show DMOpGauss = "gauss"

instance Show DMTypeOps_Binary where
  show DMOpAdd = "+"
  show DMOpSub = "-"
  show DMOpMul = "*"
  show DMOpDiv = "/"
  show DMOpMod = "%"
  show DMOpEq = "=="

instance Show DMTypeOps_Ternary where
  show DMOpLoop = "loop"

-- An application of a type operation to an appropriate number of type arguments
data DMTypeOp =
   Unary DMTypeOps_Unary (DMType :& SVar) DMType
   | Binary DMTypeOps_Binary (DMType :& SVar , DMType :& SVar) DMType
   | Ternary DMTypeOps_Ternary (DMType :& SVar , DMType :& SVar , DMType :& SVar) DMType
  deriving (Show)


--------------------------------------------------------------------------
-- Other ...

data Asgmt a = (:-) Symbol a
  deriving (Generic, Show)


newtype Ctx v x = Ctx (MonCom x v)
  deriving (Generic, DictLike v x)
instance (Normalize t x) => Normalize t (Ctx v x) where
  normalize (Ctx m) = Ctx <$> normalize m

instance Functor (Ctx v) where
  fmap f (Ctx (MonCom m)) = Ctx (MonCom (H.map f m))

instance (SemigroupM m x, HasMonCom m x v) => SemigroupM m (Ctx v x) where
  (⋆) (Ctx c) (Ctx d) = Ctx <$> (c ⋆ d)

instance (Show v, Show x, DictKey v) => Show (Ctx v x) where
  show (Ctx γ) = showWith ", " (\x τ -> show x <> " : " <> show τ) γ

instance Default (Ctx v x)
type TypeCtx extra = Ctx Symbol (DMType :& extra)

-- newtype TypeCtx extra = TypeCtx ([Asgmt (DMType :& extra)] )
-- newtype TypeCtx extra = TypeCtx (MonCom (DMType :& extra) Symbol)
-- ([Asgmt (DMType :& extra)] )
  -- deriving (Generic, Show, DictLike Symbol (DMType :& extra))
-- instance Default (TypeCtx e)

-- data DMTypeOp where
--   Op1 :: DMTypeOp
--   deriving (Generic, Show)

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
  WrongNumberOfArgsOp :: Show a => a -> Int -> DMException
  ImpossibleError :: String -> DMException
  VariableNotInScope :: Show a => a -> DMException
  -- deriving (Generic, Show)

instance Show DMException where
  show (UnsupportedTermError t) = "The term '" <> show t <> "' is currently not supported."
  show (UnificationError a b) = "Could not unify '" <> show a <> "' with '" <> show b <> "'."
  show (WrongNumberOfArgs a b) = "While unifying: the terms '" <> show a <> "' and '" <> show b <> "' have different numbers of arguments"
  show (WrongNumberOfArgsOp op n) = "The operation " <> show op <> " was given a wrong number (" <> show n <> ") of args."
  show (ImpossibleError e) = "Something impossible happened: " <> show e
  show (VariableNotInScope v) = "Variable not in scope: " <> show v




data Lam_ = Lam_ [Asgmt JuliaType] DMTerm
  deriving (Generic, Show)

data DMTerm =
  Ret DMTerm
  | Sng Float JuliaType
  | Var Symbol JuliaType
  | Arg Symbol JuliaType
  | Op DMTypeOp_Some [DMTerm]
  | Phi DMTerm DMTerm DMTerm
  | Lam Lam_
  | LamStar Lam_
  | DPhi [Lam_]
  | Apply DMTerm [DMTerm]
  | Iter DMTerm DMTerm DMTerm
  | FLet Symbol [JuliaType] Lam_ DMTerm
-- ....
  deriving (Generic, Show)


