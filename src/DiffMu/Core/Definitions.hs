
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Core.Definitions where

import DiffMu.Prelude

import DiffMu.Core.Symbolic
import DiffMu.Abstract
import {-# SOURCE #-} DiffMu.Core.TC

import Data.Singletons.TH

import           Data.Singletons.Prelude hiding (Symbol)
import           Data.Singletons.Prelude.Enum (SEnum (..))
import           Data.Singletons.Prelude.List hiding (Group)

import qualified Data.Text as T

import Data.HashMap.Strict

import           Foreign.C.String
import           Foreign.C.Types
import           Foreign.Ptr

---------------------------------------------------------
-- Definition of Meta variables
--
-- We are going to need a type of variables/symbols which
-- do not only contain a string for a name, but also which
-- are annotated with some kind k from some type j containing
-- these kinds, i.e. (k :: j).
-- For this we use the `SymbolOf (k :: j)` type defined in our Prelude.

-- Here we simply add abbreviations for the variable types which we
-- are going to use.
-- The Notation with the "@" symbol comes from the "TypeApplications" ghc-extension.
-- It allows us to explicitly set "j := DMKind" or "j := SensKind". Such that the
-- k's with which TVarOf (resp. SVarOf) are annotated must come from the `DMKind`
-- (resp. `SensKind`) type.
type TVarOf = SymbolOf @DMKind
type SVarOf = SymbolOf @SensKind

-- We further add abbreviations for type/sens variables of their respective "main"-kind.
type TVar   = TVarOf MainKind
type SVar   = SVarOf MainSensKind

-- NOTE: Sensitivities only have a single kind, `MainSensKind`.

---------------------------------------------------------
-- Sensitivity and Privacy
--
-- The actual definition of sensitivity terms is in Core.Symbolic.
-- Here we only give it a different name .

-- In order to fit the same type classes (in particular Term, and MonadTerm from Abstract.Class),
-- sensitivities are also annotated with (k :: SensKind). Even though this type only contains a single
-- kind (MainSensKind :: SensKind). But because of this we also have a kinded, and an abbreviated definition:
type SensitivityOf = SymTerm
type Sensitivity = SymTerm MainSensKind

-- Privacies are defined similarly.
-- NOTE: Since they are currently not used anywhere, this definition is not battle tested.
--       We might want to define them slightly differently, for example using a newtype.
--       On the other hand, this seems to be the most sensible option currently, with the least syntactic overhead.
type PrivacyOf a = (SensitivityOf a,SensitivityOf a)
type Privacy = PrivacyOf MainSensKind




-------
--- TODO: REORDER FILE?
newtype JuliaType = JuliaType String
  deriving (Generic, Eq, Ord)



---------------------------------------------------------
-- Definition of DMTypes
--
-- Our DMTypes do not only contain the real types of the duet
-- type system, but also norm and clip expressions. To still
-- be able to differentiate between the different kinds of `DMTypes`,
-- We annotate their type with a term of `DMKind`.

--------------------
-- 1. DMKinds

data AnnotationKind = SensitivityK | PrivacyK

data LocationKind = GammaK | TauK

data Location (l :: LocationKind) where
  GammaLocation :: Sensitivity -> Location GammaK
  TauLocation :: SVar -> Location TauK

data Annotation (l :: LocationKind) (a :: AnnotationKind) where
  SensitivityAnnotation :: Location l -> Annotation l SensitivityK
  PrivacyAnnotation :: (Location l, Location l) -> Annotation l PrivacyK

data Signature (l :: LocationKind) where
  TauSignature :: [JuliaType] -> Signature TauK
  GammaSignature :: Signature GammaK

-- data Signature (s :: SignatureKind) where
--   MethodSignature :: [JuliaType] -> Signature MethodK
--   EmptySignature :: Signature EmptyK

-- type family Annotation (a :: Annotation) = (result :: *) | result -> a where
-- data family Annotation (a :: Annotation) :: *
-- data instance Annotation SensitivityK = SymTerm MainSensKind
-- data instance Annotation PrivacyK = (SymTerm MainSensKind, SymTerm MainSensKind)

-- data RealizeType (l :: Location) (a :: Annotation) where

-- data RealizeVar (a :: Annotation) where
--   RealizeSVar :: SVar -> RealizeVar SensitivityK
--   RealizePVar :: (SVar, SVar) -> RealizeVar PrivacyK

pattern Sens x = SensitivityAnnotation (GammaLocation x)
pattern Priv a b = PrivacyAnnotation (GammaLocation a, GammaLocation b)

instance Eq (Location GammaK) where
  (GammaLocation s) == (GammaLocation s') = (s == s')

instance Eq (Annotation GammaK a) where
  (SensitivityAnnotation a) == SensitivityAnnotation b = a == b
  (PrivacyAnnotation a) == PrivacyAnnotation b = a == b

instance (Monad t) => SemigroupM t (Annotation GammaK a) where
  (Sens a) ⋆ (Sens b) = Sens <$> ((a ⋆ b))
  (Priv x a) ⋆ (Priv y b) = Priv <$> (x ⋆ y) <*> (a ⋆ b)
  a ⋆ b = error "This is very strange, and shouldn't actually happen..."

instance Typeable a => MonoidM Identity (Annotation GammaK a) where
  neutral = let case1 = testEquality (typeRep @a) (typeRep @SensitivityK)
                case2 = testEquality (typeRep @a) (typeRep @PrivacyK)
            in case (case1, case2) of
                (Just Refl , _) -> pure $ Sens zeroId
                (_ , Just Refl) -> pure $ Priv zeroId zeroId
                _ -> undefined

instance Typeable a => CMonoidM Identity (Annotation GammaK a) where
  {-
-- type family Annotation SensitivityK = Sensitivity

-}
-- A `DMKind` is one of the following constructors:
data DMKind =
    MainKind
  | NumKind
  | BaseNumKind
  | ClipKind
  | NormKind
  | FunKind
  | NoFunKind
  | AnnotatedKind LocationKind AnnotationKind
  | ForAllKind
  deriving (Typeable)

-- Using the "TemplateHaskell" ghc-extension, and the following function from the singletons library,
-- we generate the `SingI` instances (and related stuff) needed to work with `DMKind` expressions on the type level.
genSingletons [''AnnotationKind]
genSingletons [''LocationKind]
genSingletons [''DMKind]

-- DMKinds are pretty printed as follows. For this we implement the `Show` typeclass for `DMKind`.
instance Show DMKind where
  show MainKind = "*"
  show NumKind = "Num"
  show BaseNumKind = "BaseNum"
  show ClipKind = "Clip"
  show NormKind = "Norm"
  show FunKind = "Fun"
  show NoFunKind = "NoFun"
  show (AnnotatedKind l a) = "Ann"
  show ForAllKind = "ForAll"
  -- show ReturnKind = "Return"

--------------------
-- 2. DMTypes

-- Now we can define our actual DMTypes.
-- We call the general case of a type of some kind k, `DMTypeOf k`.
-- The specific case of a type of "main" kind, we simply call `DMType`, i.e.:
type DMType = DMTypeOf NoFunKind
type DMFun = DMTypeOf FunKind

-- And we give a similar abbreviation for numeric dmtypes:
type DMNumType = DMTypeOf NumKind

-- The actual, generic definition of `DMTypeOf` for types of any kind `k` (for `k` in `DMKind`) is given as follows.
-- NOTE: We can write `(k :: DMKind)` here, because we use the `DataKinds` ghc-extension, which allows us to use
-- the terms in `DMKind` in a place where normally haskell types would be expected.
data DMTypeOf (k :: DMKind) where
  Deleted :: DMTypeOf k

  -- the base numeric constructors
  DMInt    :: DMTypeOf BaseNumKind
  DMReal   :: DMTypeOf BaseNumKind

  -- a base numeric type can be either constant or non constant or data
  Const    :: Sensitivity -> DMTypeOf BaseNumKind -> DMTypeOf NumKind
  NonConst :: DMTypeOf BaseNumKind -> DMTypeOf NumKind
  DMData   :: DMTypeOf NumKind

  -- we include numeric types into main types using this constructor
  Numeric  :: DMTypeOf NumKind -> DMType

  -- type vars can be of any kind (k :: DMKind). But we require the constraint that
  -- k be typeable, because it is needed in cases where we want to compare different k's.
  TVar :: IsKind k => SymbolOf k -> DMTypeOf k

  -- the arrow type
  (:->:) :: [DMTypeOf (AnnotatedKind GammaK SensitivityK)] -> DMTypeOf (AnnotatedKind TauK SensitivityK) -> DMFun

  -- the privacy-arrow type
  (:->*:) :: [DMTypeOf (AnnotatedKind GammaK PrivacyK)] -> DMTypeOf (AnnotatedKind TauK PrivacyK) -> DMFun

  -- tuples
  DMTup :: [DMType] -> DMType

   --- matrix norms
  L1 :: DMTypeOf NormKind
  L2 :: DMTypeOf NormKind
  LInf :: DMTypeOf NormKind

  -- embed norms into ClipKind
  U :: DMTypeOf ClipKind
  Clip :: DMTypeOf NormKind -> DMTypeOf ClipKind

  -- matrices
  DMMat :: (DMTypeOf NormKind) -> (DMTypeOf ClipKind) -> Sensitivity -> Sensitivity -> DMType -> DMType

  -- choices
  DMChoice :: [DMType :& (Maybe [JuliaType], Sensitivity)] -> DMType

  -- foralls
  ForAll :: [SomeK TVarOf] -> DMTypeOf FunKind -> DMTypeOf ForAllKind

  -- annotations
  NoFun :: DMExtra a => (DMTypeOf NoFunKind :& Annotation l a) -> DMTypeOf (AnnotatedKind l a)
  Fun :: [DMTypeOf ForAllKind :& (Signature l, Annotation l a)] -> DMTypeOf (AnnotatedKind l a)
  (:∧:) :: (DMExtra a) => DMTypeOf (AnnotatedKind l a) -> DMTypeOf (AnnotatedKind l a) -> DMTypeOf (AnnotatedKind l a) -- infimum
  (:↷:) :: Sensitivity -> DMTypeOf (AnnotatedKind GammaK a) -> DMTypeOf (AnnotatedKind GammaK a) -- scale
  Trunc :: (DMExtra a, DMExtra b) => Annotation GammaK a -> DMTypeOf (AnnotatedKind GammaK b) -> DMTypeOf (AnnotatedKind GammaK a)
  -- TruncFunc :: DMExtra a => Annotation a -> [DMTypeOf ForAllKind :& (Sensitivity)] -> DMTypeOf (AnnotatedKind a)

  -- ReturnFun :: [DMTypeOf ForAllKind :& ([JuliaType], SVar)] -> DMTypeOf ReturnKind
  -- ReturnNoFun :: (DMTypeOf NoFunKind :& SVar) -> DMTypeOf ReturnKind
  -- ReturnInfimum :: DMTypeOf ReturnKind -> DMTypeOf ReturnKind -> DMTypeOf ReturnKind

type DMExtra e = (Typeable e, SingI e)
--                   Eq (Annotation e), Show (Annotation e),
--                   CMonoidM Identity (Annotation e),
--                   -- Substitute SVarOf SensitivityOf (Annotation e), FreeVars TVarOf (Annotation e),
--                   -- Unify MonadDMTC (Annotation e) --, (HasNormalize MonadDMTC (Annotation e))
--                  )

instance Show (Annotation l a) where
  show (SensitivityAnnotation s) = show s
  show (PrivacyAnnotation p) = show p

instance Show (Location l) where
  show (GammaLocation s) = show s
  show (TauLocation s) = show s

instance Show (Signature l) where
   show (TauSignature s) = show s
   show GammaSignature = ""


-- Types are pretty printed as follows.
instance Show (DMTypeOf k) where
  show Deleted = "Deleted"
  show DMInt = "Int"
  show DMReal = "Real"
  show DMData = "Data"
  show (Const s t) = show t <> "[" <> show s <> "]"
  show (NonConst t) = show t <> "[--]"
  show (Numeric t) = "Num(" <> show t <> ")"
  show (TVar t) = show t
  show (a :->: b) = "(" <> show a <> " -> " <> show b <> ")"
  show (a :->*: b) = "(" <> show a <> " ->* " <> show b <> ")"
  show (DMTup ts) = "Tupl(" <> show ts <> ")"
  show L1 = "L1"
  show L2 = "L2"
  show LInf = "L∞"
  show U = "U"
  show (Clip n) = "Clip(" <> show n <> ")"
  show (DMMat nrm clp n m τ) = "Matrix<n: "<> show nrm <> ", c: " <> show clp <> ">[" <> show n <> " × " <> show m <> "](" <> show τ <> ")"
  show (DMChoice cs) = "Choice{" <> show cs <> "}"
  show (ForAll vs f) = case vs of
     [] -> show f
     _ -> "ForAll {" <> show vs <> "}. " <> show f
  show (NoFun x) = show x --"NoFun(" <> show x <> ")"
  show (Fun xs) = "Fun(" <> show xs <> ")"
  show (a :↷: x) = show a <> " ↷ " <> show x
  show (x :∧: y) = "(" <> show x <> "∧" <> show y <> ")"
  show (Trunc a x) = "|" <> show x <> "|_" <> show a
  -- show (TruncFunc a x) = "|" <> show x <> "|_" <> show a
  -- show (ReturnNoFun x) = "Return (" <> show x <> ")"--"NoFun(" <> show x <> ")"
  -- show (ReturnFun xs) =  "RFun(" <> show xs <> ")"
  -- show (ReturnInfimum x y) =  "Return (" <> show x <> "∧" <> show y <> ")"


instance Eq (DMTypeOf NormKind) where
  L1 == L1 = True
  L2 == L2 = True
  LInf == LInf = True
  TVar a == TVar b = a == b
  _ == _ = False

instance Eq (DMTypeOf ClipKind) where
  U == U = True
  Clip c == Clip d = c == d
  TVar a == TVar b = a == b
  _ == _ = False

-- instance Ord (DMTypeOf ClipKind) where

--------------------
-- 3. Additional Notation
--
-- We sometimes want to pair a type with a sensitivity, just as in the arrow
-- type constructor in DMType. For this we define the type (a :& b), which is
-- effectively just a tuple (a,b). But this gives us this new notation, and
-- terms (x :@ y) :: (a :& b) are pretty printed with an "@".

infix 3 :@
data (:&) a b = (:@) a b
  deriving (Generic)

instance (Show a, Show b) => Show (a :& b) where
  show (a :@ b) = show a <> " @ " <> show b

-- Since we want to use (monadic-)algebraic operations on terms of type `(a :& b)`,
-- we declare these instances here. That is, if `a` and `b` have such instances,
-- then (a :& b) has them as well:

-- (a :& b) is a monadic semigroup.
instance (SemigroupM t a, SemigroupM t b) => SemigroupM t (a :& b) where
  (⋆) (a₁ :@ b₁) (a₂ :@ b₂) = (:@) <$> (a₁ ⋆ a₂) <*> (b₁ ⋆ b₂)

-- (a :& b) is a monadic monoid.
instance (MonoidM t a, MonoidM t b) => MonoidM t (a :& b) where
  neutral = (:@) <$> neutral <*> neutral

-- (a :& b) is a monadic monoid in which an explicit equality check with the neutral element
-- is possible.
instance (CheckNeutral m a, CheckNeutral m b) => CheckNeutral m (a :& b) where
  checkNeutral (a :@ b) = (\a b -> and [a,b]) <$> checkNeutral a <*> checkNeutral b

-- NOTE: The monoidal operation for sensitivities is addition.
--       The operation for DMTypes is unification.
--       That means, given `(x :@ s), (y :@ t) :: (DMType :& Sensitivity)`,
--       computing `(x :@ s) ⋆ (y :@ t)` unifies `x` and `y`, and sums `s` and `t`.
--       The result lives in a monad.

fstAnn :: (a :& b) -> a
fstAnn (a :@ b) = a

sndAnn :: (a :& b) -> b
sndAnn (a :@ b) = b


-- fstAnnI :: (WithRelev b) -> DMType
-- fstAnnI (WithRelev _ (a :@ b)) = a

-- sndAnnI :: WithRelev b -> (Annotation b)
-- sndAnnI (WithRelev _ (a :@ b)) = b


---------------------------------------------------------
-- Julia types
--
-- Our representation is obviously very rudimentary currently.
-- It is split into two parts because we use the `JuliaNumType`
-- to annotate singleton terms with their type.

-- data JuliaNumType = JTNumInt | JTNumReal
--   deriving (Generic, Show, Eq)

-- instance Hashable JuliaNumType

-- data JuliaType = JTAny | JTNum JuliaNumType
--   deriving (Generic, Show, Eq)

instance Hashable JuliaType where

instance Show JuliaType where
  show (JuliaType str) = show str

pattern JTAny = JuliaType "Any"
pattern JTNumInt = JuliaType "Integer"
pattern JTNumReal = JuliaType "Real"

--------------------------------------
-- Tracked CString
-- data JuliaType = JuliaType String CString
--   deriving (Generic, Eq)

-- instance Hashable JuliaType where

-- instance Show JuliaType where
--   show (JuliaType str _) = show str

-- pattern JTAny a = JuliaType "Any" a
-- pattern JTNumInt a = JuliaType "Integer" a
-- pattern JTNumReal a = JuliaType "Real" a

-------------------------------------

-- instance Hashable JuliaType

-- NOTE: The "deriving(Generic,Show)" part is a feature of Haskell which
--       allows us to automatically generate instances for type classes.
--       In this case an instance for Show (conversion to String),
--       and for Generic (used for further automatic derivation of
--       serialization instances or, in our case, instances of Default).
--       But if the data types contain multiple type parameters
--       or existential quantification, such an automatic derivation is
--       unfortunately no longer possible.


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
  deriving (Generic, Eq, Ord)

-- The type of all possible binary type operations.
data DMTypeOps_Binary =
   DMOpAdd
   | DMOpSub
   | DMOpMul
   | DMOpDiv
   | DMOpMod
   | DMOpEq
  deriving (Generic, Eq, Ord)


data DMTypeOp_Some = IsUnary DMTypeOps_Unary | IsBinary DMTypeOps_Binary
  deriving (Show, Generic, Eq, Ord)

instance Show DMTypeOps_Unary where
  show DMOpCeil = "ceil"

instance Show DMTypeOps_Binary where
  show DMOpAdd = "+"
  show DMOpSub = "-"
  show DMOpMul = "*"
  show DMOpDiv = "/"
  show DMOpMod = "%"
  show DMOpEq = "=="

-- An application of a type operation to an appropriate number of type arguments
data DMTypeOp =
     UnaryNum DMTypeOps_Unary   (DMTypeOf NumKind :& SVar) (DMTypeOf NumKind)
   | BinaryNum DMTypeOps_Binary (DMTypeOf NumKind :& SVar , DMTypeOf NumKind :& SVar) (DMTypeOf NumKind)
  deriving (Show)


--------------------------------------------------------------------------
-- Constraints
--
-- Constraints are axiomatized as wrappers around their content. Every kind
-- of constraint *is* its own wrapper type, that is, we have:
--
-- IsEqual :: Type -> Type
-- IsLessEqual :: Type -> Type
-- IsTypeOpResult :: Type -> Type
-- ...
--
-- And usually these wrappers have constructors of the same name as their type,
-- i.e., we have, forall a:
--
--  Term constructor
--   |               Type constructor
--   |                |
--   v                v
-- IsEqual :: a -> IsEqual a
-- IsLessEqual :: a -> IsLessEqual a
-- IsTypeOpResult :: a -> IsTypeOpResult a
-- ...
--
-- For example, we have:
newtype IsTypeOpResult a = IsTypeOpResult a
  deriving (Show)
--
-- The idea is that `a` represents the data which is the actual content which needs
-- to be solved by this constraint, and the type of the wrapper around it tells us
-- what kind of constraint this is.
-- For example, it makes sens to have `IsEqual (DMType,DMType)` or `IsMaximum (Sensitivity,Sensitivity,Sensitivity)`
-- or `IsTypeOpResult DMTypeOp`.
--
-- Having the generic type parameter a allows us to treat all constraints equally,
-- in cases where we are writing generic code for dealing with any kind of constraints.
-- In order for this to work, we have to proof that our "constraint type" is nothing
-- but a wrapper around `a`. For this, we show that it is an instance of the `TCConstraint`
-- type class, for example:
instance TCConstraint IsTypeOpResult where
  constr = IsTypeOpResult
  runConstr (IsTypeOpResult c) = c
  -- where
  --
  -- `constr` :: a -> c a
  --  requires that we can put our "data" into the constraint.
  --
  -- `runConstr` :: c a -> a
  --  requires that we can extract our "data" from the constraint.
--
--
-- There are two further type classes associated with constraints:
-- 1. Constraints exist in order to be solved. This is axiomatized by the typeclass
--    `Solve isT c a`, which says that the class of monads described by `isT`
--    (e.g., `isT := MonadDMTC`) can solve constraints of (wrapper-)type `c`
--    with data `a`.
--
--    For example, we have the instance `Solve MonadDMTC IsTypeOpResult DMTypeOp`
--    (see in DiffMu.Typecheck.Operations).
--    But also `Solve MonadDMTC IsEqual (DMTypeOf k)`, for any k.
--    (see in DiffMu.Core.Unification).
--    These instances implement the `solve_` function which runs in the `MonadDMTC` monad
--    and tries to solve the constraint.
--
--    NOTE: we use a class of monads `isT` here, instead of a specific monad `t` here, because
--          of the following problem: It should be possible to add a constraint while in the
--          sensitivity typechecking monad (`TC Sensitivity a`) but solve it in the privacy monad.
--          Thus we define "solvability" for the whole class of TC like monads at once.
--          That is, for the class `MonadDMTC`.
--
-- 2. While typechecking (and/or solving constraints) we sometimes have to add new constraints.
--    The typeclass `MonadConstraint isT t` expresses that, the monad `t` allows us to
--    add, discharge or update constraints which are solvable by monads in the class `isT`.
--    All monads in the `MonadDMTC` class are instances of `MonadConstraint MonadDMTC`.
--
--    But to reiterate: the Haskell type system only allows to add a constraint `c`, via
--    ```
--    do addConstraint (Solvable (c))
--    ```
--    if there is an instance of `Solve isT c a` currently in scope.
--
--
-- NOTE: The basic constraints definitions for equality/less-equal are located
--       in Abstract.Class.Constraint.
--       Here, also the definition of `Solvable` and `MonadConstraint` is to be found.
--


--------------------------------------------------------------------------
-- DMTerm
--

type Clip = DMTypeOf ClipKind

data Asgmt a = (:-) Symbol a
  deriving (Generic, Show, Eq, Ord)

fstA :: Asgmt a -> Symbol
fstA (x :- τ) = x

sndA :: Asgmt a -> a
sndA (x :- τ) = τ

-- data Lam_ = Lam_ [Asgmt JuliaType] DMTerm
--   deriving (Generic, Show)

data DMTerm =
  Ret DMTerm
  | Sng Float JuliaType
  | Var Symbol JuliaType
  | Arg Symbol JuliaType Relevance
  | Op DMTypeOp_Some [DMTerm]
  | Phi DMTerm DMTerm DMTerm
  | Lam     [Asgmt JuliaType] DMTerm
  | LamStar [(Asgmt JuliaType, Relevance)] DMTerm
  | Apply DMTerm [DMTerm]
  | FLet Symbol [JuliaType] DMTerm DMTerm
  | Choice (HashMap [JuliaType] DMTerm)
  | SLet (Asgmt JuliaType) DMTerm DMTerm
  | Tup [DMTerm]
  | TLet [(Asgmt JuliaType)] DMTerm DMTerm
  | Gauss DMTerm DMTerm DMTerm DMTerm
  | MCreate DMTerm DMTerm DMTerm
  | ClipM Clip DMTerm
  | Iter DMTerm DMTerm DMTerm
  | Loop DMTerm DMTerm (Symbol, Symbol) DMTerm
-- ....
  deriving (Generic, Show, Eq)


--------------------------------------------------------------------------
-- DMException
--
-- The different kinds of errors we can throw.

data DMException where
  UnsupportedTermError    :: DMTerm -> DMException
  UnificationError        :: Show a => a -> a -> DMException
  WrongNumberOfArgs       :: Show a => a -> a -> DMException
  WrongNumberOfArgsOp     :: Show a => a -> Int -> DMException
  ImpossibleError         :: String -> DMException
  InternalError           :: String -> DMException
  VariableNotInScope      :: Show a => a -> DMException
  UnsatisfiableConstraint :: String -> DMException
  TypeMismatchError       :: String -> DMException
  NoChoiceFoundError      :: String -> DMException

instance Show DMException where
  show (UnsupportedTermError t) = "The term '" <> show t <> "' is currently not supported."
  show (UnificationError a b) = "Could not unify '" <> show a <> "' with '" <> show b <> "'."
  show (WrongNumberOfArgs a b) = "While unifying: the terms '" <> show a <> "' and '" <> show b <> "' have different numbers of arguments"
  show (WrongNumberOfArgsOp op n) = "The operation " <> show op <> " was given a wrong number (" <> show n <> ") of args."
  show (ImpossibleError e) = "Something impossible happened: " <> e
  show (InternalError e) = "Internal error: " <> e
  show (VariableNotInScope v) = "Variable not in scope: " <> show v
  show (UnsatisfiableConstraint c) = "The constraint " <> c <> " is not satisfiable."
  show (TypeMismatchError e) = "Type mismatch: " <> e
  show (NoChoiceFoundError e) = "No choice found: " <> e



--------------------------------------------------------------------------
-- The environment for executing typechecking

data DMEnv = DMEnv
  {
    -- askJuliaSubtypeOf :: Maybe (FunPtr (JuliaType -> JuliaType -> Bool))
    askJuliaSubtypeOf :: Maybe (FunPtr (CString -> CString -> Bool))
  }
makeDMEnv :: FunPtr (CString -> CString -> Bool) -> DMEnv
makeDMEnv subtype = DMEnv
  { askJuliaSubtypeOf = Just $ subtype
  -- { askJuliaSubtypeOf = Just $ \(JuliaType _ a) (JuliaType _ b) -> subtype a b
  }
makeEmptyDMEnv :: DMEnv
makeEmptyDMEnv = DMEnv
  { askJuliaSubtypeOf = Nothing
  }


-------------------------------------------------------------------------
-- Relevance Annotations

data Relevance = IsRelevant | NotRelevant
  deriving (Eq, Ord)

instance Show Relevance where
   show IsRelevant = "interesting"
   show NotRelevant = "uninteresting"

data WithRelev extra = WithRelev Relevance (DMTypeOf (AnnotatedKind GammaK extra))

instance Semigroup Relevance where
  (<>) IsRelevant b = IsRelevant
  (<>) a IsRelevant = IsRelevant
  (<>) _ _ = NotRelevant

instance Show (WithRelev e) where
  show (WithRelev IsRelevant  x) = show x
  show (WithRelev NotRelevant x) = "{" <> show x <> "}"

makeRelev :: (DMTypeOf (AnnotatedKind GammaK e)) -> WithRelev e
makeRelev = WithRelev IsRelevant

makeNotRelev :: (DMTypeOf (AnnotatedKind GammaK e)) -> WithRelev e
makeNotRelev = WithRelev NotRelevant

