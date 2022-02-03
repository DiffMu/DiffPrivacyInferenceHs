
{-# LANGUAGE TemplateHaskell, UndecidableInstances #-}

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
-- Definition of DMTypes
--
-- Our DMTypes do not only contain the real types of the duet
-- type system, but also norm and clip expressions. To still
-- be able to differentiate between the different kinds of `DMTypes`,
-- We annotate their type with a term of `DMKind`.

--------------------
-- 1. DMKinds

data AnnotationKind = SensitivityK | PrivacyK
  deriving Show

-- type family Annotation (a :: AnnotationKind) = (result :: *) | result -> a where
-- data family Annotation (a :: AnnotationKind) :: *
-- data instance Annotation SensitivityK = SymTerm MainSensKind
-- data instance Annotation PrivacyK = (SymTerm MainSensKind, SymTerm MainSensKind)

data Annotation (a :: AnnotationKind) where
  SensitivityAnnotation :: SymTerm MainSensKind -> Annotation SensitivityK
  PrivacyAnnotation :: (SymTerm MainSensKind, SymTerm MainSensKind) -> Annotation PrivacyK

instance Eq (Annotation a) where
  (SensitivityAnnotation a) == SensitivityAnnotation b = a == b
  (PrivacyAnnotation a) == PrivacyAnnotation b = a == b

instance Monad t => SemigroupM t (Annotation a) where
  (SensitivityAnnotation a) ⋆ (SensitivityAnnotation b) = SensitivityAnnotation <$> (a ⋆ b)
  (PrivacyAnnotation a) ⋆ (PrivacyAnnotation b) = PrivacyAnnotation <$> (a ⋆ b)

instance Monad t => CheckNeutral t (Annotation a) where
  checkNeutral (SensitivityAnnotation s) = checkNeutral s
  checkNeutral (PrivacyAnnotation s) = checkNeutral s

instance Typeable a => MonoidM Identity (Annotation a) where
  neutral = let case1 = testEquality (typeRep @a) (typeRep @SensitivityK)
                case2 = testEquality (typeRep @a) (typeRep @PrivacyK)
            in case (case1, case2) of
                (Just Refl , _) -> pure $ SensitivityAnnotation zeroId
                (_ , Just Refl) -> pure $ PrivacyAnnotation (zeroId, zeroId)
                _ -> undefined

instance Typeable a => CMonoidM Identity (Annotation a) where
-- type family Annotation SensitivityK = Sensitivity

-- A `DMKind` is one of the following constructors:
data DMKind =
    MainKind
  | NumKind
  | BaseNumKind
  | ClipKind
  | NormKind
  | FunKind
  | NoFunKind
  | VecKindKind
  deriving (Typeable)

-- Using the "TemplateHaskell" ghc-extension, and the following function from the singletons library,
-- we generate the `SingI` instances (and related stuff) needed to work with `DMKind` expressions on the type level.
genSingletons [''AnnotationKind]
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
  show VecKindKind = "VecKindKind"

-- so we don't get incomplete pattern warnings for them
{-# COMPLETE DMInt, DMReal, Const, NonConst, DMData, Numeric, TVar, (:->:), (:->*:), DMTup, L1, L2, LInf, U, Clip, Vector, Gradient, Matrix,
 DMContainer, DMVec, DMGrads, DMMat, DMModel, NoFun, Fun, (:∧:), BlackBox, Deepcopied #-}

--------------------
-- 2. DMTypes

-- Now we can define our actual DMTypes.
-- We call the general case of a type of some kind k, `DMTypeOf k`.
-- The specific case of a type of "main" kind, we simply call `DMType`, i.e.:
type DMMain = DMTypeOf MainKind
type DMType = DMTypeOf NoFunKind
type DMFun = DMTypeOf FunKind

-- And we give a similar abbreviation for numeric dmtypes:
type DMNum = DMTypeOf NumKind

-- Abbreviation for veckinds
type VecKind = DMTypeOf VecKindKind

pattern DMVec n c d t = DMContainer Vector n c d t
pattern DMMat n c r d t = DMContainer (Matrix r) n c d t
pattern DMGrads n c d t = DMContainer Gradient n c d t

-- The actual, generic definition of `DMTypeOf` for types of any kind `k` (for `k` in `DMKind`) is given as follows.
-- NOTE: We can write `(k :: DMKind)` here, because we use the `DataKinds` ghc-extension, which allows us to use
-- the terms in `DMKind` in a place where normally haskell types would be expected.
data DMTypeOf (k :: DMKind) where
  -- a "virtual" type of which everything is a subtype
  -- we need this in places where we require stuff to
  -- be subtype of some julia type, and do not need
  -- additional information about possible refinements
  DMAny :: DMTypeOf k

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
  (:->:) :: [DMTypeOf MainKind :@ Sensitivity] -> DMTypeOf MainKind -> DMFun

  -- the privacy-arrow type
  (:->*:) :: [DMTypeOf MainKind :@ Privacy] -> DMTypeOf MainKind -> DMFun

  -- tuples
  DMTup :: [DMType] -> DMType

   --- matrix norms
  L1 :: DMTypeOf NormKind
  L2 :: DMTypeOf NormKind
  LInf :: DMTypeOf NormKind

  -- embed norms into ClipKind
  U :: DMTypeOf ClipKind
  Clip :: DMTypeOf NormKind -> DMTypeOf ClipKind

  -- veckinds
  Vector :: VecKind
  Gradient :: VecKind
  Matrix :: Sensitivity -> VecKind

  -- matrices
  DMContainer :: VecKind -> (DMTypeOf NormKind) -> (DMTypeOf ClipKind) -> Sensitivity -> DMMain -> DMType
  --DMMat :: (DMTypeOf NormKind) -> (DMTypeOf ClipKind) -> Sensitivity -> Sensitivity -> DMMain -> DMType
  DMModel :: Sensitivity -> DMNum -> DMType -- number of parameters and element type

  -- annotations
  NoFun :: DMType -> DMTypeOf MainKind
  Fun :: [DMTypeOf FunKind :@ Maybe [JuliaType]] -> DMTypeOf MainKind
  (:∧:) :: DMTypeOf MainKind -> DMTypeOf MainKind -> DMTypeOf MainKind -- infimum

  -- black box functions (and a wrapper to make them MainKind but still have a BlackBoxKind so we can have TVars of it)
  BlackBox :: [JuliaType] -> DMTypeOf MainKind

  -- deep copied type, thus allowed to be returned from functions
  Deepcopied :: DMType -> DMType



instance Hashable (DMTypeOf k) where
  hashWithSalt s (DMInt) = s +! 1
  hashWithSalt s (DMReal) = s +! 2
  hashWithSalt s (DMData) = s +! 3
  hashWithSalt s (L1) = s +! 4
  hashWithSalt s (L2) = s +! 5
  hashWithSalt s (LInf) = s +! 6
  hashWithSalt s (U) = s +! 7
  hashWithSalt s (DMAny) = s +! 8
  hashWithSalt s (Vector) = s +! 9
  hashWithSalt s (Gradient) = s +! 10
  hashWithSalt s (Const n t) = s `hashWithSalt` n `hashWithSalt` t
  hashWithSalt s (NonConst t) = s `hashWithSalt` t
  hashWithSalt s (Numeric t) = s `hashWithSalt` t
  hashWithSalt s (TVar t) = s `hashWithSalt` t
  hashWithSalt s (n :->: t) = s `hashWithSalt` n `hashWithSalt` t
  hashWithSalt s (n :->*: t) = s `hashWithSalt` n `hashWithSalt` t
  hashWithSalt s (DMTup t) = s `hashWithSalt` t
  hashWithSalt s (Matrix t) = s `hashWithSalt` t
  hashWithSalt s (Clip t) = s `hashWithSalt` t
  hashWithSalt s (DMContainer k n t u v) = s `hashWithSalt` k `hashWithSalt` n `hashWithSalt` t `hashWithSalt` u `hashWithSalt` v
--  hashWithSalt s (DMMat n t u v w) = s `hashWithSalt` n `hashWithSalt` t `hashWithSalt` u `hashWithSalt` v `hashWithSalt` w
  hashWithSalt s (DMModel u v) = s `hashWithSalt` u `hashWithSalt` v
  hashWithSalt s (Fun t) = s `hashWithSalt` t
  hashWithSalt s (NoFun t) = s `hashWithSalt` t
  hashWithSalt s (n :∧: t) = s `hashWithSalt` n `hashWithSalt` t
  hashWithSalt s (BlackBox n) = s `hashWithSalt` n
  hashWithSalt s (Deepcopied n) = s `hashWithSalt` n

instance (Hashable a, Hashable b) => Hashable (a :@ b) where
  hashWithSalt s (a:@ b) = s `hashWithSalt` a `hashWithSalt` b

type DMExtra e = (Typeable e, SingI e)
--                   Eq (Annotation e), Show (Annotation e),
--                   CMonoidM Identity (Annotation e),
--                   -- Substitute SVarOf SensitivityOf (Annotation e), FreeVars TVarOf (Annotation e),
--                   -- Unify MonadDMTC (Annotation e) --, (HasNormalize MonadDMTC (Annotation e))
--                  )

instance Show (Annotation a) where
  show (PrivacyAnnotation p) = show p
  show (SensitivityAnnotation s) = show s

-- Types are pretty printed as follows.
instance Show (DMTypeOf k) where
  show DMAny = "DMAny"
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
  show Vector = "Vector"
  show Gradient = "Gradient"
  show (Matrix n) = show n <> "-row Matrix"
  show (Clip n) = "Clip(" <> show n <> ")"
  show (DMVec nrm clp n τ) = "Vector<n: "<> show nrm <> ", c: " <> show clp <> ">[" <> show n <> "](" <> show τ <> ")"
  show (DMMat nrm clp n m τ) = "Matrix<n: "<> show nrm <> ", c: " <> show clp <> ">[" <> show n <> " × " <> show m <> "](" <> show τ <> ")"
  show (DMModel m τ) = "Model[" <> show m <> "](" <> show τ <> ")"
  show (DMGrads nrm clp m τ) = "Grads<n: "<> show nrm <> ", c: " <> show clp <> ">[" <> show m <> "](" <> show τ <> ")"
  show (DMContainer k nrm clp m τ) = "Container("<> show k <> ")<n: "<> show nrm <> ", c: " <> show clp <> ">[" <> show m <> "](" <> show τ <> ")"
  show (NoFun x) = "NoFun(" <> show x <> ")"
  show (Fun xs) = "Fun(" <> show xs <> ")"
  show (x :∧: y) = "(" <> show x <> "∧" <> show y <> ")"
  show (BlackBox n) = "BlackBox [" <> show n <> "]"
  show (Deepcopied n) = "Deepcopied [" <> show n <> "]"

showArgPretty :: (ShowPretty a, ShowPretty b) => (a :@ b) -> String
showArgPretty (a :@ b) = "-  " <> showPretty a <> "\n"
                      <> "    @ " <> showPretty b <> "\n"

showFunPretty :: (ShowPretty a, ShowPretty b) => String -> [(a :@ b)] -> a -> String
showFunPretty marker args ret = intercalate "\n" (fmap showArgPretty args)
                         <> "--------------------------\n"
                         <> " " <> marker <> " " <> (showPretty ret)

showPrettyEnumVertical :: (ShowPretty a) => [a] -> String
showPrettyEnumVertical as = "{\n" <> intercalate "\n,\n" (fmap (justIndent . showPretty) as) <> "\n}"

instance ShowPretty (Sensitivity) where
  showPretty s = show s

instance ShowPretty (SymbolOf k) where
  showPretty = show

instance (ShowPretty a, ShowPretty b) => ShowPretty (a :@ b) where
  showPretty (a :@ b) = showPretty a <> " @ " <> showPretty b


instance ShowPretty (DMTypeOf k) where
  showPretty DMAny = "DMAny"
  showPretty DMInt = "Int"
  showPretty DMReal = "Real"
  showPretty DMData = "Data"
  showPretty (Const s t) = showPretty t <> "[" <> showPretty s <> "]"
  showPretty (NonConst t) = "NonConst " <> showPretty t
  showPretty (Numeric t) = showPretty t
  showPretty (TVar t) = showPretty t
  showPretty (a :->: b) = showFunPretty "->" a b
  showPretty (a :->*: b) = showFunPretty "->*" a b
  showPretty (DMTup ts) = showPretty ts
  showPretty L1 = "L1"
  showPretty L2 = "L2"
  showPretty LInf = "L∞"
  showPretty U = "U"
  showPretty Vector = "Vector"
  showPretty Gradient = "Gradient"
  showPretty (Matrix n) = showPretty n <> "-row Matrix"
  showPretty (Clip n) = showPretty n
  showPretty (DMVec nrm clp n τ) = "Vector<n: "<> showPretty nrm <> ", c: " <> showPretty clp <> ">[" <> showPretty n <> "](" <> showPretty τ <> ")"
  showPretty (DMMat nrm clp n m τ) = "Matrix<n: "<> showPretty nrm <> ", c: " <> showPretty clp <> ">[" <> showPretty n <> " × " <> showPretty m <> "](" <> showPretty τ <> ")"
  showPretty (DMModel m τ) = "DMModel[" <> showPretty m <> "](" <> showPretty τ <> ")"
  showPretty (DMGrads nrm clp m τ) = "DMGrads<n: "<> showPretty nrm <> ", c: " <> showPretty clp <> ">[" <> showPretty m <> "](" <> showPretty τ <> ")"
  showPretty (DMContainer k nrm clp m τ) = "DMContainer{" <> show k <> "}<n: "<> showPretty nrm <> ", c: " <> showPretty clp <> ">[" <> showPretty m <> "](" <> showPretty τ <> ")"
  showPretty (NoFun x) = showPretty x
  showPretty (Fun xs) = showPrettyEnumVertical (fmap fstAnn xs)
  showPretty (x :∧: y) = "(" <> showPretty x <> "∧" <> showPretty y <> ")"
  showPretty (BlackBox n) = "BlackBox[" <> showPretty n <> "]"
  showPretty (Deepcopied n) = "Deepcopied[" <> showPretty n <> "]"


-- instance Eq (DMTypeOf NormKind) where
--   _ == _ = False

-- instance Eq (DMTypeOf ClipKind) where

instance Eq (DMTypeOf k) where
  -- special
  TVar a == TVar b = a == b

  -- ClipKind
  U == U = True
  Clip c == Clip d = c == d

  -- NormKind
  L1 == L1 = True
  L2 == L2 = True
  LInf == LInf = True


  -- VecKind
  Vector == Vector = True
  Gradient == Gradient = True
  Matrix r1 == Matrix r2 = r1 == r2

  -- the base numeric constructors
  DMInt    == DMInt = True
  DMReal   == DMReal = True

  -- a base numeric type can be either constant or non constant or data
  Const s t == Const s2 t2 = and [s == s2, t == t2]
  NonConst t == NonConst t2 = t == t2
  DMData   == DMData = True

  -- we include numeric types into main types using this constructor
  Numeric t1 == Numeric t2 = t1 == t2


  -- the arrow type
  (xs :->: x) == (ys :->: y) = and [xs == ys, x == y]

  -- the privacy-arrow type
  (xs :->*: x) == (ys :->*: y) = and [xs == ys, x == y]

  -- tuples
  DMTup xs == DMTup ys = xs == ys

  -- matrices
  DMContainer k a b c d == DMContainer k2 a2 b2 c2 d2 = and [k == k2, a == a2, b == b2, c == c2, d == d2]
--  DMVec a b c d == DMVec a2 b2 c2 d2 = and [a == a2, b == b2, c == c2, d == d2]
--  DMVec a b c d == DMVec a2 b2 c2 d2 = and [a == a2, b == b2, c == c2, d == d2]
--  DMMat a b c d e == DMMat a2 b2 c2 d2 e2 = and [a == a2, b == b2, c == c2, d == d2, e == e2]

  -- annotations
  NoFun t == NoFun s = t == s
  Fun ts == Fun ss = ts == ss
  (a :∧: b) == (a2 :∧: b2) = and [a == a2, b == b2]

  (BlackBox n1) == (BlackBox n2) = n1 == n2

  -- Error case
  _ == _ = False




-- instance Ord (DMTypeOf ClipKind) where

--------------------
-- 3. Additional Notation
--
-- We sometimes want to pair a type with a sensitivity, just as in the arrow
-- type constructor in DMType. For this we define the type (a :@ b), which is
-- effectively just a tuple (a,b). But this gives us this new notation, and
-- terms (x :@ y) :: (a :@ b) are pretty printed with an "@".

infix 3 :@
data (:@) a b = (:@) a b
  deriving (Generic, Eq)

instance (Show a, Show b) => Show (a :@ b) where
  show (a :@ b) = show a <> " @ " <> show b

-- Since we want to use (monadic-)algebraic operations on terms of type `(a :@ b)`,
-- we declare these instances here. That is, if `a` and `b` have such instances,
-- then (a :@ b) has them as well:

-- (a :@ b) is a monadic semigroup.
instance (SemigroupM t a, SemigroupM t b) => SemigroupM t (a :@ b) where
  (⋆) (a₁ :@ b₁) (a₂ :@ b₂) = (:@) <$> (a₁ ⋆ a₂) <*> (b₁ ⋆ b₂)

-- (a :@ b) is a monadic monoid.
instance (MonoidM t a, MonoidM t b) => MonoidM t (a :@ b) where
  neutral = (:@) <$> neutral <*> neutral

-- (a :@ b) is a monadic monoid in which an explicit equality check with the neutral element
-- is possible.
instance (CheckNeutral m a, CheckNeutral m b) => CheckNeutral m (a :@ b) where
  checkNeutral (a :@ b) = (\a b -> and [a,b]) <$> checkNeutral a <*> checkNeutral b

-- NOTE: The monoidal operation for sensitivities is addition.
--       The operation for DMTypes is unification.
--       That means, given `(x :@ s), (y :@ t) :: (DMType :@ Sensitivity)`,
--       computing `(x :@ s) ⋆ (y :@ t)` unifies `x` and `y`, and sums `s` and `t`.
--       The result lives in a monad.

fstAnn :: (a :@ b) -> a
fstAnn (a :@ b) = a

sndAnn :: (a :@ b) -> b
sndAnn (a :@ b) = b


-------------
-- Recursion into DMTypes
--
recDMTypeM :: forall m k. (Monad m)
           => (forall k. DMTypeOf k -> m (DMTypeOf k)) 
           -> (Sensitivity -> m (Sensitivity)) 
           -> DMTypeOf k -> m (DMTypeOf k)
recDMTypeM typemap sensmap DMAny = pure DMAny
recDMTypeM typemap sensmap L1 = pure L1
recDMTypeM typemap sensmap L2 = pure L2
recDMTypeM typemap sensmap LInf = pure LInf
recDMTypeM typemap sensmap U = pure U
recDMTypeM typemap sensmap Vector = pure Vector
recDMTypeM typemap sensmap Gradient = pure Gradient
recDMTypeM typemap sensmap (Matrix n) = Matrix <$> sensmap n
recDMTypeM typemap sensmap (Clip n) = Clip <$> typemap n
recDMTypeM typemap sensmap DMInt = pure DMInt
recDMTypeM typemap sensmap DMReal = pure DMReal
recDMTypeM typemap sensmap DMData = pure DMData
recDMTypeM typemap sensmap (Numeric τ) = Numeric <$> typemap τ
recDMTypeM typemap sensmap (NonConst τ) = NonConst <$> typemap τ
recDMTypeM typemap sensmap (Const η τ) = Const <$> sensmap η <*> typemap τ
recDMTypeM typemap sensmap (TVar x) = pure (TVar x)
recDMTypeM typemap sensmap (τ1 :->: τ2) = (:->:) <$> mapM (\(a :@ b) -> (:@) <$> typemap a <*> sensmap b) τ1 <*> typemap τ2
recDMTypeM typemap sensmap (τ1 :->*: τ2) = (:->*:) <$> mapM (\(a :@ (b0, b1)) -> f <$> typemap a <*> sensmap b0 <*> sensmap b1) τ1 <*> typemap τ2
  where
    f a b0 b1 = a :@ (b0, b1)
recDMTypeM typemap sensmap (DMTup τs) = DMTup <$> mapM typemap τs
recDMTypeM typemap sensmap (DMContainer k nrm clp n τ) = DMContainer <$> typemap k <*> typemap nrm <*> typemap clp <*> sensmap n <*> typemap τ
--recDMTypeM typemap sensmap (DMMat nrm clp n m τ) = DMMat <$> typemap nrm <*> typemap clp <*> sensmap n <*> sensmap m <*> typemap τ
recDMTypeM typemap sensmap (DMModel m τ) = DMModel <$> sensmap m <*> typemap τ
recDMTypeM typemap sensmap (NoFun x) = NoFun <$> typemap x
recDMTypeM typemap sensmap (Fun xs) = Fun <$> mapM (\(a :@ b) -> (:@) <$> typemap a <*> pure b) xs
recDMTypeM typemap sensmap (x :∧: y) = (:∧:) <$> typemap x <*> typemap y
recDMTypeM typemap sensmap (BlackBox n) = pure (BlackBox n)
recDMTypeM typemap sensmap (Deepcopied n) = Deepcopied <$> typemap n

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


---------------------------------------------------------
-- Julia types
-- 
-- An almost one-to-one representation of all supported julia types, with the exception of JTBot which does not
-- exist in julia and is set to be a julia-subtype of all other JuliaTypes as defined in Typecheck/JuliaTypes.jl

data JuliaType =
    JTAny
    | JTBot
    | JTInt
    | JTReal
    | JTFunction
    | JTPFunction
    | JTTuple [JuliaType]
    | JTVector JuliaType
    | JTMatrix JuliaType
    | JTModel
    | JTGrads
  deriving (Generic, Eq, Ord)

instance Hashable JuliaType where

-- this is used for callbacks to actual julia, so the string representation matches julia exactly.
instance Show JuliaType where
  show JTAny = "Any"
  show JTInt = "Integer"
  show JTReal = "Real"
  show JTFunction = "Function"
  show JTPFunction = "PrivacyFunction"
  show (JTTuple as) = "Tuple{" ++ (intercalate "," (show <$> as)) ++ "}"
  show (JTVector t) = "Vector{" ++ show t ++ "}"
  show (JTMatrix t) = "Matrix{" ++ show t ++ "}"
  show (JTModel) = "DMModel"
  show (JTGrads) = "DMGrads"
  show (JTBot) = "Bot"


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
     Unary DMTypeOps_Unary   (DMType :@ SVar) (DMType)
   | Binary DMTypeOps_Binary (DMType :@ SVar , DMType :@ SVar) (DMType)
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

data Asgmt a = (:-) (Maybe TeVar) a
  deriving (Generic, Show, Eq, Ord)

fstA :: Asgmt a -> Maybe TeVar
fstA (x :- τ) = x

sndA :: Asgmt a -> a
sndA (x :- τ) = τ

-- data Lam_ = Lam_ [Asgmt JuliaType] DMTerm
--   deriving (Generic, Show)

data LetKind = PureLet | BindLet | LoopLet | SampleLet
  deriving (Eq, Show)


data PreDMTerm (t :: * -> *) =
    Extra (t (PreDMTerm t))
  | Ret ((PreDMTerm t))
  | Sng Float JuliaType
  | Var (Asgmt JuliaType)
--  | Rnd JuliaType
  | Arg TeVar JuliaType Relevance
  | Op DMTypeOp_Some [(PreDMTerm t)]
  | Phi (PreDMTerm t) (PreDMTerm t) (PreDMTerm t)
  | Lam     [Asgmt JuliaType] (PreDMTerm t)
  | LamStar [(Asgmt (JuliaType, Relevance))] (PreDMTerm t)
  | BBLet TeVar [JuliaType] (PreDMTerm t) -- name, arguments, tail
  | BBApply (PreDMTerm t) [(PreDMTerm t)] [TeVar] -- term containing the application, list of captured variables.
  | Apply (PreDMTerm t) [(PreDMTerm t)]
  | FLet TeVar (PreDMTerm t) (PreDMTerm t)
  | Choice (HashMap [JuliaType] (PreDMTerm t))
  | SLetBase LetKind (Asgmt JuliaType) (PreDMTerm t) (PreDMTerm t)
  | Tup [(PreDMTerm t)]
  | TLetBase LetKind [(Asgmt JuliaType)] (PreDMTerm t) (PreDMTerm t)
  | Gauss (PreDMTerm t) (PreDMTerm t) (PreDMTerm t) (PreDMTerm t)
  | Laplace (PreDMTerm t) (PreDMTerm t) (PreDMTerm t)
  | AboveThresh (PreDMTerm t) (PreDMTerm t) (PreDMTerm t) (PreDMTerm t)
  | MutGauss (PreDMTerm t) (PreDMTerm t) (PreDMTerm t) (PreDMTerm t)
  | MutLaplace (PreDMTerm t) (PreDMTerm t) (PreDMTerm t)
-- matrix related things
  | MMap (PreDMTerm t) (PreDMTerm t)
  | ConvertM (PreDMTerm t)
  | MCreate (PreDMTerm t) (PreDMTerm t) (TeVar, TeVar) (PreDMTerm t)
  | Transpose (PreDMTerm t)
  | Size (PreDMTerm t) -- matrix dimensions, returns a tuple of two numbers
  | Length (PreDMTerm t) -- vector dimension, returns a number
  | Index (PreDMTerm t) (PreDMTerm t) (PreDMTerm t) -- matrix index
  | VIndex (PreDMTerm t) (PreDMTerm t) -- vector index
  | Row (PreDMTerm t) (PreDMTerm t) -- matrix row
  | ClipM Clip (PreDMTerm t)
  | MutClipM Clip (PreDMTerm t)
  -- Loop (DMTerm : "Number of iterations") ([TeVar] : "Captured variables") (TeVar : "name of iteration var", TeVar : "name of capture variable") (DMTerm : "body")
  | Loop (PreDMTerm t) [TeVar] (Maybe TeVar, TeVar) (PreDMTerm t)
-- Special NN builtins
  | SubGrad (PreDMTerm t) (PreDMTerm t)
  | ScaleGrad (PreDMTerm t) (PreDMTerm t) -- scale (a : Scalar) (g : Mutating Gradient)
-- Special Tuple terms
  | Reorder [Int] (PreDMTerm t)
  | TProject Int (PreDMTerm t)
-- Special Scope terms
  | LastTerm (PreDMTerm t)
  | ZeroGrad (PreDMTerm t)
  | SumGrads (PreDMTerm t) (PreDMTerm t)
  | Sample (PreDMTerm t) (PreDMTerm t) (PreDMTerm t)
-- Internal terms
  | InternalExpectConst (PreDMTerm t)
-- Demutation related, but user specified
  | DeepcopyValue (PreDMTerm t)
  deriving (Generic)

pattern SLet a b c = SLetBase PureLet a b c
pattern SBind a b c = SLetBase BindLet a b c
pattern TLet a b c = TLetBase PureLet a b c
pattern TBind a b c = TLetBase BindLet a b c
pattern SmpLet a b c = TLetBase SampleLet a b c

{-# COMPLETE Extra, Ret, Sng, Var, Arg, Op, Phi, Lam, LamStar, BBLet, BBApply,
 Apply, FLet, Choice, SLet, SBind, Tup, TLet, TBind, Gauss, Laplace, MutGauss, MutLaplace, AboveThresh, MMap, ConvertM, MCreate, Transpose,
 Size, Length, Index, VIndex, Row, ClipM, MutClipM, Loop, SubGrad, ScaleGrad, Reorder, TProject, LastTerm,
 ZeroGrad, SumGrads, SmpLet, Sample, InternalExpectConst #-}


deriving instance (forall a. Show a => Show (t a)) => Show (PreDMTerm t)
deriving instance (forall a. Eq a => Eq (t a)) => Eq (PreDMTerm t)


--------------------------------------------------------------------------
-- Extensions

-----
-- empty extension
data EmptyExtension a where
 deriving (Functor, Foldable, Traversable)

instance Show (EmptyExtension a) where
  show a = undefined

instance Eq (EmptyExtension a) where
  _ == _ = True

type DMTerm = PreDMTerm EmptyExtension



type ProcDMTerm = PreDMTerm ProceduralExtension

data ProceduralExtension a =
  ProcTLetBase LetKind [(Asgmt JuliaType)] a
  | ProcSLetBase LetKind (Asgmt JuliaType) a
  | ProcFLet TeVar a
  | ProcBBLet TeVar [JuliaType] -- name, arguments
  | ProcPhi a [a]
  | ProcPreLoop a (Maybe TeVar) a
  | ProcLoop a [TeVar] (Maybe TeVar, TeVar) a
  | Block [a]


----
-- mutability extension
data MutabilityExtension a =
  MutLet LetKind a a
  -- MutLoop (a : "Number of iterations") (TeVar : "name of iteration var") (a : "body")
  | MutLoop a (Maybe TeVar) a
  | MutPhi a [a] a
  | DNothing
  | MutRet -- we return all mutated variables
  | LoopRet [TeVar] -- we return all mutated, and all capture variables in the list
  | DefaultRet a
  deriving (Show, Eq, Functor, Foldable, Traversable)

type MutDMTerm = PreDMTerm MutabilityExtension

----
-- sum of extensions
data SumExtension e f a = SELeft (e a) | SERight (f a)
  deriving (Show, Eq, Functor, Foldable, Traversable)

----
-- functions

liftExtension :: (t (PreDMTerm t) -> PreDMTerm s) -> PreDMTerm t -> PreDMTerm s
liftExtension f x = runIdentity $ recDMTermM (Identity . liftExtension f) (Identity . f) (x)

-- recursing into a dmterm
recDMTermSameExtension :: forall t. (Traversable t) => (PreDMTerm t -> (PreDMTerm t)) -> PreDMTerm t -> (PreDMTerm t)
recDMTermSameExtension f x = runIdentity (recDMTermMSameExtension (Identity . f) x)

recDMTermMSameExtension :: forall t m. (Monad m, Traversable t) => (PreDMTerm t -> m (PreDMTerm t)) -> PreDMTerm t -> m (PreDMTerm t)
recDMTermMSameExtension f t = recDMTermM f g t
  where
    g :: t (PreDMTerm t) -> m (PreDMTerm t)
    g x =
      let x' :: t (m (PreDMTerm t))
          x' = fmap (recDMTermMSameExtension f) x
          x'' :: m (t (PreDMTerm t))
          x'' = sequence x'
      in fmap Extra x''


recDMTermM :: forall t m s. (Monad m) => (PreDMTerm t -> m (PreDMTerm s)) -> (t (PreDMTerm t) -> m (PreDMTerm s)) -> PreDMTerm t -> m (PreDMTerm s)
recDMTermM f h (Extra e)          = h e
recDMTermM f h (Ret (r))          = Ret <$> (f r)
recDMTermM f h (Sng g jt)         = pure $ Sng g jt
recDMTermM f h (Var (v :- jt))    = pure $ Var (v :- jt)
-- recDMTermM f h (Rnd jt)           = pure $ Rnd jt
recDMTermM f h (Arg v jt r)       = pure $ Arg v jt r
recDMTermM f h (Op op ts)         = Op op <$> (mapM (f) ts)
recDMTermM f h (Phi a b c)        = Phi <$> (f a) <*> (f b) <*> (f c)
recDMTermM f h (Lam     jts a)    = Lam jts <$> (f a)
recDMTermM f h (LamStar jts a)    = LamStar jts <$> (f a)
recDMTermM f h (BBLet n jts b)    = (BBLet n jts <$> f b)
recDMTermM f h (BBApply a as bs)  = BBApply <$> (f a) <*> (mapM (f) as) <*> pure bs
recDMTermM f h (Apply a bs)       = Apply <$> (f a) <*> (mapM (f) bs)
recDMTermM f h (FLet v a b)       = FLet v <$> (f a) <*> (f b)
recDMTermM f h (Choice chs)       = Choice <$> (mapM (f) chs)
recDMTermM f h (SLetBase x jt a b) = SLetBase x jt <$> (f a) <*> (f b)
recDMTermM f h (Tup as)           = Tup <$> (mapM (f) as)
recDMTermM f h (TLetBase x jt a b) = TLetBase x jt <$> (f a) <*> (f b)
recDMTermM f h (Gauss a b c d)    = Gauss <$> (f a) <*> (f b) <*> (f c) <*> (f d)
recDMTermM f h (AboveThresh a b c d)    = AboveThresh <$> (f a) <*> (f b) <*> (f c) <*> (f d)
recDMTermM f h (Laplace a b c)    = Laplace <$> (f a) <*> (f b) <*> (f c)
recDMTermM f h (MutGauss a b c d) = MutGauss <$> (f a) <*> (f b) <*> (f c) <*> (f d)
recDMTermM f h (MutLaplace a b c) = MutLaplace <$> (f a) <*> (f b) <*> (f c)
recDMTermM f h (MMap a b)         = MMap <$> (f a) <*> (f b)
recDMTermM f h (ConvertM a)       = ConvertM <$> (f a)
recDMTermM f h (MCreate a b x c ) = MCreate <$> (f a) <*> (f b) <*> pure x <*> (f c)
recDMTermM f h (Transpose a)      = Transpose <$> (f a)
recDMTermM f h (Size a)           = Size <$> (f a)
recDMTermM f h (Length a)         = Length <$> (f a)
recDMTermM f h (Index a b c)      = Index <$> (f a) <*> (f b) <*> (f c)
recDMTermM f h (VIndex a b)       = VIndex <$> (f a) <*> (f b)
recDMTermM f h (Row a b)          = Row <$> (f a) <*> (f b)
recDMTermM f h (ClipM c a)        = ClipM c <$> (f a)
recDMTermM f h (MutClipM c a)     = MutClipM c <$> (f a)
recDMTermM f h (Loop a b x d )    = Loop <$> (f a) <*> pure b <*> pure x <*> (f d)
recDMTermM f h (SubGrad a b)      = SubGrad <$> (f a) <*> (f b)
recDMTermM f h (ScaleGrad a b)    = ScaleGrad <$> (f a) <*> (f b)
recDMTermM f h (Reorder x a)      = Reorder x <$> (f a)
recDMTermM f h (TProject x a)     = TProject x <$> f a
recDMTermM f h (LastTerm x)       = LastTerm <$> (f x)
recDMTermM f h (ZeroGrad a)       = ZeroGrad <$> (f a)
recDMTermM f h (SumGrads a b)     = SumGrads <$> (f a) <*> (f b)
recDMTermM f h (Sample a b c)     = Sample <$> (f a) <*> (f b) <*> (f c)
recDMTermM f h (DeepcopyValue t) = DeepcopyValue <$> (f t)
recDMTermM f h (InternalExpectConst a) = InternalExpectConst <$> (f a)

--------------------------------------------------------------------------
-- Free variables for terms

freeVarsDMTerm :: DMTerm -> [TeVar]
freeVarsDMTerm (Var (Just v  :- jt)) = [v]
freeVarsDMTerm (Var (Nothing :- jt)) = []
freeVarsDMTerm (Lam jts body) = freeVarsDMTerm body \\ [v | (Just v :- _) <- jts]
freeVarsDMTerm (LamStar jts body) = freeVarsDMTerm body \\ [v | (Just v :- _) <- jts]
freeVarsDMTerm t = fst $ recDMTermMSameExtension f t
  where
    f :: DMTerm -> ([TeVar] , DMTerm)
    f = (\a -> (freeVarsDMTerm a, a))

--------------------------------------------------------------------------
-- pretty printing

class ShowPretty a where
  showPretty :: a -> String

instance ShowPretty a => ShowPretty [a] where
  showPretty as = "[" <> intercalate ", " (fmap showPretty as) <> "]"

newlineIndentIfLong :: String -> String
newlineIndentIfLong xs = case '\n' `elem` xs of
  False -> xs
  True -> "\n" <> justIndent xs

parenIndent :: String -> String
parenIndent s = "\n(\n" <> unlines (fmap ("  " <>) (lines s)) <> ")"

justIndent :: String -> String
justIndent s = unlines (fmap ("  " <>) (lines s))

indent :: String -> String
indent s = unlines (fmap ("  " <>) (lines s))

instance ShowPretty (TeVar) where
  showPretty (v) = show v

instance ShowPretty a => ShowPretty (Asgmt a) where
  showPretty (Nothing :- x) = "_ :- " <> showPretty x
  showPretty (Just a :- x) = showPretty a <> " :- " <> showPretty x

instance ShowPretty (DMTypeOp_Some) where
  showPretty (IsBinary op) = show op
  showPretty (IsUnary op) = show op

instance ShowPretty (JuliaType) where
  showPretty = show

instance (ShowPretty a, ShowPretty b) => ShowPretty (a,b) where
  showPretty (a,b) = "("<> showPretty a <> ", " <> showPretty b <> ")"

instance ShowPretty Relevance where
  showPretty = show


instance (forall a. ShowPretty a => ShowPretty (t a)) => ShowPretty (PreDMTerm t) where
  showPretty (Extra e)          = showPretty e
  showPretty (Ret (r))          = "Ret (" <>  showPretty r <> ")"
  showPretty (Sng g jt)         = show g
  showPretty (Var (v :- jt))    = case v of
                                    Nothing -> "_"
                                    Just tv -> show tv
--  showPretty (Rnd jt)           = "Rnd"
  showPretty (Arg v jt r)       = show v
  showPretty (Op op ts)         = showPretty op <> " " <> showPretty ts
  showPretty (Phi a b c)        = "Phi (" <> showPretty a <> ")" <> parenIndent (showPretty b) <> parenIndent (showPretty c)
  showPretty (Lam     jts a)    = "Lam (" <> showPretty jts <> ")" <> parenIndent (showPretty a)
  showPretty (LamStar jts a)    = "LamStar (" <> showPretty jts <> ")" <> parenIndent (showPretty a)
  showPretty (BBLet n jts b)    = "BBLet " <> showPretty n <> " = (" <> show jts <> " -> ?)\n" <> showPretty b
  showPretty (BBApply t as cs)  = "BBApply (" <> showPretty t <> ")[" <> showPretty cs <> "](" <> showPretty as <> ")"
  showPretty (Apply a bs)       = (showPretty a) <> (showPretty bs)
  showPretty (FLet v a b)       = "FLet " <> showPretty v <> " = " <> newlineIndentIfLong (showPretty a) <> "\n" <> (showPretty b)
  showPretty (Choice chs)       = "Choice <..>"
  showPretty (SLet v a b)       = "SLet " <> showPretty v <> " = " <> newlineIndentIfLong (showPretty a) <> "\n" <> (showPretty b)
  showPretty (Tup as)           = "Tup " <> (showPretty as)
  showPretty (TLet v a b)       = "TLet " <> showPretty v <> " = " <> newlineIndentIfLong (showPretty a) <> "\n" <> (showPretty b)
  showPretty (TBind v a b)      = "TBind " <> showPretty v <> " <- " <> newlineIndentIfLong (showPretty a) <> "\n" <> (showPretty b)
  showPretty (Gauss a b c d)    = "Gauss (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ", " <> (showPretty d) <> ")"
  showPretty (AboveThresh a b c d) = "AboveThresh (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ", " <> (showPretty d) <> ")"
  showPretty (MutLaplace a b c) = "MutLaplace (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ")"
  showPretty (MutGauss a b c d) = "MutGauss (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ", " <> (showPretty d) <> ")"
  showPretty (Laplace a b c)    = "Laplace (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ")"
  showPretty (MMap a b)         = "MMap (" <> (showPretty a) <> " to " <> (showPretty b)  <> ")"
  showPretty (ConvertM a)       = "ConvertM (" <> (showPretty a) <> ")"
  showPretty (MCreate a b x c ) = "MCreate (" <> (showPretty a) <> ", " <> (showPretty b)  <> ", " <> show x <> ", " <> (showPretty c) <> ")"
  showPretty (Transpose a)      = "Transpose (" <> (showPretty a) <> ")"
  showPretty (Size a)           = "Size (" <> (showPretty a) <> ")"
  showPretty (Length a)         = "Length (" <> (showPretty a) <> ")"
  showPretty (Index a b c)      = "Index (" <> (showPretty a) <> ", " <> (showPretty b)  <> ", " <> (showPretty c) <> ")"
  showPretty (VIndex a b)       = "VIndex (" <> (showPretty a) <> ", " <> (showPretty b)  <> ")"
  showPretty (Row a b)          = "Row (" <> (showPretty a) <> ", " <> (showPretty b) <> ")"
  showPretty (ClipM c a)        = "ClipM (" <> show c <> ", " <> (showPretty a) <> ")"
  showPretty (MutClipM c a)     = "MutClipM (" <> show c <> ", " <> (showPretty a) <> ")"
  showPretty (SubGrad a b)      = "SubGrad (" <> (showPretty a) <> ", " <> (showPretty b) <>  ")"
  showPretty (ScaleGrad a b)    = "ScaleGrad (" <> (showPretty a) <> ", " <> (showPretty b) <>  ")"
  showPretty (Reorder x a)      = "Reorder " <> show x <> parenIndent (showPretty a)
  showPretty (TProject x a)     = "Proj" <> show x <> " " <>  (showPretty a)
  showPretty (Loop a b x d )    = "Loop (" <> (showPretty a) <> ", " <> (showPretty b)  <> ", " <> show x <> ")" <> parenIndent (showPretty d)
  showPretty (SBind x a b)      = "SBind " <> showPretty x <> " <- " <> newlineIndentIfLong (showPretty a) <> "\n" <> (showPretty b)
  showPretty (LastTerm a)       = "LastTerm " <> (showPretty a)
  showPretty (ZeroGrad a)       = "ZeroGrad " <> (showPretty a)
  showPretty (SumGrads a b)     = "SumGrads (" <> (showPretty a) <> ", " <> (showPretty b) <> ")"
  showPretty (SmpLet v a b)     = "SmpLet " <> showPretty v <> " <- " <> (showPretty a) <> "\n" <> (showPretty b)
  showPretty (Sample a b c)     = "Sample (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ")"
  showPretty (DeepcopyValue a)  = "(Copy " <> showPretty a <> ")"
  showPretty (InternalExpectConst a) = "InternalExpectConst " <> (showPretty a)

instance ShowPretty a => ShowPretty (MutabilityExtension a) where
  showPretty (DNothing)      = "Nothing"
  showPretty (MutPhi a b c)    = "MutPhi (" <> showPretty a <> " ? " <> showPretty b <> " in " <> showPretty c <> ")"
  showPretty (MutLet t a b)  = "MutLet{" <> show t <> "} " <> indent (showPretty a) <> indent (showPretty b)
  showPretty (MutLoop a x d) = "MutLoop (" <> (showPretty a) <> ", " <> show x <> ")" <> parenIndent (showPretty d)
  showPretty (MutRet)        = "MutRet"
  showPretty (LoopRet as)    = "LoopRet " <> showPretty as
  showPretty (DefaultRet x)  = "DefaultRet (" <> showPretty x <> ")"

instance ShowPretty (EmptyExtension a) where
  showPretty a = undefined



--------------------------------------------------------------------------
-- DMException
--
-- The different kinds of errors we can throw.

data DMException where
  UnsupportedError        :: String -> DMException
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
  DemutationError         :: String -> DMException
  DemutationDefinitionOrderError :: Show a => a -> DMException
  DemutationVariableAccessTypeError :: String -> DMException
  BlackBoxError           :: String -> DMException
  FLetReorderError        :: String -> DMException
  UnificationShouldWaitError :: DMTypeOf k -> DMTypeOf k -> DMException
  TermColorError          :: AnnotationKind -> DMTerm -> DMException
  ParseError              :: String -> String -> Int -> DMException -- error message, filename, line number
  DemutationMovedVariableAccessError :: Show a => a -> DMException
  DemutationNonAliasedMutatingArgumentError :: String -> DMException

instance Show DMException where
  show (UnsupportedError t) = "The term '" <> t <> "' is currently not supported."
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
  show (UnificationShouldWaitError a b) = "Trying to unify types " <> show a <> " and " <> show b <> " with unresolved infimum (∧)."
  show (DemutationError e) = "While demutating, the following error was encountered:\n " <> e
  show (BlackBoxError e) = "While preprocessing black boxes, the following error was encountered:\n " <> e
  show (FLetReorderError e) = "While processing function signatures, the following error was encountered:\n " <> e
  show (ParseError e file line) = "Unsupported julia expression in file " <> file <> ", line " <> show line <> ":\n " <> e
  show (TermColorError color t) = "Expected " <> show t <> " to be a " <> show color <> " expression but it is not."
  show (DemutationDefinitionOrderError a) = "The variable '" <> show a <> "' has not been defined before being used.\n"
                                            <> "Note that currently every variable has to be assigned some value prior to its usage.\n"
                                            <> "Here, 'prior to usage' means literally earlier in the code.\n"
                                            <> "The actual value of that assignment is irrelevant, e.g., the first line of the following code is only there to fix the error which is currently shown:\n"
                                            <> ">  a = 0" <> "\n"
                                            <> ">  function f()" <> "\n"
                                            <> ">    a" <> "\n"
                                            <> ">  end" <> "\n"
                                            <> ">  a = 3" <> "\n"
                                            <> ">  f()" <> "\n"
  show (DemutationVariableAccessTypeError e) = "An error regarding variable access types occured:\n" <> e
  show (DemutationMovedVariableAccessError a) = "Tried to access the variable " <> show a <> ". But this variable is not valid anymore, because it was assigned to something else."
  show (DemutationNonAliasedMutatingArgumentError a) = "An error regarding non-aliasing of mutating arguments occured:\n" <> a

instance Eq DMException where
  UnsupportedTermError    a        == UnsupportedTermError    b       = True
  UnificationError        a a2     == UnificationError        b b2    = True
  WrongNumberOfArgs       a a2     == WrongNumberOfArgs       b b2    = True
  WrongNumberOfArgsOp     a a2     == WrongNumberOfArgsOp     b b2    = True
  ImpossibleError         a        == ImpossibleError         b       = True
  InternalError           a        == InternalError           b       = True
  VariableNotInScope      a        == VariableNotInScope      b       = True
  UnsatisfiableConstraint a        == UnsatisfiableConstraint b       = True
  TypeMismatchError       a        == TypeMismatchError       b       = True
  NoChoiceFoundError      a        == NoChoiceFoundError      b       = True
  UnificationShouldWaitError a a2  == UnificationShouldWaitError b b2 = True
  ParseError e1 file1 line1        == ParseError e2 file2 line2       = True
  FLetReorderError        a        == FLetReorderError        b       = True
  TermColorError      a b          == TermColorError c d              = True
  DemutationError a                == DemutationError         b       = True
  DemutationDefinitionOrderError a == DemutationDefinitionOrderError b = True
  DemutationVariableAccessTypeError a == DemutationVariableAccessTypeError b = True
  DemutationMovedVariableAccessError a       == DemutationMovedVariableAccessError b = True
  DemutationNonAliasedMutatingArgumentError a       == DemutationNonAliasedMutatingArgumentError b = True
  _ == _ = False







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

data WithRelev extra = WithRelev Relevance (DMTypeOf MainKind :@ Annotation extra)


instance Semigroup Relevance where
  (<>) IsRelevant b = IsRelevant
  (<>) a IsRelevant = IsRelevant
  (<>) _ _ = NotRelevant

instance Show (WithRelev e) where
  show (WithRelev IsRelevant  x) = show x
  show (WithRelev NotRelevant x) = "{" <> show x <> "}"

makeRelev :: (DMTypeOf MainKind :@ Annotation e) -> WithRelev e
makeRelev = WithRelev IsRelevant

makeNotRelev :: (DMTypeOf MainKind :@ Annotation e) -> WithRelev e
makeNotRelev = WithRelev NotRelevant
