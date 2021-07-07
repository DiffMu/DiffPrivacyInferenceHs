
module DiffMu.Core.Unification where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.TC

import DiffMu.Core.Symbolic

import Data.HashMap.Strict as H

-------------------------------------------------------------------
-- Unification of dmtypes
--

instance Monad t => Normalize t JuliaType where
  normalize = pure



instance Unify MonadDMTC JuliaType where
  unify_ (JuliaType a) (JuliaType b) | a == b = pure (JuliaType a)
  unify_ t s = throwError (UnificationError t s)


instance Unify MonadDMTC (Annotation e) where
  -- NOTE: we can use the unify_ (with underscore) function here,
  -- because we do not have to normalize the just normalized arguments
  unify_ (SensitivityAnnotation s) (SensitivityAnnotation t) = SensitivityAnnotation <$> unify_ s t
  unify_ (PrivacyAnnotation s) (PrivacyAnnotation t) = PrivacyAnnotation <$> unify_ s t

-- TODO: Check, is i <> j what we want to do here?
-- instance Unify MonadDMTC e => Unify MonadDMTC (WithRelev e) where
--   unify_ (WithRelev i e) (WithRelev j f)  = WithRelev (i <> j) <$> unify_ e f

instance Unify MonadDMTC (WithRelev e) where
  unify_ (WithRelev i e) (WithRelev j f)  = WithRelev (i <> j) <$> unify_ e f

-- Unification of DMTypes (of any kind k) is given by:
instance Unify MonadDMTC (DMTypeOf k) where
  unify_ Deleted a                     = internalError "A deleted variable reappeared and tried to escape via unification."
  unify_ a Deleted                     = internalError "A deleted variable reappeared and tried to escape via unification."
  unify_ DMReal DMReal                 = pure DMReal
  unify_ DMInt DMInt                   = pure DMInt
  unify_ DMData DMData                 = pure DMData
  unify_ (Numeric t) (Numeric s)       = Numeric <$> unify t s
  unify_ (NonConst τ₁) (NonConst τ₂)   = NonConst <$> unify τ₁ τ₂
  unify_ (Const η₁ τ₁) (Const η₂ τ₂)   = Const <$> unify η₁ η₂ <*> unify τ₁ τ₂
  unify_ (as :->: a) (bs :->: b)       = (:->:) <$> unify as bs <*> unify a b
  unify_ (as :->*: a) (bs :->*: b)     = (:->*:) <$> unify as bs <*> unify a b
  unify_ (DMTup as) (DMTup bs)         = DMTup <$> unify as bs
  unify_ (TVar x) (TVar y) | x == y    = pure $ TVar x
  unify_ (TVar x) t                    = addSub (x := t) >> pure t
  unify_ t (TVar x)                    = addSub (x := t) >> pure t
  unify_ L1 L1                         = pure L1
  unify_ L2 L2                         = pure L2
  unify_ LInf LInf                     = pure LInf
  unify_ U U                           = pure U
  unify_ (Clip k) (Clip s)             = Clip <$> unify k s
  unify_ (DMMat nrm1 clp1 n1 m1 τ1) (DMMat nrm2 clp2 n2 m2 τ2) =
     DMMat <$> unify nrm1 nrm2 <*> unify clp1 clp2 <*> unify n1 n2 <*> unify m1 m2 <*> unify τ1 τ2
  unify_ (NoFun x) (NoFun y)              = NoFun <$> unify x y
  unify_ (Fun xs) (Fun ys)                = Fun <$> unify xs ys
  unify_ (x :∧: y) (v :∧: w)              = undefined
  unify_ (ForAll xs t) (ForAll ys s)      =
    -- NOTE: we actually have to remove all variables which were substituted
    --       from the merged list (xs <> ys). But luckily this is done
    --       automatically by the definition of substitution, and will happen
    --       when the returned type is being normalized
    --
    ForAll (xs <> ys) <$> unify t s
  unify_ t s                              = throwError (UnificationError t s)

-- Above we implictly use unification of terms of the type (a :& b).
-- These are unified entry-wise:
instance (Unify isT a, Unify isT b) => Unify isT (a :& b) where
  unify_ (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unify_ a₁ a₂ <*> unify_ e₁ e₂

-- Similarly, lists of terms are unified elements wise,
-- but they only match if they are of the same lenght:
instance (Show a, Unify MonadDMTC a) => Unify MonadDMTC [a] where
  unify_ xs ys | length xs == length ys = mapM (uncurry unify_) (zip xs ys)
  unify_ xs ys = throwError (UnificationError xs ys)

instance Typeable k => FixedVars TVarOf (IsEqual (DMTypeOf k, DMTypeOf k)) where
  fixedVars _ = mempty

-- Using the unification instance, we implement solving of the `IsEqual` constraint for DMTypes.
instance Solve MonadDMTC IsEqual (DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ name (IsEqual (a,b)) = unify_ a b >> dischargeConstraint name



solveLessEqualSensitivity :: Sensitivity -> Sensitivity -> Maybe Bool
solveLessEqualSensitivity (SingleKinded (LinCom (MonCom as))) (SingleKinded (LinCom (MonCom bs))) = case (H.toList as, H.toList bs) of
  ([(MonCom a,av)],[(MonCom b, bv)]) -> case (H.toList a, H.toList b) of
    ([],[]) -> Just (av <= bv)
    _ -> Nothing
  _ -> Nothing

instance Solve MonadDMTC IsLessEqual (Sensitivity, Sensitivity) where
  solve_ Dict _ name (IsLessEqual (s1, s2)) = case solveLessEqualSensitivity s1 s2 of
    Just True -> dischargeConstraint name
    Just False -> failConstraint name
    Nothing -> return ()

-------------------------------------------------------------------
-- Monadic monoid structure on dmtypes
--

-- new monoid structure using infimum

instance (IsT MonadDMTC t) => SemigroupM (t) (DMTypeOf MainKind) where
  (⋆) x y = return (x :∧: y)

instance (IsT MonadDMTC t) => MonoidM (t) (DMTypeOf MainKind) where
  neutral = newVar


-- An optimized check for whether a given DMType is a neutral does not create new typevariables,
-- but simply checks if the given DMType is one.
instance (SingI k, Typeable k, IsT MonadDMTC t) => (CheckNeutral (t) (DMTypeOf k)) where
  checkNeutral (TVar x) = return True
  checkNeutral (_) = return False

-- Old semigroup structure by unification
{-
-- We define a monadic semigroup structure on `DMTypeOf k`,
-- which is simply unification.
instance (IsT MonadDMTC t) => SemigroupM (t) (DMTypeOf k) where
  (⋆) = unify

-- This is even a monadic monoid, with the neutral element given by a new type variable.
instance (SingI k, Typeable k, IsT MonadDMTC t) => MonoidM (t) (DMTypeOf k) where
  neutral = TVar <$> newTVar ""

-- An optimized check for whether a given DMType is a neutral does not create new typevariables,
-- but simply checks if the given DMType is one.
instance (SingI k, Typeable k, IsT MonadDMTC t) => (CheckNeutral (t) (DMTypeOf k)) where
  checkNeutral (TVar x) = return True
  checkNeutral (_) = return False
-}


