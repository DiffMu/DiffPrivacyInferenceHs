

module DiffMu.Typecheck.Constraint.IsJuliaEqual where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Unification

import Debug.Trace

import Prelude as P


-----------------------------------------------------------------
-- Fake julia types
--
-- We do not have a real "julia type layer" for now. Since our types
-- mostly only differ from the julia types by having the singleton const types,
-- we have a constraint which checks this by unifying after making variables non-const
-- if possible.


-- defining the constraint
newtype IsJuliaEqual a = IsJuliaEqual a deriving Show

instance TCConstraint IsJuliaEqual where
  constr = IsJuliaEqual
  runConstr (IsJuliaEqual c) = c


makeNonConst_JuliaVersion ::  DMTypeOf k -> DMTypeOf k
makeNonConst_JuliaVersion (TVar a) = TVar a
makeNonConst_JuliaVersion (Const _ a) = NonConst a
makeNonConst_JuliaVersion (NonConst a) = NonConst a
makeNonConst_JuliaVersion (NoFun a) = NoFun (makeNonConst_JuliaVersion a)
makeNonConst_JuliaVersion (DMTup as) = DMTup (makeNonConst_JuliaVersion <$> as)
makeNonConst_JuliaVersion (Numeric a) = Numeric (makeNonConst_JuliaVersion a)
-- everything else is not changed
makeNonConst_JuliaVersion x = x

solveJuliaEqual :: (IsT MonadDMTC t) => Symbol -> DMMain -> DMMain -> t ()
solveJuliaEqual name (NoFun a) (NoFun b) = do
  -- we compute the free variables in the type which are of NumKind
  -- these are the once which block this constraint, since they have
  -- to be resolved to Const/NonConst, before we can apply the `makeNonConst_JuliaVersion`
  -- on `a` and `b`
  let freev = freeVars @_ @TVarOf a <> freeVars b
      freev0 = (filterSomeK @TVarOf @BaseNumKind freev)
      freev1 = filterSomeK @TVarOf @NormKind freev
      freev2 = filterSomeK @TVarOf @ClipKind freev

      -- compare the length of `m` and `n`, that is, if all free variables
      -- have the aforementioned kinds
      m = length freev
      n = length freev0 P.+ length freev1 P.+ length freev2

  case (m == n) of
    True -> do let a' = makeNonConst_JuliaVersion a
                   b' = makeNonConst_JuliaVersion b
               unify a' b'
               dischargeConstraint name
    False -> return()

solveJuliaEqual name (TVar _) _   = return ()
solveJuliaEqual name (_) (TVar _) = return ()
solveJuliaEqual name (_) (_ :∧: _) = return ()
solveJuliaEqual name (_ :∧: _) (_) = return ()
solveJuliaEqual name _ _ = failConstraint name



-- solving it
instance Solve MonadDMTC IsJuliaEqual (DMMain, DMMain) where
  solve_ Dict _ name (IsJuliaEqual (a,b)) = solveJuliaEqual name a b

instance FixedVars TVarOf (IsJuliaEqual (DMMain, DMMain)) where
  fixedVars _ = mempty


-------------------------------------------------------------------
-- set the a type to non-const, in case it's numeric or a tuple.
--

newtype IsNonConst a = IsNonConst a deriving Show

instance TCConstraint IsNonConst where
  constr = IsNonConst
  runConstr (IsNonConst c) = c

instance Typeable k => FixedVars TVarOf (IsNonConst (DMTypeOf k, DMTypeOf k)) where
  fixedVars (IsNonConst _) = []

instance Typeable k => Solve MonadDMTC IsNonConst (DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ name (IsNonConst (τ, τ_nonconst)) = do
     let freev = freeVars @_ @TVarOf τ
         freev' = filterSomeK @TVarOf @BaseNumKind freev

     case (length freev == length freev') of
       True -> do let a = makeNonConst_JuliaVersion τ
                  unify τ_nonconst a
                  dischargeConstraint name
       False -> return ()




-------------------------------------------------------------------
-- Mostly unify two types, but when encountering const / non-const
-- things behave like subtyping.
--

newtype UnifyWithConstSubtype a = UnifyWithConstSubtype a deriving Show

instance TCConstraint UnifyWithConstSubtype where
  constr = UnifyWithConstSubtype
  runConstr (UnifyWithConstSubtype c) = c

instance Typeable k => FixedVars TVarOf (UnifyWithConstSubtype (DMTypeOf k, DMTypeOf k)) where
  fixedVars (UnifyWithConstSubtype _) = []


instance Typeable k => Solve MonadDMTC UnifyWithConstSubtype (DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ name (UnifyWithConstSubtype (a, b)) = case a of
    ----------
    -- interesting const / non-const cases
    --
    --
    -- "if a[--] <= x, then x needs to be a[n]"
    NonConst dto -> unify a b >> dischargeConstraint name
    --
    --
    -- "if a[n] <= x, then we do not know about x, it could be const or non-const"
    Const sk dto -> case b of
      -- if rhs is a variable, we keep our constraint
      TVar so -> pure ()

      -- if const/nonconst, we can unify all components
      Const sk' dto' -> unify sk sk' >> unify dto dto' >> dischargeConstraint name
      NonConst dto' -> unify dto dto' >> dischargeConstraint name

      -- rest
      DMAny -> internalError "This case distinction was not fully thought out."
      DMData -> unify a b >> dischargeConstraint name

    ----------
    -- induction step
    Numeric dto -> do dto' <- newVar ; unify (Numeric dto') b ; dischargeConstraint name ; addConstraint (Solvable (UnifyWithConstSubtype (dto, dto'))) ; pure ()
    (:->:) xs dto -> do
      xs' <- mapM (\a -> (:@ a) <$> newVar) ((\(_ :@ a) -> a) <$> xs)
      dto' <- newVar
      unify (xs' :->: dto') b
      dischargeConstraint name
      mapM (addConstraint . Solvable . UnifyWithConstSubtype) (zip (fstAnn <$> xs) (fstAnn <$> xs'))
      addConstraint (Solvable (UnifyWithConstSubtype (dto, dto')))
      pure ()
    (:->*:) xs dto -> do
      xs' <- mapM (\a -> (:@ a) <$> newVar) ((\(_ :@ a) -> a) <$> xs)
      dto' <- newVar
      unify (xs' :->*: dto') b
      dischargeConstraint name
      mapM (addConstraint . Solvable . UnifyWithConstSubtype) (zip (fstAnn <$> xs) (fstAnn <$> xs'))
      addConstraint (Solvable (UnifyWithConstSubtype (dto, dto')))
      pure ()
    DMTup dtos -> do
      dtos' <- mapM (\() -> newVar) ((\_ -> ()) <$> dtos)
      unify (DMTup dtos') b
      dischargeConstraint name
      mapM (addConstraint . Solvable . UnifyWithConstSubtype) (zip dtos dtos')
      pure ()
    DMContainer dto dto1 dto2 sk dto3 -> do dto3' <- newVar ; unify (DMContainer dto dto1 dto2 sk dto3') b ; dischargeConstraint name ; addConstraint (Solvable (UnifyWithConstSubtype (dto3, dto3'))) ; pure ()
    DMModel sk dto -> do dto' <- newVar ; unify (DMModel sk dto') b ; dischargeConstraint name ; addConstraint (Solvable (UnifyWithConstSubtype (dto, dto'))) ; pure ()
    NoFun dto -> do dto' <- newVar ; unify (NoFun dto') b ; dischargeConstraint name ; addConstraint (Solvable (UnifyWithConstSubtype (dto, dto'))) ; pure ()
    Fun xs -> do
      xs' <- mapM (\a -> (:@ a) <$> newVar) ((\(_ :@ a) -> a) <$> xs)
      unify (Fun xs') b
      dischargeConstraint name
      mapM (addConstraint . Solvable . UnifyWithConstSubtype) (zip (fstAnn <$> xs) (fstAnn <$> xs'))
      pure ()
    (:∧:) dto dto' -> pure ()

    TVar so -> case b of
      --------
      --
      -- interesting cases
      --
      -- "if x <= a[n], then x needs to be equal to a"
      Const sk dto -> unify a b >> dischargeConstraint name
      --
      -- "if x <= a[--], then we do not know about x"
      NonConst dto -> pure ()

      --------
      --
      -- induction cases
      Numeric dto -> do dto' <- newVar ; unify (Numeric dto') a ; dischargeConstraint name ; addConstraint (Solvable (UnifyWithConstSubtype (dto, dto'))) ; pure ()
      (:->:) xs dto -> do
        xs' <- mapM (\a -> (:@ a) <$> newVar) ((\(_ :@ a) -> a) <$> xs)
        dto' <- newVar
        unify (xs' :->: dto') a
        dischargeConstraint name
        mapM (addConstraint . Solvable . UnifyWithConstSubtype) (zip (fstAnn <$> xs) (fstAnn <$> xs'))
        addConstraint (Solvable (UnifyWithConstSubtype (dto, dto')))
        pure ()
      (:->*:) xs dto -> do
        xs' <- mapM (\a -> (:@ a) <$> newVar) ((\(_ :@ a) -> a) <$> xs)
        dto' <- newVar
        unify (xs' :->*: dto') a
        dischargeConstraint name
        mapM (addConstraint . Solvable . UnifyWithConstSubtype) (zip (fstAnn <$> xs) (fstAnn <$> xs'))
        addConstraint (Solvable (UnifyWithConstSubtype (dto, dto')))
        pure ()
      DMTup dtos -> do
        dtos' <- mapM (\() -> newVar) ((\_ -> ()) <$> dtos)
        unify (DMTup dtos') a
        dischargeConstraint name
        mapM (addConstraint . Solvable . UnifyWithConstSubtype) (zip dtos dtos')
        pure ()
      DMContainer dto dto1 dto2 sk dto3 -> do dto3' <- newVar ; unify (DMContainer dto dto1 dto2 sk dto3') a ; dischargeConstraint name ; addConstraint (Solvable (UnifyWithConstSubtype (dto3, dto3'))) ; pure ()
      DMModel sk dto -> do dto' <- newVar ; unify (DMModel sk dto') a ; dischargeConstraint name ; addConstraint (Solvable (UnifyWithConstSubtype (dto, dto'))) ; pure ()
      NoFun dto -> do dto' <- newVar ; unify (NoFun dto') a ; dischargeConstraint name ; addConstraint (Solvable (UnifyWithConstSubtype (dto, dto'))) ; pure ()
      Fun xs -> do
        xs' <- mapM (\a -> (:@ a) <$> newVar) ((\(_ :@ a) -> a) <$> xs)
        unify (Fun xs') a
        dischargeConstraint name
        mapM (addConstraint . Solvable . UnifyWithConstSubtype) (zip (fstAnn <$> xs) (fstAnn <$> xs'))
        pure ()

      TVar so' -> pure ()

      -- the rest are induction base cases, we directly unify lhs with rhs
      -- { DMAny DMInt DMReal DMData L1 L2 LInf U (Clip dto) Vector Gradient Matrix (BlackBox jts )}
      b -> unify a b >> dischargeConstraint name

    -- the rest are induction base cases, we directly unify lhs with rhs
    -- { DMAny DMInt DMReal DMData L1 L2 LInf U (Clip dto) Vector Gradient Matrix (BlackBox jts )}
    a -> unify a b >> dischargeConstraint name






