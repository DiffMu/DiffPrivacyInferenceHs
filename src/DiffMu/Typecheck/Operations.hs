
module DiffMu.Typecheck.Operations where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Typecheck.Subtyping


-- Given a kind of a type op (`DMTypeOp_Some`), and a number of given arguments,
-- we create an `IsTypeOpResult` constraint, and return the contained types/sensitivities.
makeTypeOp :: (IsT MonadDMTC t) => DMTypeOp_Some -> Int -> t ((DMNumType) , [(DMNumType,SVar)])
makeTypeOp (IsUnary op) 1 =
  do s1 <- newSVar "η"
     τ1 <-  TVar <$> newTVar "τa"
     res <- TVar <$> newTVar "τr"
     addConstraint @MonadDMTC (Solvable (IsTypeOpResult (UnaryNum op (τ1 :@ s1) res)))
     return (res , [(τ1, s1)])
makeTypeOp (IsBinary op) 2 =
  do s1 <- newSVar "η"
     s2 <- newSVar "η"
     τ1 <-  TVar <$> newTVar "τa"
     τ2 <-  TVar <$> newTVar "τa"
     res <- TVar <$> newTVar "τr"
     addConstraint (Solvable (IsTypeOpResult (BinaryNum op (τ1:@s1, τ2:@s2) res)))
     return (res , [(τ1,s1),(τ2,s2)])
makeTypeOp op lengthArgs = throwError (WrongNumberOfArgsOp op (lengthArgs))

-- We can solve a unary typeop constraint.
solveUnaryNum :: forall t e. IsT MonadDMTC t => DMTypeOps_Unary -> DMNumType -> t (Maybe (Sensitivity, DMNumType))
solveUnaryNum op τ = f op τ
  where
    ret :: Sensitivity -> t (DMNumType) -> t (Maybe (Sensitivity, DMNumType))
    ret s τ = do
      τ' <- τ
      return (Just (s, τ'))

    f :: DMTypeOps_Unary -> (DMNumType) -> t (Maybe (Sensitivity, DMNumType))
    f DMOpCeil (Const s1 t1) = ret zeroId (return (Const (ceil s1) DMInt))
    f DMOpCeil (NonConst t2) = ret oneId (return (NonConst DMInt))
    f DMOpCeil _             = return Nothing

-- We can solve a binary typeop constraint.
solveBinaryNum :: forall t e. IsT MonadDMTC t => DMTypeOps_Binary -> (DMNumType, DMNumType) -> t (Maybe (Sensitivity , Sensitivity, DMNumType))
solveBinaryNum op (τ1, τ2) = f op τ1 τ2
  where
    ret :: Sensitivity -> Sensitivity -> t (DMNumType) -> t (Maybe (Sensitivity, Sensitivity, DMNumType))
    ret s1 s2 τ = do
      τ' <- τ
      return (Just (s1, s2, τ'))

    f :: DMTypeOps_Binary -> (DMNumType) -> (DMNumType) -> t (Maybe (Sensitivity , Sensitivity, DMNumType))
    f DMOpAdd (Const s1 t1) (Const s2 t2) = ret zeroId zeroId (Const (s1 ⋆! s2) <$> supremum t1 t2)
    f DMOpAdd (Const s1 t1) (NonConst t2) = ret zeroId oneId  (NonConst <$> supremum t1 t2)
    f DMOpAdd (NonConst t1) (Const s2 t2) = ret oneId  zeroId (NonConst <$> supremum t1 t2)
    f DMOpAdd (NonConst t1) (NonConst t2) = ret oneId  oneId  (NonConst <$> supremum t1 t2)
    f DMOpAdd _ _                         = return Nothing

    f DMOpMul (Const s1 t1) (Const s2 t2) = ret zeroId zeroId (Const (s1 ⋅! s2) <$> supremum t1 t2)
    f DMOpMul (Const s1 t1) (NonConst t2) = ret zeroId s1 (NonConst <$> supremum t1 t2)
    f DMOpMul (NonConst t1) (Const s2 t2) = ret s2 zeroId (NonConst <$> supremum t1 t2)
    f DMOpMul (NonConst t1) (NonConst t2) = ret (constCoeff Infty) (constCoeff Infty) (NonConst <$> supremum t1 t2)
    f DMOpMul _ _                         = return Nothing

    -- TODO figure out how to handle negative numbers.
    f DMOpSub (Const s1 t1) (Const s2 t2) = ret zeroId zeroId (Const (minus s1 s2) <$> supremum t1 t2)
    f DMOpSub (Const s1 t1) (NonConst t2) = ret zeroId oneId (NonConst <$> supremum t1 t2)
    f DMOpSub (NonConst t1) (Const s2 t2) = ret oneId zeroId (NonConst <$> supremum t1 t2)
    f DMOpSub (NonConst t1) (NonConst t2) = ret oneId oneId (NonConst <$> supremum t1 t2)
    f DMOpSub _ _                         = return Nothing

    -- TODO notZero constraints for divisor?
    f DMOpDiv (Const s1 t1) (Const s2 t2) = ret zeroId zeroId (return (Const (divide s1 s2) DMReal))
    f DMOpDiv (Const s1 t1) (NonConst t2) = ret zeroId (constCoeff Infty) (return (NonConst DMReal))
    f DMOpDiv (NonConst t1) (Const s2 t2) = ret (divide oneId s2) zeroId (return (NonConst DMReal))
    f DMOpDiv (NonConst t1) (NonConst t2) = ret (constCoeff Infty) (constCoeff Infty) (return (NonConst DMReal))
    f DMOpDiv _ _                         = return Nothing

    f _ _ _ = undefined

makeNonConstType :: (IsT MonadDMTC t) => DMNumType -> t DMNumType
makeNonConstType (TVar a) = do
  -- first we check whether the var is a fixed variable
  -- if it is, we do nothing
  fixedVars <- getFixedVars (Proxy @DMTypeOf)
  case (a `elem` fixedVars) of
    True -> return (TVar a)

    -- if a' is not fixed, we can make it non-const
    False -> do a' <- newVar
                let t = (NonConst a')
                addSub (a := t)
                return t
makeNonConstType (NonConst t) = pure $ NonConst t
makeNonConstType (Const s t) = pure $ Const s t
makeNonConstType (DMData) = pure $ DMData -- TODO: Check, we do nothing with DMData?
makeNonConstType (Deleted) = internalError "A deleted value tried to escape. We catched it when it was about to become NonConst."

makeNonConstTypeOp :: (IsT MonadDMTC t) => DMTypeOp -> t DMTypeOp
makeNonConstTypeOp (UnaryNum op (τ :@ s) ρ) = do
  τ' <- makeNonConstType τ
  pure (UnaryNum op (τ' :@ s) ρ)
makeNonConstTypeOp (BinaryNum op ((τ₁ :@ s₁) , (τ₂ :@ s₂)) ρ) = do
  τ1' <- makeNonConstType τ₁
  τ2' <- makeNonConstType τ₂
  pure (BinaryNum op ((τ1' :@ s₁) , (τ2' :@ s₂)) ρ)

----------------------------------------
-- Solving unary constraints (exactly)
solveop :: (IsT MonadDMTC t) => Symbol -> IsTypeOpResult DMTypeOp -> t ()
solveop name (IsTypeOpResult (UnaryNum op (τa :@ s) τr)) = do
  solveres <- solveUnaryNum op τa
  case solveres of
    Nothing -> return ()
    Just (val_s, val_τr) -> do
      addSub (s := val_s)
      unify τr val_τr
      dischargeConstraint @MonadDMTC name

----------------------------------------
-- Solving binary constraints (exactly)
solveop name (IsTypeOpResult (BinaryNum op (τa1 :@ s1 , τa2 :@ s2) τr)) = do
  solveres <- solveBinaryNum op (τa1, τa2)
  case solveres of
    Nothing -> return ()
    Just (val_s1, val_s2, val_τr) -> do
      -- NOTE: We do have to do unification here, instead of creating substitutions
      --       (which we theoretically could, since the LHS is a svar), because
      --       it might be that the variables on the LHS already have been substituted
      --       with something elsewhere. Thus we would have two subs for the same var
      --       in the sub context.
      unify (svar s1) val_s1
      unify (svar s2) val_s2

      unify τr val_τr
      dischargeConstraint @MonadDMTC name

instance FixedVars TVarOf (IsTypeOpResult DMTypeOp) where
  fixedVars (IsTypeOpResult (UnaryNum _ _ res)) = freeVars res
  fixedVars (IsTypeOpResult (BinaryNum _ _ res)) = freeVars res

-- An instance which says that the `IsTypeOpResult DMTypeOp` constraint is solvable
-- in the `MonadDMTC` class of monads.
instance Solve MonadDMTC (IsTypeOpResult) DMTypeOp where

  -- If we are solving exact, then we simply call `solveop`
  solve_ Dict SolveExact name constr = solveop name constr

  -- If we are "losing generality" / "assuming worst case", then we make all operands in the op into `NonConst`s.
  solve_ Dict SolveAssumeWorst name (IsTypeOpResult op) = do
    op' <- makeNonConstTypeOp op
    solveop name (IsTypeOpResult op')




opAdd x y = Op (IsBinary DMOpAdd) [x,y]
opSub x y = Op (IsBinary DMOpSub) [x,y]
opMul x y = Op (IsBinary DMOpMul) [x,y]
opCeil x = Op (IsUnary DMOpCeil) [x]
opDiv x y = Op (IsBinary DMOpDiv) [x,y]













