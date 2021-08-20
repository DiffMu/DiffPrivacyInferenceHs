
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
makeTypeOp :: (IsT MonadDMTC t) => DMTypeOp_Some -> Int -> t ((DMType) , [(DMType,SVar)])
makeTypeOp (IsUnary op) 1 =
  do s1 <- newSVar "η"
     τ1 <-  TVar <$> newTVar "τa"
     res <- TVar <$> newTVar "τr"
     addConstraint @MonadDMTC (Solvable (IsTypeOpResult (Unary op (τ1 :@ s1) res)))
     return (res , [(τ1, s1)])
makeTypeOp (IsBinary op) 2 =
  do s1 <- newSVar "η"
     s2 <- newSVar "η"
     τ1 <-  TVar <$> newTVar "τa"
     τ2 <-  TVar <$> newTVar "τa"
     res <- TVar <$> newTVar "τr"
     addConstraint (Solvable (IsTypeOpResult (Binary op (τ1:@s1, τ2:@s2) res)))
     return (res , [(τ1,s1),(τ2,s2)])
makeTypeOp op lengthArgs = throwError (WrongNumberOfArgsOp op (lengthArgs))

-- We can solve a unary typeop constraint.
solveUnary :: forall t e. IsT MonadDMTC t => DMTypeOps_Unary -> DMType -> t (Maybe (Sensitivity, DMType))
solveUnary op τ = f op τ
  where
    ret :: Sensitivity -> t (DMType) -> t (Maybe (Sensitivity, DMType))
    ret s τ = do
      τ' <- τ
      return (Just (s, τ'))

    f :: DMTypeOps_Unary -> DMType -> t (Maybe (Sensitivity, DMType))
    f DMOpCeil (Numeric (Const s1 t1)) = ret zeroId (return (Numeric (Const (ceil s1) DMInt)))
    f DMOpCeil (Numeric (NonConst t2)) = ret oneId (return (Numeric (NonConst DMInt)))
    f DMOpCeil _             = return Nothing

-- We can solve a binary typeop constraint.
solveBinary :: forall t e. IsT MonadDMTC t => DMTypeOps_Binary -> (DMType, DMType) -> t (Maybe (Sensitivity , Sensitivity, DMType))
solveBinary op (τ1, τ2) = f op τ1 τ2
  where
    ret :: Sensitivity -> Sensitivity -> t (DMType) -> t (Maybe (Sensitivity, Sensitivity, DMType))
    ret s1 s2 τ = do
      τ' <- τ
      return (Just (s1, s2, τ'))

    f :: DMTypeOps_Binary -> (DMType) -> (DMType) -> t (Maybe (Sensitivity , Sensitivity, DMType))
    f DMOpAdd (Numeric (Const s1 t1)) (Numeric (Const s2 t2)) = ret zeroId zeroId ((Numeric . (Const (s1 ⋆! s2)) <$> supremum t1 t2))
    f DMOpAdd (Numeric (Const s1 t1)) (Numeric (NonConst t2)) = ret zeroId oneId  ((Numeric . NonConst) <$> supremum t1 t2)
    f DMOpAdd (Numeric (NonConst t1)) (Numeric (Const s2 t2)) = ret oneId  zeroId ((Numeric . NonConst) <$> supremum t1 t2)
    f DMOpAdd (Numeric (NonConst t1)) (Numeric (NonConst t2)) = ret oneId  oneId  ((Numeric . NonConst) <$> supremum t1 t2)
    f DMOpAdd (DMMat n1 cl1 r1 c1 t1) (DMMat n2 cl2 r2 c2 t2) = do
                                                             s <- solveBinary op (t1, t2)
                                                             unify n1 n2
                                                             unify r1 r2
                                                             unify c1 c2
                                                             case s of
                                                                Nothing -> return Nothing
                                                                Just (s1, s2, τ) -> return (Just (s1, s2, (DMMat n1 U r1 c1 τ)))
    f DMOpAdd (DMMat n cl r c t) (TVar a) = do
                                               clv <- newVar
                                               τ <- newVar
                                               unify (TVar a) (DMMat n clv r c τ)
                                               return Nothing
    f DMOpAdd (TVar a) (DMMat n cl r c t) = solveBinary DMOpAdd ((DMMat n cl r c t), (TVar a))


    f DMOpMul (Numeric (Const s1 t1)) (Numeric (Const s2 t2)) = ret zeroId zeroId ((Numeric . (Const (s1 ⋅! s2))) <$> supremum t1 t2)
    f DMOpMul (Numeric (Const s1 t1)) (Numeric (NonConst t2)) = ret zeroId s1 ((Numeric . NonConst) <$> supremum t1 t2)
    f DMOpMul (Numeric (NonConst t1)) (Numeric (Const s2 t2)) = ret s2 zeroId ((Numeric . NonConst) <$> supremum t1 t2)
    f DMOpMul (Numeric (NonConst t1)) (Numeric (NonConst t2)) = ret (constCoeff Infty) (constCoeff Infty) ((Numeric . NonConst) <$> supremum t1 t2)
    f DMOpMul (Numeric τs) (DMMat n cl r c τm)                = do
                                                             s <- solveBinary op (Numeric τs, τm)
                                                             case s of
                                                                Nothing -> return Nothing
                                                                Just (s1, s2, τ) -> return (Just (r ⋅! c ⋅! s1, s2, (DMMat n U r c τ)))

    -- TODO figure out how to handle negative numbers.
    f DMOpSub (Numeric (Const s1 t1)) (Numeric (Const s2 t2)) = ret zeroId zeroId ((Numeric . (Const (minus s1 s2))) <$> supremum t1 t2)
    f DMOpSub (Numeric (Const s1 t1)) (Numeric (NonConst t2)) = ret zeroId oneId ((Numeric . NonConst) <$> supremum t1 t2)
    f DMOpSub (Numeric (NonConst t1)) (Numeric (Const s2 t2)) = ret oneId zeroId ((Numeric . NonConst) <$> supremum t1 t2)
    f DMOpSub (Numeric (NonConst t1)) (Numeric (NonConst t2)) = ret oneId oneId ((Numeric . NonConst) <$> supremum t1 t2)
    f DMOpSub (DMMat n1 cl1 r1 c1 t1) (DMMat n2 cl2 r2 c2 t2) = do
                                                             s <- solveBinary op (t1, t2)
                                                             unify n1 n2
                                                             unify r1 r2
                                                             unify c1 c2
                                                             case s of
                                                                Nothing -> return Nothing
                                                                Just (s1, s2, τ) -> return (Just (s1, s2, (DMMat n1 U r1 c1 τ)))
    f DMOpSub (DMMat n cl r c t) (TVar a) = do
                                               clv <- newVar
                                               τ <- newVar
                                               unify (TVar a) (DMMat n clv r c τ)
                                               return Nothing
    f DMOpSub (TVar a) (DMMat n cl r c t) = solveBinary DMOpSub ((DMMat n cl r c t), (TVar a))


    -- TODO notZero constraints for divisor?
    f DMOpDiv (Numeric (Const s1 t1)) (Numeric (Const s2 t2)) = ret zeroId zeroId (return (Numeric (Const (divide s1 s2) DMReal)))
    f DMOpDiv (Numeric (Const s1 t1)) (Numeric (NonConst t2)) = ret zeroId (constCoeff Infty) (return (Numeric (NonConst DMReal)))
    f DMOpDiv (Numeric (NonConst t1)) (Numeric (Const s2 t2)) = ret (divide oneId s2) zeroId (return (Numeric (NonConst DMReal)))
    f DMOpDiv (Numeric (NonConst t1)) (Numeric (NonConst t2)) = ret (constCoeff Infty) (constCoeff Infty) (return (Numeric (NonConst DMReal)))

    -- TODO: Don't we need to return a "Bool" type?
    f DMOpEq (Numeric (Const s1 t1)) (Numeric (Const s2 t2)) = ret zeroId zeroId (pure $ Numeric (NonConst DMInt))
    f DMOpEq (Numeric (Const s1 t1)) (Numeric (NonConst t2)) = ret zeroId oneId  (pure $ Numeric (NonConst DMInt))
    f DMOpEq (Numeric (NonConst t1)) (Numeric (Const s2 t2)) = ret oneId  zeroId (pure $ Numeric (NonConst DMInt))
    f DMOpEq (Numeric (NonConst t1)) (Numeric (NonConst t2)) = ret oneId  oneId  (pure $ Numeric (NonConst DMInt))

    f _ (Numeric _) (TVar a)           = do
                                           τ <- newVar
                                           unify (TVar a) (Numeric τ)
                                           return Nothing

    f _ (TVar a) (Numeric _)           = do
                                           τ <- newVar
                                           unify (TVar a) (Numeric τ)
                                           return Nothing

    f _ _ _                            = return Nothing

makeNonConstType :: (IsT MonadDMTC t) => DMType -> t DMType
makeNonConstType (Numeric (TVar a)) = do
  -- first we check whether the var is a fixed variable
  -- if it is, we do nothing
  fixedVars <- getFixedVars (Proxy @DMTypeOf)
  case (a `elem` fixedVars) of
    True -> return (Numeric (TVar a))

    -- if a' is not fixed, we can make it non-const
    False -> do a' <- newVar
                let t = (NonConst a')
                addSub (a := t)
                return (Numeric t)
makeNonConstType (Numeric (NonConst t)) = pure $ Numeric (NonConst t)
makeNonConstType (Numeric (Const s t)) = pure $ Numeric (Const s t)
makeNonConstType (Numeric DMData) = pure $ (Numeric DMData) -- TODO: Check, we do nothing with DMData?
makeNonConstType (DMMat a b c d e)  = (DMMat a b c d) <$> (makeNonConstType e)
makeNonConstType (TVar a)  = pure $ (TVar a) -- TODO: Check, we do nothing with TVar?
makeNonConstType (Deleted) = internalError "A deleted value tried to escape. We catched it when it was about to become NonConst."
makeNonConstType a = internalError ("makeNonConstType called on " <> show a)

makeNonConstTypeOp :: (IsT MonadDMTC t) => DMTypeOp -> t DMTypeOp
makeNonConstTypeOp (Unary op (τ :@ s) ρ) = do
  τ' <- makeNonConstType τ
  pure (Unary op (τ' :@ s) ρ)
makeNonConstTypeOp (Binary op ((τ₁ :@ s₁) , (τ₂ :@ s₂)) ρ) = do
  τ1' <- makeNonConstType τ₁
  τ2' <- makeNonConstType τ₂
  pure (Binary op ((τ1' :@ s₁) , (τ2' :@ s₂)) ρ)

----------------------------------------
-- Solving unary constraints (exactly)
solveop :: (IsT MonadDMTC t) => Symbol -> IsTypeOpResult DMTypeOp -> t ()
solveop name (IsTypeOpResult (Unary op (τa :@ s) τr)) = do
  solveres <- solveUnary op τa
  case solveres of
    Nothing -> return ()
    Just (val_s, val_τr) -> do
      addSub (s := val_s)
      unify τr val_τr
      dischargeConstraint @MonadDMTC name

----------------------------------------
-- Solving binary constraints (exactly)
solveop name (IsTypeOpResult (Binary op (τa1 :@ s1 , τa2 :@ s2) τr)) = do
  solveres <- solveBinary op (τa1, τa2)
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
  fixedVars (IsTypeOpResult (Unary _ _ res)) = freeVars res
  fixedVars (IsTypeOpResult (Binary _ _ res)) = freeVars res

-- An instance which says that the `IsTypeOpResult DMTypeOp` constraint is solvable
-- in the `MonadDMTC` class of monads.
instance Solve MonadDMTC (IsTypeOpResult) DMTypeOp where

  -- If we are solving exact, then we simply call `solveop`
  solve_ Dict SolveExact name constr = solveop name constr

  -- If we are "losing generality" / "assuming worst case", then we make all operands in the op into `NonConst`s.
  solve_ Dict SolveAssumeWorst name (IsTypeOpResult op) = makeNonConstTypeOp op >> return ()
  solve_ Dict _ name (IsTypeOpResult op)                = return ()




opAdd x y = Op (IsBinary DMOpAdd) [x,y]
opSub x y = Op (IsBinary DMOpSub) [x,y]
opMul x y = Op (IsBinary DMOpMul) [x,y]
opCeil x = Op (IsUnary DMOpCeil) [x]
opDiv x y = Op (IsBinary DMOpDiv) [x,y]













