
module DiffMu.Core.Operations where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadTC
import DiffMu.Core.TC
import DiffMu.Core.Term
import DiffMu.Core.MonadicPolynomial
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Core.Subtyping

makeTypeOp :: (IsT MonadDMTC t) => DMTypeOp_Some -> Int -> t e ((DMNumType) , [(DMNumType,SVar)])
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
makeTypeOp (IsTernary op) 3 = undefined
makeTypeOp op lengthArgs = throwError (WrongNumberOfArgsOp op (lengthArgs))


solveBinaryNum :: forall t e. IsT MonadDMTC t => DMTypeOps_Binary -> (DMNumType, DMNumType) -> t e (Maybe (Sensitivity , Sensitivity, DMNumType))
solveBinaryNum op (τ1, τ2) = f op τ1 τ2
  where
    ret :: Sensitivity -> Sensitivity -> t e (DMNumType) -> t e (Maybe (Sensitivity, Sensitivity, DMNumType))
    ret s1 s2 τ = do
      τ' <- τ
      return (Just (s1, s2, τ'))

    f :: DMTypeOps_Binary -> (DMNumType) -> (DMNumType) -> t e (Maybe (Sensitivity , Sensitivity, DMNumType))
    f DMOpAdd (Const s1 t1) (Const s2 t2) = ret zeroId zeroId (Const (s1 ⋆! s2) <$> supremum t1 t2)
    f DMOpAdd (Const s1 t1) (NonConst t2) = ret zeroId oneId  (NonConst <$> supremum t1 t2)
    f DMOpAdd (NonConst t1) (Const s2 t2) = ret oneId  zeroId (NonConst <$> supremum t1 t2)
    f DMOpAdd (NonConst t1) (NonConst t2) = ret oneId  oneId  (NonConst <$> supremum t1 t2)
    f DMOpAdd _ _                         = return Nothing
    f _ _ _ = undefined


  -- (\a -> Just (s1, s1, a)) <$> Const <$> supremum t1 t2 <*> pure s1
-- solveBinaryNum op _ = pure Nothing

solveop :: (IsT MonadDMTC t) => SolvingMode -> Symbol -> IsTypeOpResult DMTypeOp -> t e ()
solveop mode name (IsTypeOpResult (UnaryNum op (τa :@ s) τr)) = undefined
solveop mode name (IsTypeOpResult (BinaryNum op (τa1 :@ s1 , τa2 :@ s2) τr)) = do
  solveres <- solveBinaryNum op (τa1, τa2)
  case solveres of
    Nothing -> return ()
    Just (val_s1, val_s2, val_τr) -> do
      addSub (s1 := val_s1)
      addSub (s2 := val_s2)
      -- unify (svar s1) val_s1
      -- unify (svar s2) val_s2
      unify τr val_τr
      dischargeConstraint @MonadDMTC name
solveop mode name (IsTypeOpResult (Ternary op xx res)) = undefined

instance Solve MonadDMTC (IsTypeOpResult) DMTypeOp where
  solve_ Dict mode name constr = solveop mode name constr














