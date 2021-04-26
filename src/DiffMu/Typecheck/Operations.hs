
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

    f _ _ _ = undefined


-- we can solve arbitrary dmtypeop constraints
solveop :: (IsT MonadDMTC t) => SolvingMode -> Symbol -> IsTypeOpResult DMTypeOp -> t ()
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

-- An instance which says that the `IsTypeOpResult DMTypeOp` constraint is solvable
-- in the `MonadDMTC` class of monads.
instance Solve MonadDMTC (IsTypeOpResult) DMTypeOp where
  solve_ Dict mode name constr = solveop mode name constr


opAdd x y = Op (IsBinary DMOpAdd) [x,y]
opSub x y = Op (IsBinary DMOpSub) [x,y]
opMul x y = Op (IsBinary DMOpMul) [x,y]
opCeil x = Op (IsUnary DMOpCeil) [x]
opDiv x y = Op (IsBinary DMOpDiv) [x,y]













