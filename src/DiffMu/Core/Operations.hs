
module DiffMu.Core.Operations where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadTC
import DiffMu.Core.TC
import DiffMu.Core.Term
import DiffMu.Core.MonadicPolynomial2
import DiffMu.Core.Symbolic


makeTypeOp :: (Monad m, MonadDMTC e (t m)) => DMTypeOp_Some -> Int -> t m e (DMType , [(DMType,SVar)])
makeTypeOp (IsUnary op) 1 =
  do s1 <- newSVar "η"
     τ1 <-  TVar <$> newTVar "τa"
     res <- TVar <$> newTVar "τr"
     addConstraint (Solvable (IsTypeOpResult (Unary op (τ1 :@ s1) res)))
     return (res , [(τ1, s1)])
makeTypeOp (IsBinary op) 2 =
  do s1 <- newSVar "η"
     s2 <- newSVar "η"
     τ1 <-  TVar <$> newTVar "τa"
     τ2 <-  TVar <$> newTVar "τa"
     res <- TVar <$> newTVar "τr"
     addConstraint (Solvable (IsTypeOpResult (Binary op (τ1:@s1, τ2:@s2) res)))
     return (res , [(τ1,s1),(τ2,s2)])
makeTypeOp (IsTernary op) 3 = undefined
makeTypeOp op lengthArgs = throwError (WrongNumberOfArgsOp op (lengthArgs))
















