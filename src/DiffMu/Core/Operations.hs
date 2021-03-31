
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
  do s1 <- newSVar "arg1"
     τ1 <-  TVar <$> newTVar "arg1"
     res <- TVar <$> newTVar "res"
     addConstraint' (Solvable' (IsTypeOpResult (Unary op (τ1 :@ s1) res)))
     return (res , [(τ1, s1)])
makeTypeOp (IsBinary op) 2 =
  do s1 <- newSVar "arg1"
     s2 <- newSVar "arg2"
     τ1 <-  TVar <$> newTVar "arg1"
     τ2 <-  TVar <$> newTVar "arg2"
     res <- TVar <$> newTVar "res"
     addConstraint' (Solvable' (IsTypeOpResult (Binary op (τ1:@s1, τ2:@s2) res)))
     return (res , [(τ1,s1),(τ2,s2)])
makeTypeOp (IsTernary op) 3 = undefined
makeTypeOp op lengthArgs = throwError (WrongNumberOfArgsOp op (lengthArgs))















