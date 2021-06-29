
module DiffMu.Typecheck.Constraint.CheapConstraints where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Typecheck.JuliaType
import Algebra.PartialOrd

import Debug.Trace

import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as H
import Data.HashMap.Strict (HashMap)
import qualified Data.POSet as PO
import Data.POSet (POSet)

import Debug.Trace
import qualified Data.HashMap.Strict as H


-------------------------------------------------------------------
-- set the a type to a variable const, in case it's numeric or a tuple.
--

newtype IsConst a = IsConst a deriving Show

instance TCConstraint IsConst where
  constr = IsConst
  runConstr (IsConst c) = c

instance Typeable k => FixedVars TVarOf (IsConst (DMTypeOf k)) where
  fixedVars (IsConst _) = []

instance Typeable k => Solve MonadDMTC IsConst (DMTypeOf k) where
  solve_ Dict _ name (IsConst τ) = do
     let freev = freeVars @_ @TVarOf τ
         freev' = filterSomeK @TVarOf @NumKind freev

     let makeVarConst v = do
                     k <- newVar
                     τv <- newVar
                     unify (TVar v) (Const k τv)

     mapM makeVarConst freev'

     case (length freev == length freev') of
        True -> dischargeConstraint name
        False -> pure ()

{-

makeConst_JuliaVersion :: MonadDMTC t => DMTypeOf k -> t (DMTypeOf k)
makeConst_JuliaVersion (TVar a) = return (TVar a)
makeConst_JuliaVersion (Const k a) = return (Const k a)
makeConst_JuliaVersion (NonConst a) = do
                                         k <- newVar
                                         return (Const k a)
makeConst_JuliaVersion (NoFun a) = NoFun <$> (makeConst_JuliaVersion a)
makeConst_JuliaVersion (DMTup as) = DMTup <$> (sequence (makeConst_JuliaVersion <$> as))
makeConst_JuliaVersion (Numeric a) = Numeric <$> (makeConst_JuliaVersion a)
-- everything else is not changed
makeConst_JuliaVersion x = return x
-}
-------------------------------------------------------------------
-- is it Loop or static Loop (i.e. is no of iterations const or not)

newtype IsLoopResult a = IsLoopResult a deriving Show

instance TCConstraint IsLoopResult where
  constr = IsLoopResult
  runConstr (IsLoopResult c) = c

instance FixedVars TVarOf (IsLoopResult ((Sensitivity, Sensitivity, Sensitivity), Annotation SensitivityK, DMMain)) where
  fixedVars (IsLoopResult (_, _, res)) = freeVars res


-- TODO implement this
instance Solve MonadDMTC IsLoopResult ((Sensitivity, Sensitivity, Sensitivity), Annotation SensitivityK, DMMain) where
  solve_ Dict _ name (IsLoopResult ((s1, s2, s3), sa, τ_iter)) = do
     let SensitivityAnnotation s = sa
     case τ_iter of
        NoFun (Numeric (Const η _)) -> do
           unify s1 zeroId
           unify s2 (exp s η)
           unify s3 η
           dischargeConstraint name
        NoFun (Numeric (NonConst _)) -> do
           unify s oneId
           unify s1 oneId
           unify s2 oneId
           unify s3 inftyS
           dischargeConstraint name
        _ -> return ()


