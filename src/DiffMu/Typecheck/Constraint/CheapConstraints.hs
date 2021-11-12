
module DiffMu.Typecheck.Constraint.CheapConstraints where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Abstract.Data.Permutation
import DiffMu.Core.Definitions
import DiffMu.Core.Logging
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Typecheck.Subtyping
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
import qualified Prelude as P


-------------------------------------------------------------------
-- set the a type to a variable const, in case it's numeric or a tuple.
--

newtype MakeConst a = MakeConst a deriving Show

instance TCConstraint MakeConst where
  constr = MakeConst
  runConstr (MakeConst c) = c

instance Typeable k => FixedVars TVarOf (MakeConst (DMTypeOf k)) where
  fixedVars (MakeConst _) = []

instance Typeable k => Solve MonadDMTC MakeConst (DMTypeOf k) where
  solve_ Dict _ name (MakeConst τ) = do
     -- colltect all free variables that are numeric
     let freev = freeVars @_ @TVarOf τ
         freev0 = filterSomeK @TVarOf @BaseNumKind freev
         freev1 = filterSomeK @TVarOf @NormKind freev
         freev2 = filterSomeK @TVarOf @ClipKind freev
         freev3 = filterSomeK @TVarOf @NumKind freev

     let makeVarConst v = do
                     k <- newVar
                     τv <- newVar
                     unify (TVar v) (Const k τv)

     mapM makeVarConst freev3

     -- compare the length of `m` and `n`, that is, if all free variables
     -- have the aforementioned kinds
     let m = length freev
         n = length freev0 P.+ length freev1 P.+ length freev2 P.+ length freev3

     case (m == n) of
        True -> dischargeConstraint name
        False -> pure () -- there are free variables whose numericity is not yet clear




----------------------------------------------------------
-- replacing all Numeric TVars by non-const


newtype MakeNonConst a = MakeNonConst a deriving Show

instance TCConstraint MakeNonConst where
  constr = MakeNonConst
  runConstr (MakeNonConst c) = c

instance Typeable k => FixedVars TVarOf (MakeNonConst (DMTypeOf k)) where
  fixedVars (MakeNonConst _) = []

instance Typeable k => Solve MonadDMTC MakeNonConst (DMTypeOf k) where
  solve_ Dict _ name (MakeNonConst τ) = do
     let freev = freeVars @_ @TVarOf τ
         freev0 = filterSomeK @TVarOf @BaseNumKind freev
         freev1 = filterSomeK @TVarOf @NormKind freev
         freev2 = filterSomeK @TVarOf @ClipKind freev
         freev3 = filterSomeK @TVarOf @NumKind freev

     let makeVarNonConst v = do
                     -- k <- newVar
                     τv <- newVar
                     unify (TVar v) (NonConst τv)

     mapM makeVarNonConst freev3


     -- compare the length of `m` and `n`, that is, if all free variables
     -- have the aforementioned kinds
     let m = length freev
         n = length freev0 P.+ length freev1 P.+ length freev2 P.+ length freev3

     case (m == n) of
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


--------------------------------------------------
-- is it gauss or mgauss?
instance FixedVars TVarOf (IsGaussResult (DMTypeOf MainKind, DMTypeOf MainKind)) where
  fixedVars (IsGaussResult (gauss,_)) = freeVars gauss

instance Solve MonadDMTC IsGaussResult (DMTypeOf MainKind, DMTypeOf MainKind) where
  solve_ Dict _ name (IsGaussResult (τgauss, τin)) =
     case τin of
        TVar x -> pure () -- we don't know yet.
        NoFun (DMGrads nrm clp n τ) -> do -- is mgauss

           logForce $ ">>>>>>>>>>>>>>>>>>>>>>>>\nIn gauss, type is " <> show (DMGrads nrm clp n τ) <> "<<<<<<<<<<<<<<<<<<<<<"

           iclp <- newVar -- clip of input matrix can be anything
           τv <- newVar -- input matrix element type can be anything (as long as it's numeric)

           -- set in- and output types as given in the mgauss rule
           -- input type gets a LessEqual so convert can happen implicitly if necessary
           -- (convert is implemented as a special subtyping rule, see there)
           addConstraint(Solvable(IsLessEqual(τin, (NoFun (DMGrads L2 iclp n (Numeric (τv)))))))
           unify τgauss (NoFun (DMGrads LInf U n (Numeric (NonConst DMReal))))

           dischargeConstraint @MonadDMTC name
        _ -> do -- regular gauss or unification errpr later
           τ <- newVar -- input type can be anything (as long as it's numeric)

           -- set in- and output types as given in the gauss rule
           unify τin (NoFun (Numeric τ))
           unify τgauss (NoFun (Numeric (NonConst DMReal)))

           dischargeConstraint @MonadDMTC name


--------------------------------------------------
-- reordering of tuples

newtype IsReorderedTuple a = IsReorderedTuple a deriving Show

instance FixedVars TVarOf (IsReorderedTuple (([Int], DMTypeOf MainKind) :=: DMTypeOf MainKind)) where
  fixedVars (IsReorderedTuple (_ :=: ρ)) = freeVars ρ

instance TCConstraint IsReorderedTuple where
  constr = IsReorderedTuple
  runConstr (IsReorderedTuple c) = c

instance Solve MonadDMTC IsReorderedTuple (([Int], DMTypeOf MainKind) :=: DMTypeOf MainKind) where
  solve_ Dict _ name (IsReorderedTuple ((σ , τ) :=: ρ)) = f τ
    where
      f :: MonadDMTC t => DMTypeOf MainKind -> t ()
      f (TVar _) = pure ()
      f (NoFun (TVar _)) = pure ()
      f (NoFun (DMTup τs)) = do
        unify ρ (NoFun (DMTup (permute σ τs)))
        dischargeConstraint name
        pure ()
      f (τs) = throwError (TypeMismatchError $ "Expected the type " <> show τ <> " to be a tuple type.")


--------------------------------------------------
-- projecting of tuples

newtype IsTProject a = IsTProject a deriving Show

instance FixedVars TVarOf (IsTProject ((Int, DMTypeOf MainKind) :=: DMTypeOf MainKind)) where
  fixedVars (IsTProject (_ :=: ρ)) = freeVars ρ

instance TCConstraint IsTProject where
  constr = IsTProject
  runConstr (IsTProject c) = c

instance Solve MonadDMTC IsTProject ((Int, DMTypeOf MainKind) :=: DMTypeOf MainKind) where
  solve_ Dict _ name (IsTProject ((i , ρs) :=: ρ)) = f ρs
    where
      f :: MonadDMTC t => DMTypeOf MainKind -> t ()
      f (TVar _) = pure ()
      f (NoFun (TVar _)) = pure ()
      f (NoFun (DMTup ρs)) = do
        let ρ' = ρs ^? element i
        case ρ' of
          Just ρ' -> do
            unify ρ (NoFun ρ')
            dischargeConstraint name
            pure ()
          Nothing -> internalError $ "tuple index out of range\nwhere index: " <> show i <> ",tuple type: " <> show ρs
      f (τs) = throwError (TypeMismatchError $ "Expected the type " <> show ρs <> " to be a tuple type.")


--------------------------------------------------
-- black boxes

newtype IsBlackBox a = IsBlackBox a deriving Show

instance FixedVars TVarOf (IsBlackBox ((DMTypeOf MainKind, [DMTypeOf MainKind]))) where
  fixedVars (IsBlackBox (b, args)) = []

instance TCConstraint IsBlackBox where
  constr = IsBlackBox
  runConstr (IsBlackBox c) = c

instance Solve MonadDMTC IsBlackBox (DMMain, [DMMain]) where
    solve_ Dict _ name (IsBlackBox (box, args)) = 
     case box of
        TVar x -> pure () -- we don't know yet.
        BlackBox jts -> do -- its a box!
           case length jts == length args of
                True -> let setArg :: IsT MonadDMTC t => (JuliaType, DMMain) -> t ()
                            setArg (jt, arg) = addJuliaSubtypeConstraint arg jt
                        in do
                            mapM setArg (zip jts args)
                            dischargeConstraint @MonadDMTC name
                False -> throwError (NoChoiceFoundError "Wrong number of arguments for black box call.")
        _ -> impossible $ "Box Apply used with non-box!"




newtype IsBlackBoxReturn a = IsBlackBoxReturn a deriving Show

instance FixedVars TVarOf (IsBlackBoxReturn ((DMTypeOf MainKind, (DMTypeOf MainKind, Sensitivity)))) where
  fixedVars (IsBlackBoxReturn (b, args)) = []

instance TCConstraint IsBlackBoxReturn where
  constr = IsBlackBoxReturn
  runConstr (IsBlackBoxReturn c) = c


instance Solve MonadDMTC IsBlackBoxReturn (DMMain, (DMMain, Sensitivity)) where
    solve_ Dict _ name (IsBlackBoxReturn (ret, (argt, args))) =
     let discharge s = do
                          unify args s
                          dischargeConstraint @MonadDMTC name
     in case ret of
          TVar _ -> pure ()
          NoFun (DMVecLike vret nret cret dret tret) -> do
              unify ret (NoFun (DMVecLike vret LInf U dret (Numeric DMData)))
              case argt of
                   TVar _ -> pure ()
                   NoFun (DMVecLike _ _ _ _ targ) -> do
                       unify targ (Numeric DMData)
                       discharge oneId
                   _ -> discharge inftyS
          _ -> discharge inftyS

{-
-- TODO for now we set output to L_inf directly
-- black boxes have infinite sensitivity in their arguments, except for ones whose output is a vector with
-- (L_inf, Data) norm and the argument is a vector with any Data norm. in this case the black box (as every
-- other function with such input/output) has sensitivity 1 in that argument.
instance Solve MonadDMTC IsBlackBoxReturn (DMMain, (DMMain, Sensitivity)) where
    solve_ Dict SolveSpecial name (IsBlackBoxReturn (ret, (argt, args))) =
     let discharge s = do
                          unify args s
                          dischargeConstraint @MonadDMTC name
     in case ret of
          TVar _ -> pure ()
          NoFun (DMVecLike _ nret cret n tret) -> case cret of
              U -> case argt of
                        TVar _ -> pure ()
                        NoFun (DMVecLike _ narg carg _ targ) -> case (nret, tret) of
                           (TVar _, TVar _)         -> pure ()
                           (LInf, TVar _)           -> pure ()
                           (TVar _, Numeric DMData) -> pure ()
                           -- if the output norm d is (L_inf, Data) and the input norm is some norm d' on data,
                           -- we have for every function f and all input vectors x!=y:
                           -- d(f(x), f(y)) = 1 <= d'(x, y)
                           -- so f is 1-sensitive using these norms.
                           (LInf, Numeric DMData)   -> case targ of
                              TVar _ -> pure ()
                              (Numeric DMData) -> discharge oneId
                              _ -> discharge inftyS
                           _ -> discharge inftyS
                        _ -> discharge inftyS
              _ -> do
                      unify cret U -- output type cannot be clipped
                      return ()
          _ -> discharge inftyS
-- if the blackbox output is a vector, the black boxes sensitivity is 1 when measured using the (L_inf, Data) norm on
-- the output vector and some Data norm on the input vector (see above).
-- in the final typechecking stage it is likely that we won't manage to infer the vector norm, so we just set it to (L_inf, Data),
-- risking unification errors but giving us sensitivity 1 on the black box...
    solve_ Dict SolveFinal name (IsBlackBoxReturn (ret, (argt, args))) = case (ret, argt) of
          (NoFun (DMVecLike vret nret cret dret tret), (NoFun (DMVecLike varg narg carg darg targ))) -> do
              unify ret (NoFun (DMVecLike vret LInf U dret (Numeric DMData)))
              unify targ (Numeric DMData)
              return ()
          _ -> pure ()
          
    solve_ Dict _ name (IsBlackBoxReturn (ret, (argt, args))) = pure ()
    -}


instance Solve MonadDMTC IsLess (Sensitivity, Sensitivity) where
  solve_ Dict _ name (IsLess (s1, s2)) = solveLessSensitivity s1 s2
    where
      solveLessSensitivity :: IsT MonadDMTC t => Sensitivity -> Sensitivity -> t ()
      solveLessSensitivity a@(SingleKinded (LinCom (MonCom as))) b@(SingleKinded (LinCom (MonCom bs))) = case (H.toList as, H.toList bs) of
        ([(MonCom aterm,av)],[(MonCom bterm, bv)]) -> do
            traceM ("solving " <> show a <> " < " <> show b)
            case (H.toList aterm, H.toList bterm) of
                 -- a has no free variables, and is infinity
                 ([],_) | av == Infty -> b ==! constCoeff Infty >> dischargeConstraint name

                 -- both a and b do not have any free variables
                 ([],[]) -> do
                              traceM ("really solving " <> show a <> " < " <> show b)
                              case (av < bv) of
                                True -> dischargeConstraint name
                                False -> failConstraint name
                 _ -> return ()
        _ -> return()

