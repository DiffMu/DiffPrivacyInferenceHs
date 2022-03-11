{-# LANGUAGE OverloadedLists #-}

module DiffMu.Typecheck.JuliaType where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.TC
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Typecheck.Subtyping

-- local imports
import Algebra.PartialOrd

import Data.IORef
import System.IO.Unsafe

import           Foreign.C.String
import           Foreign.C.Types
import           Foreign.Ptr
import           Foreign.Marshal.Unsafe

import Debug.Trace

default (Text)

---------------------------------------------------------
-- getting JuliaType corresponding to DMType
--
-- get a list of all possible julia types that a dmtype could be. used to determine
-- which methods are applicable to arguments of an inferred dmtype when resolving
-- isFunctionArgument constraints. note that for TVars, who belong to arguments whose
-- type has not (yet) been inferred, we get a bottom julia type because they could
-- potentially match any method.
juliatypes :: DMTypeOf k -> [JuliaType]
juliatypes (Numeric (Num t c)) = juliatypes t
juliatypes (Numeric (TVar _)) = [JTInt, JTReal]
juliatypes DMInt = [JTInt]
juliatypes DMReal = [JTReal]
juliatypes (DMData) = [JTInt, JTReal]
juliatypes (DMVec _ _ _ τ) = (juliatypesInContainer JTVector τ)
juliatypes (DMMat _ _ _ _ τ) = (juliatypesInContainer JTMatrix τ)
juliatypes (DMGrads _ _ _ _) = [JTGrads]
juliatypes (DMContainer _ _ _ _ τ) = JTGrads : ((juliatypesInContainer JTVector τ) ++ (juliatypesInContainer JTMatrix τ))
juliatypes (TVar x) = [JTBot] -- TVars fit everywhere
juliatypes (Num t c) = juliatypes t
juliatypes (_ :->: _) = [JTFunction]
juliatypes (_ :->*: _) = [JTPFunction]
juliatypes (DMTup xs) =
  let jss :: [[JuliaType]]
      jss = juliatypes `mapM` xs
      f js = JTTuple js
  in f <$> jss
juliatypes (Fun ((τ :@ _):_)) = juliatypes τ -- TODO i am lazy and assume that the list is homogeneous. see issue #161
juliatypes (NoFun τ) = juliatypes τ
juliatypes τ = error $ "juliatypes(" <> show τ <> ") not implemented."

juliatypesInContainer constr t = map constr (juliatypes t)

----------------------------------------------------------------------------
-- Creating DMTypes from JuliaTypes

-- get a BaseNumKind DMType corresponding to the given JuliaType
createDMTypeBaseNum :: MonadDMTC t => JuliaType -> t (DMTypeOf BaseNumKind)
createDMTypeBaseNum (JTInt) = pure DMInt
createDMTypeBaseNum (JTReal) = pure DMReal
createDMTypeBaseNum (t) = pure DMAny

-- get a NumKind DMType corresponding to the given JuliaType
createDMTypeNum :: MonadDMTC t => JuliaType -> t DMMain
createDMTypeNum (JTInt) = pure (NoFun (Numeric (Num DMInt NonConst)))
createDMTypeNum (JTReal)  = do
    v <- newVar -- could be data!
    addConstraintNoMessage (Solvable (IsFloat $ NoFun (Numeric v)))
    return (NoFun (Numeric v))
createDMTypeNum (t) = pure DMAny

-- get the DMType corresponding to a given JuliaType
-- used to make DMType subtyping constraints for annotated things
createDMType :: MonadDMTC t => JuliaType -> t DMType
createDMType (JTInt) = do
  return (Numeric (Num DMInt NonConst))
createDMType (JTReal) = do
  v <- newVar
  addConstraintNoMessage (Solvable (IsFloat $ NoFun (Numeric v)))
  return (Numeric v)
createDMType (JTTuple ts) = do
  dts <- mapM createDMType ts
  return (DMTup (dts))
createDMType (JTVector t) = do
  dt <- createDMTypeNum t
  nrm <- newVar
  clp <- newVar
  n <- newVar
  return (DMVec nrm clp n dt)
createDMType (JTMatrix t) = do
  dt <- createDMTypeNum t
  nrm <- newVar
  clp <- newVar
  n <- newVar
  m <- newVar
  return (DMMat nrm clp m n dt)
createDMType (JTModel) = do
  n <- newVar
  return (DMModel n)
createDMType (JTGrads) = do
  nrm <- newVar
  clp <- newVar
  n <- newVar
  return (DMGrads nrm clp n DMAny)
createDMType JTAny = return DMAny
createDMType (t)  = throwUnlocatedError (TypeMismatchError $ "expected " <> show t <> " to not be a function.")


---------------------------------------------------------
-- julia-subtype constraints
--
-- Adds a subtype constraint corresponding to the given julia type, e.g. for annotated things.
-- But does nothing if the julia type cannot be mapped to a dmtype, e.g. if it is `Any`
addJuliaSubtypeConstraint :: IsT MonadDMTC t => DMMain -> JuliaType -> t ()
addJuliaSubtypeConstraint τ JTAny = pure ()
addJuliaSubtypeConstraint τ JTFunction = do
    addConstraintNoMessage (Solvable (IsFunction (SensitivityK, τ)))
    pure ()
addJuliaSubtypeConstraint τ JTPFunction = do
    addConstraintNoMessage (Solvable (IsFunction (PrivacyK, τ)))
    pure ()
addJuliaSubtypeConstraint τ jt = do
  ι <- createDMType jt
  (τ ≤! (NoFun ι)) "julia subtype constraint"
  pure ()


---------------------------------------------------------
-- julia subtyping
--
-- is implemented as a callback to actual julia subtyping machinery.

global_callback_issubtype :: IORef (DMEnv)
global_callback_issubtype = unsafePerformIO (newIORef makeEmptyDMEnv)

foreign import ccall "dynamic" call_StringStringBool :: FunPtr (CString -> CString -> Bool) -> CString -> CString -> Bool

-- make a call to julia subtyping, using the string representation of the JuliaTypes.
instance PartialOrd JuliaType where
  leq a b = let callback = (askJuliaSubtypeOf $ unsafePerformIO (readIORef global_callback_issubtype))
            in case (callback) of
                    Nothing -> error "Julia callback (issubtype) is not set."
                    Just fun  -> unsafeLocalState (withCString (show a) (\ca -> withCString (show b) (\cb -> return $ call_StringStringBool fun ca cb)))

-- `leq` on lists is defined weirdly, so we make our own for signatures.
newtype JuliaSignature = JuliaSignature [JuliaType]
  deriving (Generic, Eq, Ord, Show)

instance PartialOrd JuliaSignature where
  leq (JuliaSignature a) (JuliaSignature b) = and (zipWith leq a b)




--------------------------------------------------
-- real or data
--

newtype IsFloat a = IsFloat a deriving Show

instance FixedVars TVarOf (IsFloat DMMain) where
    fixedVars (IsFloat _) = []

instance TCConstraint IsFloat where
    constr = IsFloat
    runConstr (IsFloat a) = a

instance Solve MonadDMTC IsFloat DMMain where
    solve_ Dict _ name (IsFloat a) =
        case a of
             TVar _ -> pure ()
             NoFun (TVar _) -> pure ()
             NoFun (Numeric (TVar _)) -> pure ()
             (NoFun (Numeric (Num (TVar _) _))) -> pure ()
             (NoFun (Numeric (Num DMReal _))) -> dischargeConstraint name
             (NoFun (Numeric (Num DMData _))) -> dischargeConstraint name
             _ -> failConstraint name

--------------------------------------------------
-- Things that should be functions

instance FixedVars TVarOf (IsFunction (AnnotationKind, DMTypeOf MainKind)) where
  fixedVars (IsFunction (b)) = []

instance Solve MonadDMTC IsFunction (AnnotationKind, DMMain) where
    solve_ Dict _ name (IsFunction (kind, typ)) = let
        checkKind (f :@ _) = case (f, kind) of
            (_:->:_, SensitivityK) -> True
            (_:->*:_, PrivacyK) -> True
            _ -> False
        in case typ of
            Fun ts -> case and (map checkKind ts) of
                           True -> dischargeConstraint name
                           False -> failConstraint name
            NoFun _ -> failConstraint name
            _ -> pure ()
