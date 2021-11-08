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


juliatypes :: DMTypeOf k -> [JuliaType]
juliatypes (Numeric (Const _ τ)) = juliatypes τ
juliatypes (Numeric (NonConst τ)) = juliatypes τ
juliatypes (Numeric (TVar x)) = [JTInt, JTReal]
juliatypes DMInt = [JTInt]
juliatypes DMReal = [JTReal]
juliatypes (DMVec _ _ _ τ) = (map (\t -> (JTVector t)) (juliatypes τ))
juliatypes (DMMat _ _ _ _ τ) = (map (\t -> (JTMatrix t)) (juliatypes τ))
juliatypes (Const _ τ) = juliatypes τ
juliatypes (NonConst τ) = juliatypes τ
-- TODO: This is not like in DM.jl, and another workaround should be found!
juliatypes (TVar x) = [JTAny]
juliatypes (_ :->: _) = [JTFunction]
juliatypes (_ :->*: _) = [JTFunction]
juliatypes (DMTup xs) =
  let jss :: [[JuliaType]]
      jss = juliatypes `mapM` xs
      f js = JTTuple js
  in f <$> jss
juliatypes (Fun _) = [JTFunction]
juliatypes (NoFun τ) = juliatypes τ
juliatypes τ = error $ "juliatypes(" <> show τ <> ") not implemented."

global_callback_issubtype :: IORef (DMEnv)
global_callback_issubtype = unsafePerformIO (newIORef makeEmptyDMEnv)

instance PartialOrd JuliaType where
  leq a b =
    let callback = (askJuliaSubtypeOf $ unsafePerformIO (readIORef global_callback_issubtype))
    in case (callback) of
      Nothing -> error "Julia callback (issubtype) is not set."
      Just fun  -> unsafeLocalState (withCString (show a) (\ca -> withCString (show b) (\cb -> return $ call_StringStringBool fun ca cb)))
      -- Just f  -> call_StringStringBool f t s

-- `leq` on lists is defined weirdly, so we make our own for signatures.
newtype JuliaSignature = JuliaSignature [JuliaType]
  deriving (Generic, Eq, Ord, Show)

instance PartialOrd JuliaSignature where
  leq (JuliaSignature a) (JuliaSignature b) = and (zipWith leq a b)




foreign import ccall "dynamic" call_StringStringBool :: FunPtr (CString -> CString -> Bool) -> CString -> CString -> Bool


----------------------------------------------------------------------------
-- Creating DMTypes from JuliaTypes



-- Maps julia num types to DMtypes (of basenumkind)
createDMTypeBaseNum :: MonadDMTC t => JuliaType -> t (DMTypeOf BaseNumKind)
createDMTypeBaseNum (JTInt) = pure DMInt
createDMTypeBaseNum (JTReal)  = pure DMReal
createDMTypeBaseNum (t) = do
    v <- newVar
    return v

createDMTypeNum :: MonadDMTC t => JuliaType -> t (DMTypeOf NumKind)
createDMTypeNum x = NonConst <$> createDMTypeBaseNum x


createDMTypeType :: MonadDMTC t => JuliaType -> t DMType
createDMTypeType (JTInt) = do
  return (Numeric (NonConst DMInt))
createDMTypeType (JTReal) = do
  return (Numeric (NonConst DMReal))
createDMTypeType (JTTuple ts) = do
  dts <- mapM createDMTypeType ts
  return (DMTup (dts))
createDMTypeType (JTVector t) = do
  dt <- createDMTypeNum t
  nrm <- newVar
  clp <- newVar
  n <- newVar
  return (DMVec nrm clp n (Numeric (dt)))
createDMTypeType (JTMatrix t) = do
  dt <- createDMTypeNum t
  nrm <- newVar
  clp <- newVar
  n <- newVar
  m <- newVar
  return (DMMat nrm clp m n (Numeric (dt)))
createDMTypeType (JTModel) = do
  dt <- createDMTypeNum JTAny
  n <- newVar
  return (DMParams n (Numeric (dt)))
createDMTypeType (JTGrads) = do
  dt <- createDMTypeNum JTAny
  nrm <- newVar
  clp <- newVar
  n <- newVar
  return (DMGrads nrm clp n (Numeric (dt)))
createDMTypeType JTAny = do
  v <- newTVar "any"
  return (TVar v)
createDMTypeType (t)  = throwError (TypeMismatchError $ "expected " <> show t <> " to not be a function.")


-- Maps julia types to DMTypes (of main kind)
-- (`JTAny` is turned into a new type variable.)
createDMType :: MonadDMTC t => JuliaType -> t (DMTypeOf MainKind)
 -- NOTE: defaulting to non-const might or might not be what we want to do here.
createDMType (JTFunction) = do
  v <- newTVar "any"
  return (TVar v) -- TODO can we say it's a function?
createDMType (JTAny) = do
  v <- newTVar "any"
  return (TVar v)
createDMType (t) = do
  tt <- createDMTypeType t
  return (NoFun tt)

-- Adds a subtype constraint corresponding to the given julia type.
-- But does nothing if the julia type cannot be mapped to a dmtype, e.g. if it is `Any`
addJuliaSubtypeConstraint :: IsT MonadDMTC t => DMMain -> JuliaType -> t ()
addJuliaSubtypeConstraint τ JTAny = pure ()
addJuliaSubtypeConstraint τ JTFunction = pure ()
addJuliaSubtypeConstraint τ jt = do
  ι <- createDMType jt
  τ ≤! ι
  pure ()



