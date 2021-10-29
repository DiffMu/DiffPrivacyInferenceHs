{-# LANGUAGE OverloadedLists #-}

module DiffMu.Typecheck.JuliaType where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions

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
