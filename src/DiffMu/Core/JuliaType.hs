
module DiffMu.Core.JuliaType where

import DiffMu.Prelude
import DiffMu.Core.Definitions

-- local imports
import Algebra.PartialOrd

import Data.IORef
import System.IO.Unsafe

import           Foreign.C.String
import           Foreign.C.Types
import           Foreign.Ptr

import Debug.Trace

global_callback_issubtype :: IORef (DMEnv)
global_callback_issubtype = unsafePerformIO (newIORef makeEmptyDMEnv)

instance PartialOrd JuliaType where
  leq (JuliaType _ t) (JuliaType _ s) =
    let callback = (askJuliaSubtypeOf $ unsafePerformIO (readIORef global_callback_issubtype))
    in case (callback) of
      Nothing -> error "Julia callback (issubtype) is not set."
      Just f  -> call_StringStringBool f t s


foreign import ccall "dynamic" call_StringStringBool :: FunPtr (CString -> CString -> Bool) -> CString -> CString -> Bool

