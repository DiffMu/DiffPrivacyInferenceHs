
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE DeriveAnyClass           #-}
{-# LANGUAGE DeriveGeneric            #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module Wrapper where

import DiffMu.Prelude

import           Foreign.C.Types
import           Foreign.Ptr
import           Foreign.StablePtr
import           Foreign.C.String
import           Foreign.Marshal.Unsafe

-- import           Control.DeepSeq
import           Control.Lens
import           Data.Int          (Int32)
import           GHC.Generics      (Generic)

import Data.IORef

import DiffMu.Runner
import DiffMu.Core.Definitions
import DiffMu.Typecheck.JuliaType

import Spec

foreign import ccall "dynamic" mkFun :: FunPtr (CInt -> CInt) -> (CInt -> CInt)



callWithCString :: FunPtr (CString -> CString -> Bool) -> String -> String -> Bool
callWithCString f a b = unsafeLocalState $ do
  withCString a (\ca -> withCString b (\cb -> return $ call_StringStringBool f ca cb))


typecheckFromCString_DMTerm :: FunPtr (CString -> CString -> Bool) -> CString -> IO ()
typecheckFromCString_DMTerm fun str = do
  putStrLn "hello!"

  writeIORef global_callback_issubtype (makeDMEnv (fun))
  str' <- peekCString str
  typecheckFromString_DMTerm str'

foreign export ccall typecheckFromCString_DMTerm :: FunPtr (CString -> CString -> Bool) -> CString -> IO ()


runHaskellTests :: FunPtr (CString -> CString -> Bool) -> IO ()
runHaskellTests fun = do
  putStrLn "We are testing now!"
  writeIORef global_callback_issubtype (makeDMEnv (fun))
  runAllTests

foreign export ccall runHaskellTests :: FunPtr (CString -> CString -> Bool) -> IO ()


