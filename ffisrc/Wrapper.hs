
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

foreign import ccall "dynamic" mkFun :: FunPtr (CInt -> CInt) -> (CInt -> CInt)

-- data SubComplicated = SubComplicated Int Float String deriving(Show, Generic, NFData)

-- data Complicated = Complicated {
--   _f1 :: SubComplicated,
--   _f2 :: [Float],
--   _f3 :: Int32 -> Int32
-- }

-- instance Show Complicated where
--   show (Complicated f1' f2' f3') = "Complicated:\n\t" ++ show f1' ++ "\n\t" ++ show f2' ++ "\n\tf3(0)=" ++ show (f3' 0)


-- newComplicated :: Complicated
-- newComplicated = Complicated {
--   _f1 = SubComplicated 5 0.5 "hi",
--   _f2 = [0.1,0.2,5],
--   _f3 = (+2)
-- }

-- makeLenses ''Complicated


-- basicWrapper :: IO ()
-- basicWrapper = print "wrapper" >> run

-- getComplicated :: IO (StablePtr Complicated)
-- getComplicated = newStablePtr newComplicated

-- printComplicated :: StablePtr Complicated -> IO ()
-- printComplicated ptr = do
--   v <- deRefStablePtr ptr
--   print v

-- mutateComplicated :: CFloat -> StablePtr Complicated -> IO (StablePtr Complicated)
-- mutateComplicated (CFloat addme) ptr = do
--   v <- deRefStablePtr ptr
--   let
--     newcomp = over f2 (++[addme]) v
--   freeStablePtr ptr
--   newStablePtr newcomp



-- setAdder :: FunPtr (CInt -> CInt) -> StablePtr Complicated -> IO (StablePtr Complicated)
-- setAdder fptr ptr = do
--   v <- deRefStablePtr ptr
--   let
--     newAdder x = r where
--       CInt r = (mkFun fptr) (CInt x)
--     newcomp = set f3 newAdder v
--   freeStablePtr ptr
--   newStablePtr newcomp

-- freeComplicated :: StablePtr Complicated -> IO ()
-- freeComplicated = freeStablePtr


callWithCString :: FunPtr (CString -> CString -> Bool) -> String -> String -> Bool
callWithCString f a b = unsafeLocalState $ do
  withCString a (\ca -> withCString b (\cb -> return $ call_StringStringBool f ca cb))



typecheckFromCString_DMTerm :: FunPtr (CString -> CString -> Bool) -> CString -> IO ()
typecheckFromCString_DMTerm fun str = do
  putStrLn "hello!"
  -- let ident = "Integer"
  -- int <- (newCString ident)
  -- let int = (JuliaType ident)

  -- let ident = "Real"
  -- real <- (newCString ident)
  -- -- let real = (JuliaType ident cident)
  -- putStrLn $ "I want to call: " <> show fun <> "with " <> show int <> " and " <> show real
  -- -- let myres = callWithCString fun "Integer" "Real"
  -- let a = "Integer"
  -- let b = "Real"
  -- let myres2 = unsafeLocalState (withCString a (\ca -> withCString b (\cb -> return $ call_StringStringBool fun ca cb)))
  -- putStrLn $ "myres is" <> show myres2


  writeIORef global_callback_issubtype (makeDMEnv (fun))
  str' <- peekCString str
  typecheckFromString_DMTerm str'

  -- putStrLn $ "I got the string: {" <> str' <> "}"


-- foreign export ccall basicWrapper :: IO ()
-- foreign export ccall getComplicated :: IO (StablePtr Complicated)
-- foreign export ccall printComplicated :: StablePtr Complicated -> IO ()
-- foreign export ccall freeComplicated :: StablePtr Complicated -> IO ()
-- foreign export ccall mutateComplicated :: CFloat -> StablePtr Complicated -> IO (StablePtr Complicated)
-- foreign export ccall setAdder :: FunPtr (CInt -> CInt) -> StablePtr Complicated -> IO (StablePtr Complicated)

foreign export ccall typecheckFromCString_DMTerm :: FunPtr (CString -> CString -> Bool) -> CString -> IO ()
-- foreign export ccall typecheckFromCString_DMTerm :: FunPtr ((() -> IO CString) -> (() -> IO CString) -> Bool) -> CString -> IO ()

-- foreign import ccall "dynamic" call_StringStringBool :: FunPtr (CString -> CString -> Bool) -> CString -> CString -> Bool

-- foreign import ccall "dynamic" call_StringStringBool :: FunPtr (FunPtr (StablePtr String -> IO CString) -> StablePtr String -> StablePtr String -> Bool) -> FunPtr (StablePtr String -> IO CString) -> StablePtr String -> StablePtr String -> Bool
-- foreign import ccall "dynamic" call_StringIOStringIOBool :: FunPtr (FunPtr (StablePtr String -> IO CString) -> StablePtr String -> StablePtr String -> Bool) -> FunPtr (StablePtr String -> IO CString) -> StablePtr String -> StablePtr String -> Bool


