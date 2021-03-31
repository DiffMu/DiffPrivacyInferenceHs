module Main where

-- import Lib
import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Operations
import DiffMu.Core.Symbolic
import DiffMu.Core.Context
import DiffMu.Typecheck.Typecheck
import Example.Terms

import Debug.Trace

main :: IO ()
main = do
  putStrLn "Starting DiffMu!"
  let r = do
        -- a <- svar <$> newSVar "a"
        -- b <- svar <$> newSVar "a"
        -- let x = (traceShowId a) +! (traceShowId b)
        -- traceShow x (checkSens t₄ def)
        checkSens t₄ def
        normalizeTypes
  let x = runExcept (runStateT (runTCT r) def)
  case x of
    Left err -> putStrLn $ "Encountered error: " <> show err
    Right x -> putStrLn $ "Result: " <> show x
  putStrLn "Done!"
  return ()





