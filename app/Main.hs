module Main where

-- import Lib
import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Typecheck.Typecheck
import Example.Terms

main :: IO ()
main = do
  putStrLn "Starting DiffMu!"
  let r = checkSens t₁ def
  let x = runExcept (runStateT (runTCT r) def)
  case x of
    Left err -> putStrLn $ "Encountered error: " <> show err
    Right x -> putStrLn $ "Result: " <> show x
  putStrLn "Done!"
  return ()





