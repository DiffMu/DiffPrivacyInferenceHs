module Main where

-- import Lib
import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Typecheck.Typecheck
import Example.Terms

main :: IO ()
main = do
  putStrLn "Starting DiffMu!"
  let r = checkSens t₁
  let x = runStateT r def
  case runExcept x of
    Left err -> putStrLn $ "Encountered error: " <> show err
    Right x -> putStrLn $ "Result: " <> show x
  putStrLn "Done!"
  return ()





