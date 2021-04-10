module Main where

-- import Lib
import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Term
import DiffMu.Core.Definitions
import DiffMu.Core.Operations
import DiffMu.Core.Symbolic
import DiffMu.Core.Context
import DiffMu.Core.MonadTC
import DiffMu.Core.Subtyping
import DiffMu.Typecheck.Typecheck
import Example.Terms


import Debug.Trace

-- type INT = Numeric (Const DMInt)
-- type REAL = Numeric (Const DMReal)

main :: IO ()
main = do
  putStrLn "Starting DiffMu!"
  let r :: TC Sensitivity DMType
      r = do
        -- a <- svar <$> newSVar "a"
        -- b <- svar <$> newSVar "a"
        -- let x = (traceShowId a) +! (traceShowId b)
        -- traceShow x (checkSens t₄ def)

        -- tres <- checkSens t₅ def

        let iINT = Numeric (NonConst DMInt)
        let rREAL = Numeric (NonConst DMReal)
        aa <- TVar <$> newTVar @MainKind "a"

        -- addConstraint (Solvable (IsLessEqual (DMInt,DMReal)))
        addConstraint (Solvable (IsLessEqual (([iINT :@ oneId] :->: rREAL),aa)))
        solveAllConstraints SolveExact
        return (Numeric (NonConst DMInt))
        -- normalize tres

  let x = runExcept (runStateT (runTCT r) def)
  case x of
    Left err -> putStrLn $ "Encountered error: " <> show err
    Right x -> putStrLn $ "Result: " <> show x
  putStrLn "Done!"
  return ()





