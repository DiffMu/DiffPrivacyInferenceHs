module Main where

-- import Lib
import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Definitions
import DiffMu.Core.Symbolic
import DiffMu.Core.Context
import DiffMu.Typecheck.Operations
import DiffMu.Typecheck.Subtyping
import DiffMu.Typecheck.Typecheck
import Example.Terms


import Debug.Trace

-- type INT = Numeric (Const DMInt)
-- type REAL = Numeric (Const DMReal)

main :: IO ()
main = do
  putStrLn "Starting DiffMu!"
  let r :: TC DMType
      r = do

        -- typecheck the term t5
        tres <- checkPriv t12 def
        solveAllConstraints SolveExact
        normalize tres

        -- an example of subtyping
        {-
        let iINT = Numeric (NonConst DMInt)
        let rREAL = Numeric (NonConst DMReal)
        aa <- TVar <$> newTVar @MainKind "a"

        addConstraint (Solvable (IsLessEqual (([iINT :@ oneId] :->: rREAL),aa)))
        solveAllConstraints SolveExact
        normalizeContext
        normalize aa
        -}
        -- example of supremum
        a <- newVar
        addConstraint (Solvable (IsSupremum (Const oneId DMInt, NonConst DMReal, a)))
        solveAllConstraints SolveExact
        normalizeContext
        normalize (Numeric (a))

  let x = runExcept (runStateT (runTCT r) def)
  case x of
    Left err -> putStrLn $ "Encountered error: " <> show err
    Right x -> putStrLn $ "Result: " <> show x
  -- traceStack "This is a string" (putStrLn "This is a value of any type a, which 'forces' this command to actually be evaluated")
  return ()





