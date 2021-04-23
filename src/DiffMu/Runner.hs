
module DiffMu.Runner where

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
import DiffMu.Parser.DMTerm.FromString

import DiffMu.Core.JuliaType

import Algebra.PartialOrd

import           Foreign.C.String

run :: IO ()
run = putStrLn "Hello?"

typecheckFromString_DMTerm :: String -> IO ()
typecheckFromString_DMTerm term = do
  res <- pDMTermFromString term
  case res of
    Left err -> putStrLn $ "Error while parsing DMTerm from string: " <> show err
    Right term -> typecheckFromDMTerm term


typecheckFromDMTerm :: DMTerm -> IO ()
typecheckFromDMTerm term = do
  putStrLn "Starting DiffMu!"

  let ident = "Integer"
  cident <- (newCString ident)
  let int = (JuliaType ident cident)

  let ident = "Real"
  cident <- (newCString ident)
  let real = (JuliaType ident cident)
  putStrLn "I created a real and int.\n"

  putStrLn $ "The result is: " <> show (leq int real) <> " and " <> show (leq real int)

  let r :: TC DMType
      r = do

        -- typecheck the term t5
        tres <- checkSens term def
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

  let x = runExcept (runStateT (runTCT r) (Full def def (Right def)))
  case x of
    Left err -> putStrLn $ "Encountered error: " <> show err
    Right x -> putStrLn $ "Result: " <> show x
  return ()



