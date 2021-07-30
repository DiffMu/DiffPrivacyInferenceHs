
module DiffMu.Runner where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Definitions
import DiffMu.Core.Symbolic
import DiffMu.Core.Context
import DiffMu.Core.Logging
import DiffMu.Core.DelayedScope
import DiffMu.Typecheck.Operations
import DiffMu.Typecheck.Subtyping
import DiffMu.Typecheck.Typecheck
import DiffMu.Parser.DMTerm.FromString

import DiffMu.Typecheck.JuliaType

import Algebra.PartialOrd

import           Foreign.C.String

import Debug.Trace

run :: IO ()
run = putStrLn "Hello?"

typecheckFromString_DMTerm :: String -> IO ()
typecheckFromString_DMTerm term = do
 let res = pDMTermFromString term
 case res of
   Left err -> putStrLn $ "Error while parsing DMTerm from string: " <> show err
   Right term -> typecheckFromDMTerm term

data DoShowLog = DoShowLog DMLogSeverity [DMLogLocation] | DontShowLog

executeTC l r = do
  let (x,logs) = runWriter (runExceptT ((runStateT ((runTCT r)) (Full def def (Right def)))))

  case l of
    (DoShowLog s ls) -> do
        -- we do log a message if
        -- 1. its severity is higher/equal than this one
        --   OR
        -- 2. it was logged below one of the given locations
        let severity = s
        let locations = ls
        let realLogs = getLogMessages logs severity locations
        putStrLn "======================== LOG ========================="
        putStrLn realLogs
        putStrLn "======================== End LOG ====================="
        putStrLn ""
    (DontShowLog) -> return ()

  return x

typecheckFromDMTerm :: DMTerm -> IO ()
typecheckFromDMTerm term = do
  putStrLn "Starting DiffMu!"

  let r = do

        log $ "Checking term   : " <> show term
        -- typecheck the term t5
        let tres = checkSens term def
        let (tres'',_) = runState (extractDelayed def tres) def
        tres' <- tres''
        log $ "Type before constraint resolving: " <> show tres'
        log $ "solving constraints:"
        logPrintConstraints
        solveAllConstraints [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal]
        tres'' <- normalize tres'
        return tres''

        -- a <- newVar
        -- b <- newVar
        -- let (ss :: Sensitivity) = injectVarId (Ln (oneId ⋆! oneId ⋆! a))
        -- a ==! (b ⋆! b)
        -- solveAllConstraints SolveExact
        -- traceM $ "My s is   : " <> show ss
        -- ss' <- normalize ss
        -- traceM $ "After norm: " <> show ss'


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


  -- these are the locations from which the logs will be shown
  let logging_locations = [
        Location_Check
        -- Location_Constraint,
        -- Location_Subst
        -- Location_INC,
        -- Location_MonadicGraph,
         --Location_All
        ]

  x <- executeTC (DoShowLog Force logging_locations) r

  case x of
    Left err -> putStrLn $ "Encountered error: " <> show err
    Right x -> putStrLn $ "Result: " <> show x

  {-
  let x = runExcept (runStateT (runTCT r) (Full def def (Right def)))
  case x of
    Left err -> putStrLn $ "Encountered error: " <> show err
    Right x -> do
      let logs = view (tcstate.logger) (snd x)
      -- we do log a message if
      -- 1. its severity is higher/equal than this one
      --   OR
      -- 2. it was logged below one of the given locations
      let severity = Force
      let locations = []
      let realLogs = getLogMessages logs severity locations
      putStrLn "======================== LOG ========================="
      putStrLn realLogs
      putStrLn "======================== End LOG ====================="
      putStrLn ""
      putStrLn $ "Result: " <> show x
  return ()
-}



