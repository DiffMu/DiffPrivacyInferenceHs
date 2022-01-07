
module DiffMu.Runner where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Definitions
import DiffMu.Core.Symbolic
import DiffMu.Core.Context
import DiffMu.Core.Logging
import DiffMu.Core.Scope
import DiffMu.Typecheck.Operations
import DiffMu.Typecheck.Subtyping
import DiffMu.Typecheck.Typecheck
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.All
-- import DiffMu.Typecheck.Preprocess.Demutation
-- import DiffMu.Typecheck.Preprocess.FLetReorder
import DiffMu.Parser.DMTerm.FromString
import DiffMu.Parser.Expr.FromString
import DiffMu.Parser.Expr.JExprToDMTerm

import DiffMu.Typecheck.JuliaType

import Algebra.PartialOrd

import           Foreign.C.String

import Debug.Trace

run :: IO ()
run = putStrLn "Hello?"

typecheckFromString_DMTerm_Detailed :: String -> IO ()
typecheckFromString_DMTerm_Detailed term = do
 let res = parseJTreeFromString term >>= parseJExprFromJTree >>= parseDMTermFromJExpr
 case res of
   Left err -> putStrLn $ "Error while parsing DMTerm from string: " <> show err
   Right term -> typecheckFromDMTerm_Detailed term

typecheckFromString_DMTerm_Simple :: String -> IO ()
typecheckFromString_DMTerm_Simple term = do
 let res = parseJTreeFromString term >>= parseJExprFromJTree >>= parseDMTermFromJExpr
 case res of
   Left err -> putStrLn $ "Error while parsing DMTerm from string: " <> show err
   Right term -> typecheckFromDMTerm_Simple term

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

typecheckFromDMTermWithPrinter :: _ -> DoShowLog -> MutDMTerm -> IO ()
typecheckFromDMTermWithPrinter printer logoptions term = do
  let r = do

        log $ "Checking term   : " <> show term

        term' <- liftNewLightTC (preprocessAll term)


        -- let tres = checkSens (term') def
        tres' <- checkSens def (term')
        -- let tres'' = tres
        -- let (tres'',_) = runState (runTCT tres) def
        -- tres' <- case tres'' of
        --            Nothing -> internalError "The result of typechecking was a non-applied later value.\nFrom this, no type information can be extracted."
        --            Just a -> a


        -- log $ "Type before constraint resolving: " <> show tres'
        -- logForce $ "================================================"
        -- logForce $ "before solving constraints (1)"
        -- logPrintConstraints
        -- solveAllConstraints [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal]
        -- tres'' <- normalize tres'
        -- logForce $ "================================================"
        -- logForce $ "before solving constraints (2)"
        -- logPrintConstraints
        -- solveAllConstraints [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal]
        -- tres''' <- normalize tres''
        -- logForce $ "================================================"
        -- logForce $ "before solving constraints (3)"
        -- logPrintConstraints
        tres''' <- solveAndNormalize [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal] tres'
        return tres'''

  x <- executeTC logoptions r

  case x of
    Left err -> putStrLn $ "Encountered error: " <> show err
    Right x -> putStrLn $ printer x


-- (DoShowLog Warning logging_locations)

typecheckFromDMTerm_Simple :: MutDMTerm -> IO ()
typecheckFromDMTerm_Simple term = do
  let printer (ty, full) =
        "\n---------------------------------------------------------------------------\n"
        <> "Type:\n" <> showPretty ty
        <> "\n---------------------------------------------------------------------------\n"
        <> "Constraints:\n" <> show (_constraints (_meta full))
  typecheckFromDMTermWithPrinter printer (DontShowLog) term

typecheckFromDMTerm_Detailed :: MutDMTerm -> IO ()
typecheckFromDMTerm_Detailed term = do

  let logging_locations = [
        -- Location_Check,
        -- Location_Constraint,
        Location_PrePro_Demutation
        -- Location_Subst
        -- Location_INC,
        -- Location_MonadicGraph,
         --Location_All
        ]
  let printer (ty, full) =
        "\n---------------------------------------------------------------------------\n"
        <> "Type:\n" <> show ty
        <> "\n---------------------------------------------------------------------------\n"
        <> "Monad state:\n" <> show full

  typecheckFromDMTermWithPrinter printer (DoShowLog Debug logging_locations) term


