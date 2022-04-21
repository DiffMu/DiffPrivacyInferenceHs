
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
--import DiffMu.Parser.DMTerm.FromString
import DiffMu.Parser.FromString
import DiffMu.Parser.JExprToDMTerm

import DiffMu.Typecheck.JuliaType

import Algebra.PartialOrd

import           Foreign.C.String

import Debug.Trace
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

run :: IO ()
run = putStrLn "Hello?"


typecheckFromString_DMTerm_Detailed :: String -> String -> IO ()
typecheckFromString_DMTerm_Detailed term rawsource = do
 let (res) = parseJTreeFromString term >>= parseJExprFromJTree
 case (res) of
   Left err -> putStrLn $ "Error while parsing DMTerm from string: " <> show err
   Right (term,files) -> do
     rs <- (rawSourceFromString rawsource files)
    --  putStrLn $ ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"
    --  putStrLn $ show rs
    --  putStrLn $ ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"
     typecheckFromJExpr_Detailed term rs

typecheckFromString_DMTerm_Simple :: String -> String -> IO ()
typecheckFromString_DMTerm_Simple term rawsource = do
 let res = parseJTreeFromString term >>= parseJExprFromJTree
 case res of
   Left err -> putStrLn $ "Error while parsing DMTerm from string: " <> show err
   Right (term,files) -> do
     rs <- (rawSourceFromString rawsource files)
    --  putStrLn $ ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"
    --  putStrLn $ show rs
    --  putStrLn $ ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"
     typecheckFromJExpr_Simple term rs

data DoShowLog = DoShowLog DMLogSeverity [DMLogLocation] | DontShowLog

executeTC l r rawsource = do
  let (x,logs) = runWriter (runReaderT (runExceptT ((runStateT ((runTCT r)) (Full def def (Right def))))) rawsource)

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

    (DontShowLog) -> return ()

  let (errs,res) = case (getErrors logs, x) of
                    (errs, Left err) -> (err:errs, Nothing)
                    (errs, Right res) -> (errs, Just res)


  putStrLn "======================== Errors ====================="
  TIO.putStrLn (getErrorMessage rawsource errs)
  putStrLn "======================== End Errors ====================="

  return (errs,res)

  -- case errs of
  --   [] -> return x
  --   (x:xs) -> return (Left x)

typecheckFromJExprWithPrinter :: ((DMMain,Full (DMPersistentMessage TC)) -> Text) -> DoShowLog -> JExpr -> RawSource -> IO ()
typecheckFromJExprWithPrinter printer logoptions term rawsource = do
  let r = do

        log $ "Checking term   : " <> show term

        term' <- parseDMTermFromJExpr term >>= (liftNewLightTC . preprocessAll)

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
        tres''' <- solveAndNormalize ExactNormalization [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal] tres'
        tres'''' <- solveAndNormalize SimplifyingNormalization [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal] tres'''
        return tres''''

  x <- executeTC logoptions r rawsource

  case x of
    (_, Nothing) -> putStrLn $ "No type could be inferred"
    (_, Just x) -> TIO.putStrLn $ printer x


-- (DoShowLog Warning logging_locations)

typecheckFromJExpr_Simple :: JExpr -> RawSource -> IO ()
typecheckFromJExpr_Simple term rawsource = do
  let printer (ty, full) =
        let cs = _anncontent (_constraints (_meta full))
            cs_simple :: CtxStack IxSymbol (Watched (Solvable GoodConstraint GoodConstraintContent MonadDMTC)) = fmap (\(ConstraintWithMessage a m) -> a) cs
            pcs = runReader (showLocated cs_simple) rawsource
            cstring = case isEmptyDict cs of
                           True -> ""
                           _ -> "Constraints:\n" <> pcs
            fcs = (_failedConstraints (_meta full))
            pfcs = runReader (showLocated fcs) rawsource
            fcstring = case isEmptyDict fcs of
                           True -> ""
                           _ -> red "CHECKING FAILED" <> ": The following constraints are not satisfiable:\n"
                                <> pfcs
        in do
           "\n---------------------------------------------------------------------------\n"
           <> "Type:\n" <> runReader (showLocated ty) rawsource
           <> "\n" <> T.pack (showPretty (_userVars (_meta full)))
           <> "\n---------------------------------------------------------------------------\n"
           <> cstring <> "\n"
           <> fcstring
  typecheckFromJExprWithPrinter printer (DontShowLog) term rawsource

typecheckFromJExpr_Detailed :: JExpr -> RawSource -> IO ()
typecheckFromJExpr_Detailed term rawsource = do

  let logging_locations = [
        -- Location_Check,
        Location_Constraint,
        Location_PrePro_Demutation,
        Location_PreProcess,
        -- Location_Subst
        -- Location_INC,
        Location_MonadicGraph
         --Location_All
        ]
  let printer (ty, full) =
        "\n---------------------------------------------------------------------------\n"
        <> "Type:\n" <> runReader (showLocated ty) rawsource
        <> "\n---------------------------------------------------------------------------\n"
        <> "Monad state:\n" <> T.pack (show full)

  typecheckFromJExprWithPrinter printer (DoShowLog Debug logging_locations) term rawsource


