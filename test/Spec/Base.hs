
module Spec.Base
  (module All
  , tc , tcl , tcb , sn , sn_EW , parseEval , parseEval_l , parseEvalUnify , parseEvalUnify_l , parseEvalSimple
  )
where

import DiffMu.Prelude as All
import DiffMu.Abstract as All
import DiffMu.Core as All
import DiffMu.Core.TC as All
import DiffMu.Core.Logging as All
import DiffMu.Core.Definitions as All
import DiffMu.Core.Symbolic as All
import DiffMu.Core.Context as All
import DiffMu.Core.DelayedScope as All
import DiffMu.Typecheck.Operations as All
import DiffMu.Typecheck.Subtyping as All
import DiffMu.Typecheck.Typecheck as All
import DiffMu.Typecheck.Constraint.IsJuliaEqual as All
import DiffMu.Runner as All
import DiffMu.Parser.DMTerm.FromString as All

import DiffMu.Typecheck.JuliaType as All

import Algebra.PartialOrd as All

import           Foreign.C.String as All

import Debug.Trace as All


import Test.Hspec as All
import Test.Hspec.Core.Runner as All


tc :: TC a -> IO (Either DMException a)
tc r = do
  x <- executeTC (DontShowLog) r
  return (fst <$> x)

tcl :: TC a -> IO (Either DMException a)
tcl r = do

  x <- executeTC (DoShowLog Force [Location_Constraint , Location_INC, Location_MonadicGraph, Location_Unification]) r
  -- x <- executeTC (DoShowLog Force [Location_Constraint, Location_Subtyping]) r
  return (fst <$> x)


tcb :: Bool -> TC a -> IO (Either DMException a)
tcb True = tcl
tcb False = tc

sn :: Normalize TC a => TC a -> TC a
sn x = do
  x' <- x
  solveAllConstraints [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal]
  -- solveAllConstraints [SolveSpecial,SolveExact,SolveGlobal,SolveFinal]
  normalize x'

sn_EW :: Normalize TC a => TC a -> TC a
sn_EW x = do
  x' <- x
  solveAllConstraints [SolveExact,SolveAssumeWorst]
  normalize x'


parseEvalSimple p term expected =
  parseEval p ("Checks '" <> term <> "' correctly") term expected


parseEval = parseEval_b False CompareByEqual
parseEval_l = parseEval_b True CompareByEqual

parseEvalUnify = parseEval_b False CompareByUnification
parseEvalUnify_l = parseEval_b True CompareByUnification

data ComparisonStyle = CompareByEqual | CompareByUnification

parseEval_b dolog compstyle parse desc term (expected :: TC DMMain) =
  it desc $ do
    term' <- parse term

    let res = pDMTermFromString term'
    term'' <- case res of
      Left err -> error $ "Error while parsing DMTerm from string: " <> show err
      Right res ->
        do let tres = (do
                          inferredT_Delayed <- checkSens res def
                          return $ do
                            inferredT <- inferredT_Delayed
                            return inferredT
                            -- expectedT <- expected
                            -- unify inferredT expectedT
                      )
           let (tres'',_) = runState (extractDelayed def tres) def
           pure $ tres''

    let correct result = do
          -- first, get all constraints (these are exactly the ones which returned from the checking)
          ctrs <- getAllConstraints

          -- we check whether our result is as expected
          expectedT <- expected
          case compstyle of
            CompareByUnification -> do
              unify result expectedT
              solveAllConstraints [SolveExact]

              -- and additionally if the constraints are empty
              case ctrs of
                [] -> pure $ Right ()
                cs -> pure $ Left (show cs)

            CompareByEqual -> do
              case expectedT == result of
                True ->
                  -- and additionally if the constraints are empty
                  case ctrs of
                    [] -> pure $ Right ()
                    cs -> pure $ Left (show cs)
                False -> pure $ Left ("expected type " <> show expectedT <> " but got " <> show result)


    (tcb dolog $ (sn term'' >>= correct)) `shouldReturn` (Right (Right ()))
