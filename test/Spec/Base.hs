
module Spec.Base
  (module All
  , tc , tcl , tcb , sn , sn_EW , parseEval , parseEval_l , parseEvalUnify , parseEvalUnify_l , parseEvalSimple, parseEvalFail
  , parseEvalUnify_customCheck
  , parseEvalString , parseEvalString_l , parseEvalString_customCheck
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
import DiffMu.Typecheck.Preprocess.FLetReorder
import DiffMu.Typecheck.Preprocess.Demutation
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.All
import DiffMu.Runner as All
import DiffMu.Parser.Expr.FromString as All
import DiffMu.Parser.Expr.FromString
import DiffMu.Parser.Expr.JExprToDMTerm

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
  solveAllConstraints [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal]
  normalize x'
  solveAllConstraints [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal]
  normalize x'

sn_EW :: Normalize TC a => TC a -> TC a
sn_EW x = do
  x' <- x
  solveAllConstraints [SolveExact,SolveAssumeWorst]
  normalize x'
  solveAllConstraints [SolveExact,SolveAssumeWorst]
  normalize x'
  solveAllConstraints [SolveExact,SolveAssumeWorst]
  normalize x'


----------------------------------------------
-- without custom constraint evaluation function
parseEvalSimple p term expected =
  parseEval p ("Checks '" <> term <> "' correctly") term expected

parseEvalFail a b c f = parseEval_b False a b c (TestByFail f)

parseEval parse desc term expected = parseEval_b False parse desc term (TestByEquality expected)
parseEval_l parse desc term expected = parseEval_b True parse desc term (TestByEquality expected)


parseEvalUnify parse desc term expected   = parseEval_b False parse desc term (TestByUnification expected)
parseEvalUnify_l parse desc term expected = parseEval_b True  parse desc term (TestByUnification expected)

parseEvalString parse desc term expected   = parseEval_b False parse desc term (TestByString expected)
parseEvalString_l parse desc term expected = parseEval_b True  parse desc term (TestByString expected)

----------------------------------------------
-- with custom TC/constraint evaluation function

parseEvalFail_customCheck a b c f = parseEval_b False a b c (TestByFail f)

parseEval_customCheck parse desc term expected = parseEval_b_customCheck False parse desc term (TestByEquality expected)
parseEval_l_customCheck parse desc term expected = parseEval_b_customCheck True parse desc term (TestByEquality expected)

parseEvalUnify_customCheck parse desc term expected   = parseEval_b_customCheck False parse desc term (TestByUnification expected)
parseEvalUnify_l_customCheck parse desc term expected = parseEval_b_customCheck True  parse desc term (TestByUnification expected)

parseEvalString_customCheck parse desc term expected   = parseEval_b_customCheck False parse desc term (TestByString expected)
parseEvalString_l_customCheck parse desc term expected = parseEval_b_customCheck True  parse desc term (TestByString expected)




data ComparisonStyle = CompareByEqual | CompareByUnification
data TestExpectation b = ExpectSuccess | ExpectFail b

data TestBy = TestByEquality (TC DMMain) | TestByUnification (TC DMMain) | TestByString (String, String) | TestByFail DMException


parseEval_b dolog parse desc term (testBy :: TestBy) =
  parseEval_b_customCheck dolog parse desc term testBy customTCCheck
  where
    customTCCheck = do
      ctrs <- getAllConstraints
      case ctrs of
        [] -> pure $ Right ()
        cs -> pure $ Left (show cs)


parseEval_b_customCheck dolog parse desc term (testBy :: TestBy) customTCCheck =
  it desc $ do
    term' <- parse term

    let res = parseJTreeFromString term' >>= parseJExprFromJTree >>= parseDMTermFromJExpr

    let term'' :: TC DMMain
        term'' = case res of
                   Left err -> error $ "Error while parsing DMTerm from string: " <> show err
                   Right res''  ->
                     do
                            (res) <- liftNewLightTC (preprocessAll res'' )
                            -- res <- preprocessDMTerm res'
                            let tres = checkSens res def
                                  -- (do
                                  --          case dolog of
                                  --            True -> traceM $ "preprocessed term:\n" <> show res
                                  --            False -> pure ()

                                  --          inferredT_Delayed <- checkSens res def
                                  --          return $ do
                                  --            inferredT <- inferredT_Delayed
                                  --            return inferredT
                                  --            -- expectedT <- expected
                                  --            -- unify inferredT expectedT
                                  --      )
                            let (tres'',_) = runState (extractDelayed def tres) def
                            tres''
           -- pure $ (tres'')

    let correctEquality (expected) result = do
          expectedT <- expected
          customCheckResult <- customTCCheck
          case expectedT == result of
            True ->
              -- and additionally if the constraints are empty
              return customCheckResult
            False -> pure $ Left ("expected type " <> show expectedT <> " but got " <> show result)

        correctUnification (expected) result = do
          expectedT <- expected
          customCheckResult <- customTCCheck

          -- we check whether our result is as expected
          unify result expectedT
          solveAllConstraints [SolveExact]

          -- and additionally if the constraints are empty
          return customCheckResult

        correctString (expectedType, expectedConstrs) result = do
          let actualType = show result

          full <- get
          let actualConstrs = show (_constraints (_meta full))

          case (actualType == expectedType, actualConstrs == expectedConstrs) of
            (True,True) -> return $ Right ()
            (_,_) -> return $ Left (actualType, actualConstrs)

    case testBy of
      TestByEquality expected -> (tcb dolog $ (sn term'' >>= correctEquality expected)) `shouldReturn` (Right (Right ()))
      TestByUnification expected -> (tcb dolog $ (sn term'' >>= correctUnification expected)) `shouldReturn` (Right (Right ()))
      TestByString expected -> (tcb dolog $ (sn term'' >>= correctString (expected))) `shouldReturn` (Right (Right ()))
      TestByFail f  -> (tcb dolog $ (sn term'')) `shouldReturn` (Left f)


    -- let correct testBy result = do
    --       -- first, get all constraints (these are exactly the ones which returned from the checking)
    --       -- ctrs <- getAllConstraints
    --       customCheckResult <- customTCCheck

    --       -- we check whether our result is as expected
    --       expectedT <- expected
    --       case compstyle of
    --         CompareByUnification -> do
    --           unify result expectedT
    --           solveAllConstraints [SolveExact]

    --           -- and additionally if the constraints are empty
    --           return customCheckResult 
    --           -- case ctrs of
    --           --   [] -> pure $ Right ()
    --           --   cs -> pure $ Left (show cs)

    --         CompareByEqual -> do
    --           case expectedT == result of
    --             True ->
    --               -- and additionally if the constraints are empty
    --               return customCheckResult
    --               -- case ctrs of
    --               --   [] -> pure $ Right ()
    --               --   cs -> pure $ Left (show cs)
    --             False -> pure $ Left ("expected type " <> show expectedT <> " but got " <> show result)


    -- (tcb dolog $ (sn term'' >>= correct testBy)) `shouldReturn` (Right (Right ()))
    -- case failOrSuccess of
      -- ExpectSuccess -> (tcb dolog $ (sn term'' >>= correct testBy)) `shouldReturn` (Right (Right ()))
      -- ExpectFail f  -> (tcb dolog $ (sn term'' >>= correct testBy)) `shouldReturn` (Left f)

