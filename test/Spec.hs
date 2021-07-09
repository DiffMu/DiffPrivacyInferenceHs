
module Spec where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Logging
import DiffMu.Core.Definitions
import DiffMu.Core.Symbolic
import DiffMu.Core.Context
import DiffMu.Core.DelayedScope
import DiffMu.Typecheck.Operations
import DiffMu.Typecheck.Subtyping
import DiffMu.Typecheck.Typecheck
import DiffMu.Runner
import DiffMu.Parser.DMTerm.FromString

import DiffMu.Typecheck.JuliaType

import Algebra.PartialOrd

import           Foreign.C.String

import Debug.Trace


import Test.Hspec
import Test.Hspec.Core.Runner
import Test.QuickCheck hiding (Fun)

defaultspec spec = do
  summary <- runSpec spec defaultConfig
  evaluateSummary summary
  --     getArgs
  -- >>= readConfig defaultConfig
  -- >>= withArgs [] . runSpec spec
  -- >>= evaluateSummary



tc :: TC a -> IO (Either DMException a)
tc r = do
  x <- executeTC (DontShowLog) r
  return (fst <$> x)

tcl :: TC a -> IO (Either DMException a)
tcl r = do
  x <- executeTC (DoShowLog Force [Location_Constraint , Location_INC, Location_MonadicGraph]) r
  return (fst <$> x)


sn :: Normalize TC a => TC a -> TC a
sn x = do
  x' <- x
  solveAllConstraints SolveExact
  solveAllConstraints SolveAssumeWorst
  normalize x'


  -- TODO: Use quickcheck
testUnification = do
  describe "unify" $ do
    it "unifies equal types" $ do
      (tc $ unify (DMInt) (DMInt)) `shouldReturn` ((Right DMInt))


testSupremum = do
  describe "supremum" $ do
    let testsup (a :: DMTypeOf k) b c = do
          it ("computes sup{" <> show a <> ", " <> show b <> "} = " <> show c) $ do
            (tc $ sn $ supremum a b) `shouldReturn` (c)

    let testsupl (a :: DMTypeOf k) b c = do
          it ("computes sup{" <> show a <> ", " <> show b <> "} = " <> show c) $ do
            (tcl $ sn $ supremum a b) `shouldReturn` (c)

    let twoId = oneId ⋆! oneId

    testsup (NonConst DMInt) (NonConst DMInt) (Right $ NonConst DMInt)
    testsup (NonConst DMInt) (NonConst DMReal) (Right $ NonConst DMReal)

    testsup (Const (twoId) DMInt) (Const (twoId) DMInt) (Right $ Const (twoId) DMInt)
    testsup (Const (twoId) DMInt) (Const (oneId) DMInt) (Right $ NonConst DMInt)

    testsup (NoFun (Numeric (NonConst DMInt)))
            (Fun [ForAll [] ([NoFun (Numeric (NonConst DMInt)) :@ oneId] :->: (NoFun (Numeric (NonConst DMInt)))) :@ Nothing])
            (Left (UnsatisfiableConstraint "[test]"))


testCheck_Rules = do
  describe "rules-privacy-slet" $ do
    it "forwards inner type correctly" $ do
      let term = SLet (Symbol "x" :- JTAny) (Sng 1.0 (JuliaType "Real")) (Var (Symbol "x") JTAny)
      let f = do
            let tres = checkPriv term def
            extractDelayed def tres
      (tc $ sn $ f) `shouldReturn` (Right $ NoFun (Numeric (Const (oneId) DMReal)))

parseEvalSimple p term expected =
  parseEval p ("Checks '" <> term <> "' correctly") term expected

parseEval parse desc term expected =
  it desc $ do
    term' <- parse term

    let res = pDMTermFromString term'
    term'' <- case res of
      Left err -> error $ "Error while parsing DMTerm from string: " <> show err
      Right res ->
        do let tres = checkPriv res def
           pure $ extractDelayed def tres

    (tc $ sn $ term'') `shouldReturn` expected

testCheckSens parse = do
  describe "checkSens" $ do
    parseEvalSimple parse "3 + 7 * 9" (Right $ NoFun (Numeric (Const (constCoeff (Fin 66)) DMInt)))
    parseEvalSimple parse "2.2 * 3"   (Right $ NoFun (Numeric (Const (constCoeff (Fin 6.6000004)) DMReal)))

    let test = "function test(a)\n"
            <> "  a\n"
            <> "end"
    parseEval parse "Checks the identity function" test (Right $ NoFun (Numeric (Const (constCoeff (Fin 66)) DMInt)))

      -- let term = "3 + 7 * 9"
      -- term' <- parse term

      -- let res = pDMTermFromString term'
      -- term'' <- case res of
      --   Left err -> error $ "Error while parsing DMTerm from string: " <> show err
      --   Right res ->
      --     do let tres = checkPriv res def
      --        pure $ extractDelayed def tres

      -- (tc $ sn $ term'') `shouldReturn` (Right $ NoFun (Numeric (Const (constCoeff (Fin 66)) DMInt)))


runAllTests :: (String -> IO String) -> IO ()
runAllTests parse = defaultspec $ do
  testUnification
  testSupremum
  testCheck_Rules
  testCheckSens parse







