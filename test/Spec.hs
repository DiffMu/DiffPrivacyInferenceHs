
module Spec where

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

import DiffMu.Typecheck.JuliaType

import Algebra.PartialOrd

import           Foreign.C.String

import Debug.Trace


import Test.Hspec
import Test.Hspec.Core.Runner
import Test.QuickCheck

defaultspec spec = do
  summary <- runSpec spec defaultConfig
  evaluateSummary summary
  --     getArgs
  -- >>= readConfig defaultConfig
  -- >>= withArgs [] . runSpec spec
  -- >>= evaluateSummary



tc :: TC a -> Either DMException a
tc r = fst <$>
  runExcept (runStateT (runTCT r) (Full def def (Right def)))


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
      (tc $ unify (DMInt) (DMInt)) `shouldBe` ((Right DMInt))


testSupremum = do
  describe "supremum" $ do
    let testsup (a :: DMTypeOf k) b c = do
          it ("computes sup{" <> show a <> ", " <> show b <> "} = " <> show c) $ do
            (tc $ sn $ supremum a b) `shouldBe` (Right c)

    testsup (NonConst DMInt) (NonConst DMInt) (NonConst DMInt)
    testsup (NonConst DMInt) (NonConst DMReal) (NonConst DMReal)

    testsup (Const (oneId ⋆! oneId) DMInt) (Const (oneId) DMInt) (NonConst DMInt)


runAllTests :: IO ()
runAllTests = defaultspec $ do
  testUnification
  testSupremum







