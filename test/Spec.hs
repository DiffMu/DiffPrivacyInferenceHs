
module Spec where

import Spec.Base
import Spec.Subtyping
import Spec.Supremum
import Spec.Rules
import Spec.TypecheckingExamples

-- import Test.QuickCheck hiding (Fun)

defaultspec spec = do
  summary <- runSpec spec defaultConfig
  evaluateSummary summary
  --     getArgs
  -- >>= readConfig defaultConfig
  -- >>= withArgs [] . runSpec spec
  -- >>= evaluateSummary


  -- TODO: Use quickcheck
testUnification = do
  describe "unify" $ do
    it "unifies equal types" $ do
      (tc $ unify (DMInt) (DMInt)) `shouldReturn` ((Right DMInt))



runAllTests :: (String -> IO String) -> IO ()
runAllTests parse = defaultspec $ do
  testUnification
  testSubtyping
  testSubtyping_MaxMinCases
  testSubtyping_Cycles
  testSubtyping_ContractEdge
  testSupremum
  testCheck_Rules
  testCheckSens parse




