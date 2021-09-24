
module Spec where

import Spec.Base
import Spec.Subtyping
import Spec.Supremum
import Spec.Rules
import Spec.Scoping
import Spec.TypecheckingExamples
import Spec.Unsafe
import Spec.Unification
import Spec.Issues
import Spec.Demutation

-- import Test.QuickCheck hiding (Fun)

defaultspec spec = do
  summary <- runSpec spec defaultConfig
  evaluateSummary summary
  --     getArgs
  -- >>= readConfig defaultConfig
  -- >>= withArgs [] . runSpec spec
  -- >>= evaluateSummary




runAllTests :: (String -> IO String) -> IO ()
runAllTests parse = defaultspec $ do
  -- testUnsafe
  -- testUnification
  -- testSubtyping
  -- testSubtyping_MaxMinCases
  -- testSubtyping_Cycles
  -- testSubtyping_ContractEdge
  -- testSupremum
  -- testCheck_Rules
  -- testScoping parse
  -- testCheckSens parse
  -- testIssues parse
  testDemutation




