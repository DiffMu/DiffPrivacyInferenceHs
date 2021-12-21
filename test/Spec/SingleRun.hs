
module Spec.SingleRun where

import Spec.Base

testSingleRun p = do
  describe "supremum" $ do
    it "solves 'max{a,Real} = b' since from Real there is only 1 reflexive path" $ do
      let test :: TC _
          test = do
            a <- newVar
            b <- supremum a DMReal
            return (a,b)
      let check :: (DMTypeOf BaseNumKind, DMTypeOf BaseNumKind) -> TC _
          check (TVar a, DMReal) = pure (Right ())
          check x                = pure (Left x)
      (tcl $ (sn_EW test >>= check)) `shouldReturn` (Right (Right ()))

