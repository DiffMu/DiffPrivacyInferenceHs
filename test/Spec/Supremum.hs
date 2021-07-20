
module Spec.Supremum where

import Spec.Base


testSupremum = do
  describe "supremum" $ do
    let testsup (a :: DMTypeOf k) b c = do
          it ("computes sup{" <> show a <> ", " <> show b <> "} = " <> show c) $ do
            (tc $ sn_EW $ supremum a b) `shouldReturn` (c)

    let testsupl (a :: DMTypeOf k) b c = do
          it ("computes sup{" <> show a <> ", " <> show b <> "} = " <> show c) $ do
            (tcl $ sn_EW $ supremum a b) `shouldReturn` (c)

    let twoId = oneId ⋆! oneId

    testsup (DMInt) (DMInt) (Right $ DMInt)
    testsup (DMReal) (DMReal) (Right $ DMReal)

    testsup (NonConst DMInt) (NonConst DMInt) (Right $ NonConst DMInt)
    testsup (NonConst DMInt) (NonConst DMReal) (Right $ NonConst DMReal)

    testsup (Const (twoId) DMInt) (Const (twoId) DMInt) (Right $ Const (twoId) DMInt)
    testsup (Const (twoId) DMInt) (Const (oneId) DMInt) (Right $ NonConst DMInt)

    testsup (NoFun (Numeric (NonConst DMInt)))
            (Fun [ForAll [] ([NoFun (Numeric (NonConst DMInt)) :@ oneId] :->: (NoFun (Numeric (NonConst DMInt)))) :@ Nothing])
            (Left (UnsatisfiableConstraint "[test]"))

  describe "advanced supremum" $ do
    it "breaks down Num wrapped sups" $ do
      let term :: TC ()
          term = do
            a <- newVar
            b <- newVar
            c <- supremum (Numeric a) (Numeric b)
            return ()
          eval = do
            c <- getConstraintsByType (Proxy @(IsSupremum ((DMTypeOf NoFunKind, DMTypeOf NoFunKind) :=: DMTypeOf NoFunKind)))
            d <- getConstraintsByType (Proxy @(IsSupremum ((DMTypeOf NumKind, DMTypeOf NumKind) :=: DMTypeOf NumKind)))
            return (length c , length d)
      (tc $ (sn_EW term) >> eval) `shouldReturn` Right (0,1)

  describe "supremum (with unknown variables)" $ do
    it "does NOT solve 'max{a,Int} = b'" $ do
      let test :: TC _
          test = do
            a <- newVar
            b <- supremum a DMInt
            return (a,b)
      let check (TVar a, TVar b) | a /= b = pure (Right ())
          check x                         = pure (Left x)
      (tcl $ (sn_EW test >>= check)) `shouldReturn` (Right (Right ()))






