
module Spec.Subtyping where

import Spec.Base

testSubtyping = do
  let testsub x (a :: DMTypeOf k) b c = do
        it ("computes " <> show a <> " ≤ " <> show b <> " as [" <> show c <> "]") $ do
          (tcb x $ do
              sn_EW (a ≤! b)
              res <- (getUnsolvedConstraintMarkNormal [SolveExact])
              return (fmap (\_ -> ()) res)
            )
            `shouldReturn` (c)

  describe "generic subtyping" $ do
    it "does not resolve 'a ≤ b'." $ do
      let test0 = do
            (a :: DMTypeOf BaseNumKind) <- newVar
            b <- newVar
            a ⊑! b
            return (a,b)
      let correct (TVar a,TVar b) | a /= b = pure (Right ())
          correct x                        = pure (Left x)
      (tc $ (sn_EW test0 >>= correct)) `shouldReturn` (Right (Right ()))


  describe "subtyping of BaseNumKind/NumKind" $ do
    testsub False DMInt DMReal (Right Nothing)
    testsub False DMReal DMInt (Left (UnsatisfiableConstraint "[test]"))

  describe "subtyping of tuples" $ do
    let nci1 = (Numeric (Const oneId DMInt))
        nci2 = (Numeric (Const (constCoeff (Fin 2)) DMInt))
        nnr  = Numeric (NonConst DMReal)

    testsub False (NoFun nci1) (NoFun nnr) (Right Nothing)
    testsub False (DMTup [nci1,nci2]) (DMTup [nci1,nnr]) (Right Nothing)
    testsub False (DMTup [nci1,nci2]) (DMTup [nci2,nnr]) (Left (UnsatisfiableConstraint "[test]"))
    testsub False (DMTup [nnr,nci2]) (DMTup [nci2,nnr]) (Left (UnsatisfiableConstraint "[test]"))
    testsub False (DMTup [nnr,nci2]) (nnr) (Left (UnsatisfiableConstraint "[test]"))


testSubtyping_MaxMinCases = do
  describe "subtyping (paths with max/min cases)" $ do
    it "resolves 'a ≤ Int'." $ do
      let test0 = do
            a <- newVar
            a ⊑! DMInt
            return (a)
      (tc $ (sn_EW test0)) `shouldReturn` (Right DMInt)

    it "resolves 'Real ≤ a'." $ do
      let test0 = do
            a <- newVar
            DMReal ⊑! a
            return (a)
      (tc $ (sn_EW test0)) `shouldReturn` (Right DMReal)

    it "does NOT resolve 'Int ≤ a'." $ do
      let test0 = do
            a <- newVar
            DMInt ⊑! a
            return a
      let isTVar (TVar x) = pure (Right ())
          isTVar a        = pure (Left a)
      (tc $ (sn_EW test0) >>= isTVar) `shouldReturn` (Right (Right ()))

    it "does NOT resolve 'a ≤ Real'." $ do
      let test0 = do
            a <- newVar
            a ⊑! DMReal
            return a
      let isTVar (TVar x) = pure (Right ())
          isTVar a        = pure (Left a)
      (tc $ (sn_EW test0) >>= isTVar) `shouldReturn` (Right (Right ()))

    it "resolves 'a ≤ Int[2]' inside NoFun" $ do
      let ty = NoFun (Numeric (Const (constCoeff (Fin 2)) DMInt))
      let test0 = do
            a <- newVar
            a ⊑! ty
            return a
      (tc $ sn_EW test0) `shouldReturn` (Right ty)

    it "partially resolves 'a ≤ (Int[2],Real[--])'" $ do
      let ty1 = (Numeric (Const (constCoeff (Fin 2)) DMInt))
          ty2 = (Numeric (NonConst DMReal))
          ty = DMTup [ty1 , ty2]
      let test0 = do
            a <- newVar
            a ⊑! ty
            return a
      let correct :: (DMType) -> TC _
          correct ((DMTup [Numeric (Const s DMInt), Numeric (TVar y)])) = pure $ Right s
          correct r                                                     = pure $ Left r
      (tc $ sn_EW test0 >>= correct) `shouldReturn` (Right (Right (constCoeff (Fin 2))))

    it "partially resolves 'a[--] ≤ b' inside NoFun" $ do
      let test0 = do
            a <- newVar
            b <- newVar
            let a'  = NoFun (Numeric (NonConst a))

            a' ⊑! b
            return (a', b)
      let correct :: (DMMain,DMMain) -> TC (Either (DMMain,DMMain) ())
          correct (NoFun (Numeric (NonConst a)), NoFun (Numeric (NonConst b))) | (a /= b) = pure $ Right ()
          correct (x,y)                                                                   = pure $ Left (x,y)
      (tc $ sn_EW test0 >>= correct) `shouldReturn` (Right (Right ()))


testSubtyping_Cycles = do
  describe "subtyping (contracting cycles - only subtyping constraints)" $ do
    it "contracts a two-variable cycle" $ do
      let test0 = do
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b
            b ⊑! a
            return (a,b)
      (tc $ (sn test0 >>= (\(a,b) -> return (a == b)))) `shouldReturn` (Right True)

    it "contracts a cycle that has top in it" $ do
      let test01 = do
            (a :: DMTypeOf BaseNumKind) <- newVar
            b <- newVar
            c <- newVar
            d <- newVar
            e <- newVar
            a <- supremum DMReal e -- use supremum here bc the constraint Real <= a would be resolved by a special case
            a ⊑! b
            b ⊑! c
            c ⊑! d
            return (a,b)
      (tc $ (sn test01 >>= (\(a,b) -> return (and [(a == DMReal), (a == b)])))) `shouldReturn` (Right True)

    it "contracts a cycle that has bottom in it" $ do
      let test02 = do
            a <- newVar
            b <- newVar
            c <- newVar
            e <- newVar
            d <- infimum DMInt e -- use inf here bc the constraint d <= Int would be resolved by a special case
            a ⊑! b
            b ⊑! c
            c ⊑! d
            return (a,b)
      (tc $ (sn test02 >>= (\(a,b) -> return (and [(a == DMInt), (a == b)])))) `shouldReturn` (Right True)

    it "contracts a larger cycle with more stuff" $ do
      let test1 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b

            -- the additional variables b ≤ x ≤ y ≤ a
            x <- newVar
            y <- newVar
            b ⊑! x
            x ⊑! y
            y ⊑! a

            -- some more uninteresting things
            z <- newVar
            s <- newVar
            t <- newVar
            z ⊑! x
            s ⊑! t
            a ⊑! t

            -- we are interested in how `a` and `b` turn out
            return (a,b)
      let checkres (a,b) = a == b
      (tc $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right True)

    it "contracts a larger cycle that also has sup/inf constraints" $ do
      let test2 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b

            -- the additional variables b ≤ x ≤ z ≤ y ≤ a
            (x :: DMMain) <- supremum a b
            (y :: DMMain) <- infimum a x
            z <- newVar
            x ⊑! z
            z ⊑! y

            -- we are interested in how `a` and `b` turn out
            return (a,b)
      let checkres (a,b) = a == b
      (tc $ (sn test2 >>= (return . checkres))) `shouldReturn` (Right True)

    it "does not contract a constraint that is not in a cycle" $ do
      let test3 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b

            -- the additional variables b ≤ x ≤ z and y ≤ a
            (x :: DMMain) <- supremum a b
            (y :: DMMain) <- infimum a x
            z <- newVar
            x ⊑! z

            -- we are interested in how `a` and `b` turn out
            return (a,b)
      let checkres (a,b) = not (a == b)
      (tc $ (sn test3 >>= (return . checkres))) `shouldReturn` (Right True)




testSubtyping_ContractEdge = do
  describe "subtyping (contracting edges - only subtyping constraints)" $ do
    it "contracts a single edge" $ do
      let test0 = do
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b
            return (a,b)
      (tc $ (sn test0 >>= (\(a,b) -> return (a == b)))) `shouldReturn` (Right True)

    it "does contract edge if left variable is only bounded from below and right from above" $ do
      let test1 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b

            -- the additional variables x ≤ a ≤ b ≤ y
            x <- newVar
            y <- newVar
            x ⊑! a
            b ⊑! y

            -- we are interested in how `a` and `b` turn out
            return (a,b)
      let checkres (a,b) = a == b
      (tc $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right True)

    it "does NOT contract edge if left variable is bounded from above" $ do
      let test1 = do
            -- main
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b
            -- blocking constraint
            x <- newVar
            a ⊑! x
            return (a,b)
      (tc $ (sn test1 >>= (\(a,b) -> return (a == b)))) `shouldReturn` (Right False)

    it "does NOT contract edge if right variable is bounded from below" $ do
      let test1 = do
            -- main
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b
            -- blocking constraint
            y <- newVar
            y ⊑! b
            return (a,b)
      (tc $ (sn test1 >>= (\(a,b) -> return (a == b)))) `shouldReturn` (Right False)

    it "does NOT contract edge if variable additionally appears in a non subtyping constraint " $ do
      let test1 = do
            -- main
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b
            -- blocking constraint
            (y :: DMMain) <- newVar
            addConstraint (Solvable (IsJuliaEqual (y, a)))
            return (a,b)
      (tc $ (sn test1 >>= (\(a,b) -> return (a == b)))) `shouldReturn` (Right False)

    it "does ONLY contract those edges which are allowed to be contracted" $ do
      let test1 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b

            -- the additional variables x ≤ a ≤ b ≤ y
            x <- newVar
            y <- newVar
            x ⊑! a
            b ⊑! y

            -- blocking constraints for x and y
            (y' :: DMMain) <- newVar
            (x' :: DMMain) <- newVar
            addConstraint (Solvable (IsJuliaEqual (x, x')))
            addConstraint (Solvable (IsJuliaEqual (y, y')))

            -- we are interested in how `a`, `b`, `x`, `y` turn out
            return (x,a,b,y)
      let checkres (x,a,b,y) = and [ a == b
                                   , x /= a
                                   , y /= b ]
      (tc $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right True)

  describe "subtyping (contracting edges - subtyping and sup/inf constraints)" $ do
    it "does contract edge given by supremum" $ do
      let test1 :: TC (DMMain,DMMain,DMMain,DMMain)
          test1 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            (b :: DMMain) <- newVar
            (c :: DMMain) <- supremum a b
            (d :: DMMain) <- infimum a b

            return (d,a,b,c)
      let checkres (d,a,b,c) = (a == c, b == c, a == d, b == d)
      (tc $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right (True,True,True,True))



