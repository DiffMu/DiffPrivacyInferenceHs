
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
import DiffMu.Typecheck.Constraint.IsJuliaEqual
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
  -- x <- executeTC (DoShowLog Force [Location_Constraint , Location_INC, Location_MonadicGraph]) r
  x <- executeTC (DoShowLog Force [Location_Constraint]) r
  return (fst <$> x)


tcb :: Bool -> TC a -> IO (Either DMException a)
tcb True = tcl
tcb False = tc

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

testSubtyping = do
  let testsub x (a :: DMTypeOf k) b c = do
        it ("computes " <> show a <> " ≤ " <> show b <> " as [" <> show c <> "]") $ do
          (tcb x $ do
              sn (a ≤! b)
              res <- (getUnsolvedConstraintMarkNormal SolveExact)
              return (fmap (\_ -> ()) res)
            )
            `shouldReturn` (c)

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
      (tcl $ (sn term) >> eval) `shouldReturn` Right (0,1)



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

            -- the additional variables b ≤ x ≤ z ≤ y ≤ a
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
      (tcl $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right (True,True,True,True))
    -- it "does contract edge if left variable is only bounded from below and right from above" $ do
    --   let test1 = do
    --         -- the interesting variables a ≤ b
    --         (a :: DMMain) <- newVar
    --         b <- newVar
    --         a ⊑! b

    --         -- the additional variables x ≤ a ≤ b ≤ y
    --         x <- newVar
    --         y <- newVar
    --         x ⊑! a
    --         b ⊑! y

    --         -- we are interested in how `a` and `b` turn out
    --         return (a,b)
    --   let checkres (a,b) = a == b
    --   (tc $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right True)

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

parseEval parse desc term (expected :: TC DMMain) =
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
                            expectedT <- expected
                            unify inferredT expectedT
                            return ()
                      )
           pure $ extractDelayed def tres

    (tc $ sn $ term'') `shouldReturn` (Right ())

testCheckSens parse = do
  describe "checkSens" $ do
    parseEvalSimple parse "3 + 7 * 9" (pure $ NoFun (Numeric (Const (constCoeff (Fin 66)) DMInt)))
    parseEvalSimple parse "2.2 * 3"   (pure $ NoFun (Numeric (Const (constCoeff (Fin 6.6000004)) DMReal)))

    let test = "function test(a)\n"
            <> "  a\n"
            <> "end"
    let ty   = do
          τ <- newTVar ""
          return $ Fun([ForAll [SomeK τ] ([TVar τ :@ oneId] :->: TVar τ) :@ Just [JuliaType "Any"]])
    parseEval parse "Checks the identity function" test ty



runAllTests :: (String -> IO String) -> IO ()
runAllTests parse = defaultspec $ do
  testUnification
  testSubtyping
  testSubtyping_Cycles
  testSubtyping_ContractEdge
  testSupremum
  testCheck_Rules
  testCheckSens parse







