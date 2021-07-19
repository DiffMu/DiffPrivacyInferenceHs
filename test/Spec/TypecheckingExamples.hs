
module Spec.TypecheckingExamples where

import Spec.Base

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



