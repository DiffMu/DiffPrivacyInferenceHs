
module Spec.TypecheckingExamples where

import Spec.Base


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






