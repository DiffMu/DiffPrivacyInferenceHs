
module Spec.Rules where

import Spec.Base


testCheck_Rules = do
  describe "rules-privacy-slet" $ do
    it "forwards inner type correctly" $ do
      let term = SLet (Symbol "x" :- JTAny) (Sng 1.0 (JuliaType "Real")) (Var (Symbol "x") JTAny)
      let f = do
            let tres = checkPriv term def
            extractDelayed def tres
      (tc $ sn $ f) `shouldReturn` (Right $ NoFun (Numeric (Const (oneId) DMReal)))


