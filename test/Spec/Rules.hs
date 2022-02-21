
module Spec.Rules where

import Spec.Base


testCheck_Rules = do
  describe "rules-privacy-slet" $ do
    it "forwards inner type correctly" $ do
      let term = SLet ((UserTeVar ((UserProcVar $ Symbol "x"))) :- JTAny) (Sng 1.0 (JTReal)) (Ret (Var (((UserTeVar (UserProcVar $ Symbol "x"))) :- JTAny)))
      let f = checkPriv def term
      -- do
      --       let tres = checkPriv term def
      --       -- let (tres'',_) = runState (extractDelayed def tres) def
      --       -- tres''
      --       tres
      (tc $ sn $ f) `shouldReturn` (Right $ NoFun (Numeric (MkNum DMReal (MkConst (oneId)))))


