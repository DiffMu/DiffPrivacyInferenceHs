
module Spec.DemutationLNA where

import DiffMu.Typecheck.Preprocess.Demutation
import DiffMu.Typecheck.Preprocess.FLetReorder
import DiffMu.Typecheck.Preprocess.Demutation
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.All
import Spec.Base


-----------------------------------------------------
-- Local Name Aliasing demutation (#158)

testDemutationLNA pp = do
  describe "Local Name Aliasing demutation. (#158)" $ do
    testLNA01 pp
    -- testDScope02 pp
    -- testDScope03 pp

testLNA01 pp = do
  let ex = " function test()             \n\
           \   a = new_box(1)            \n\
           \   map_box!(x -> x + 2, a)   \n\
           \   get_box(a)                \n\
           \ end                         "

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intc (Fin 3)) :@ Just []])

  parseEval pp "01 works (simple mutation via boxes)" ex (pure ty)

