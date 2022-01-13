
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
    testLNA02 pp

testLNA01 pp = do
  let ex = " function test()             \n\
           \   a = new_box(1)            \n\
           \   map_box!(x -> x + 2, a)   \n\
           \   get_box(a)                \n\
           \ end                         "

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intc (Fin 3)) :@ Just []])

  parseEval pp "01 works (simple mutation via boxes)" ex (pure ty)

testLNA02 pp = do
  let exa = " function test()               \n\
           \   m = new_box(3)              \n\
           \   x = m                       \n\
           \   function f(x)               \n\
           \     a = x                     \n\
           \     map_box!(y -> y * 2, a)   \n\
           \   end                         \n\
           \   f(x)                        \n\
           \   x                           \n\
           \ end                           "

      intboxc c = NoFun(DMBox $ Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intboxc (Fin 6)) :@ Just []])

  parseEval pp "02a works (mutation after renaming)" exa (pure ty)

  let exb = " function test()                 \n\
            \   m = new_box(3)                \n\
            \   x = (m,m)                     \n\
            \   function f(x)                 \n\
            \     (a,b) = x                   \n\
            \     map_box!(y -> y * 2, a)     \n\
            \   end                           \n\
            \   f(x)                          \n\
            \   x                             \n\
            \ end                             "

      intboxc c = DMBox $ Numeric (Const (constCoeff c) DMInt)
      ty = Fun([([] :->: NoFun (DMTup [intboxc (Fin 6), intboxc (Fin 6)])) :@ Just []])

  parseEval pp "02b works (mutation after going through tuple)" exb (pure ty)

