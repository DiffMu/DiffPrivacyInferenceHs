
module Spec.Demutation where

import DiffMu.Typecheck.Preprocess.Demutation
import DiffMu.Typecheck.Preprocess.FLetReorder
import DiffMu.Typecheck.Preprocess.Demutation
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.All
import Spec.Base


testDemutation pp = do
  describe "Demutation Semi SSA (new names for mutated variables)" $ do
    testDemutation_SemiSSA pp


testDemutation_SemiSSA pp = do

  let exa = " function f(a)          \n\
           \   internal_mutate!(a)   \n\
           \   internal_mutate!(a)   \n\
           \   return                \n\
           \ end                     "

  let exb = " function test(a,b,c)   \n\
            \   internal_mutate!(a)  \n\
            \   internal_mutate!(a)  \n\
            \   internal_mutate!(a)  \n\
            \   a = b                \n\
            \   internal_mutate!(a)  \n\
            \   internal_mutate!(a)  \n\
            \   a = 2                \n\
            \   internal_mutate!(a)  \n\
            \   return               \n\
            \ end                    "


      intc c = NoFun(Numeric (Num DMInt (Const (constCoeff c))))
      intnc = NoFun(Numeric (Num DMInt NonConst))
      intnc' = (Numeric (Num DMInt NonConst))

      tya = Fun([([intnc :@ (constCoeff $ Fin 4)] :->: intnc) :@ Just [JTAny]])
      tyb = Fun([([intnc :@ (constCoeff $ Fin 8), intnc :@ (constCoeff $ Fin 4), intnc :@ zeroId] :->: (NoFun $ DMTup [intnc',intnc'])) :@ Just [JTAny, JTAny, JTAny]])

  parseEvalUnify pp "variant a succeeds (sanity test)" exa (pure tya)
  parseEvalUnify pp "variant b succeeds (same variable name for different args)" exb (pure tyb)
  return ()



