
module Spec.Demutation.AssignmentMoveSemantics where

import Spec.Base
import DiffMu.Core.Definitions


testScoping_AssignmentMoveSemantics pp = do
  describe "Variable assignments have move semantics" $ do
    testAMS01 pp
    testAMS02 pp

testAMS01 pp = do
  let exa = " function f(a,b)      \n\
           \   x = a              \n\
           \   norm_convert!(a)   \n\
           \ end                  "


  let exb = " function f(a,b)      \n\
           \   x = a               \n\
           \   a                   \n\
           \ end                  "


  let exc = " function f(a)       \n\
           \   x = a              \n\
           \   x+1                \n\
           \ end                  "

  let exd = " function f(a)       \n\
           \   x = a              \n\
           \   a = x              \n\
           \   a+1                \n\
           \ end                  "

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([intc (Fin 3) :@ oneId] :->: intc (Fin 3)) :@ Just [JTAny]])


  parseEvalFail pp "01a errors (mutation after move is not allowed)" exa (DemutationMovedVariableAccessError "")
  parseEvalFail pp "01b errors (value after move is not allowed)" exb (DemutationMovedVariableAccessError "")
  parseEvalUnify pp "01c succeeds (using corect value after move is allowed)" exc (pure ty)
  parseEvalUnify pp "01d succeeds (double move is allowed)" exd (pure ty)



testAMS02 pp = do
  let exa = " function f(a,b)      \n\
           \   (x,y) = (a,b)       \n\
           \   norm_convert!(a)   \n\
           \ end                  "

  let exb = " function f(a,b)     \n\
            \   (y,z) = (a,b)     \n\
            \   (v,w) = y         \n\
            \   norm_convert!(v)  \n\
            \ end                 "


  let exc = " function f(a,b)     \n\
            \   y = a             \n\
            \   (v,w) = y         \n\
            \   norm_convert!(v)  \n\
            \ end                 "

  parseEvalFail pp "02a errors (mutation after tuple move is not allowed)" exa (DemutationMovedVariableAccessError "")
  parseEvalFail pp "02b errors (mutation of tuple part is not allowed)" exb (DemutationError "")
  parseEvalFail pp "02c errors (mutation of tuple part is not allowed)" exc (DemutationError "")

