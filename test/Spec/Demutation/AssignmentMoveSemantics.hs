
module Spec.Demutation.AssignmentMoveSemantics where

import Spec.Base
import DiffMu.Core.Definitions


testScoping_AssignmentMoveSemantics pp = do
  describe "Variable assignments have move semantics" $ do
    testAMS01 pp
    testAMS02 pp

  describe "Loops have special move checking for captures" $ do
    testAMS03 pp

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
           \   clone(x)           \n\
           \ end                  "

  let exd = " function f(a)       \n\
           \   x = a              \n\
           \   a = x              \n\
           \   clone(a)           \n\
           \ end                  "

      intc c = NoFun(Numeric (Num DMInt (Const (constCoeff c))))
      ty = Fun([([intc (Fin 3) :@ oneId] :->: intc (Fin 3)) :@ Just [JTAny]])


  parseEvalFail pp "01a errors (mutation after move is not allowed)" exa (DemutationMovedVariableAccessError "")
  parseEvalFail pp "01b errors (value after move is not allowed)" exb (DemutationMovedVariableAccessError "")
  parseEvalUnify pp "01c succeeds (using corect value after move is allowed)" exc (pure ty)
  parseEvalUnify pp "01d succeeds (double move is allowed)" exd (pure ty)



testAMS02 pp = do
  let exa = " function f(a,b)      \n\
           \   (x,y) = (a,b)       \n\
           \   internal_mutate!(a)   \n\
           \ end                  "

  let exb = " function f(a,b)     \n\
            \   (y,z) = (a,b)     \n\
            \   (v,w) = y         \n\
            \   internal_mutate!(v)  \n\
            \ end                 "


  let exc = " function f(a,b)     \n\
            \   y = a             \n\
            \   (v,w) = y         \n\
            \   internal_mutate!(v)  \n\
            \ end                 "

  parseEvalFail pp "02a errors (mutation after tuple move is not allowed)" exa (DemutationMovedVariableAccessError "")
  parseEvalFail pp "02b errors (mutation of tuple part is not allowed)" exb (DemutationSplitMutatingArgumentError "")
  parseEvalFail pp "02c errors (mutation of tuple part is not allowed)" exc (DemutationSplitMutatingArgumentError "")


testAMS03 pp = do
  let exa = "function test(a,b)  \n\
            \   c = 1            \n\
            \   for i in 1:10    \n\
            \     a = c          \n\
            \   end              \n\
            \   a                \n\
            \ end                "

  let exb = " function test(a,b)  \n\
            \   c = 1             \n\
            \   for i in 1:10     \n\
            \     a = c           \n\
            \     c = a           \n\
            \   end               \n\
            \   c                 \n\
            \ end                 "

  let exc = " function test(a,b)             \n\
            \    x = 0                       \n\
            \    for i in 1:10               \n\
            \      if i == 0                 \n\
            \        x = a                   \n\
            \      else                      \n\
            \        internal_mutate!(a)     \n\
            \      end                       \n\
            \    end                         \n\
            \    x                           \n\
            \ end                            "


  parseEvalFail pp "01a errors (moving a pre-existing variable into a capture is not allowed)" exa (DemutationMovedVariableAccessError "")
  parseEvalFail pp "01b errors (double moving is not allowed)" exb (DemutationMovedVariableAccessError "")
  parseEvalFail pp "01c errors (moving in if-branches is not allowed)" exc (DemutationError "")
