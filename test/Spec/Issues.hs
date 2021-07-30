
module Spec.Issues where

import Spec.Base

testIssues pp = do
  test25 pp
  test51 pp

test25 pp = describe "issue 25" $ do
  let ex = " function test() \n\
           \   function a(b) \n\
           \       b + b     \n\
           \   end           \n\
           \   a(1)          \n\
           \ end"

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([ForAll [] ([] :->: intc (Fin 2)) :@ Just []])

  parseEval pp "seems fixed (the example typechecks)" ex (pure ty)


test51 pp = describe "issue 53" $ do
  let ex = "function f(x::Integer) :: Priv() \n"
           <>  "(theta, mu) = (100,x) \n"
           <>  "theta + mu \n"
           <>  "end"
      int = NoFun(Numeric (NonConst DMInt))
      ty = Fun([ForAll [] ([int :@ (inftyP)] :->*: int) :@ Just [JuliaType "Integer"]])

  parseEval pp "seems fixed (the example typechecks)" ex (pure ty)




