
module Spec.Issues where

import Spec.Base

testIssues pp = do
  test51 pp


test51 pp = describe "issue 53" $ do
  let ex = "function f(x::Integer) :: Priv() \n"
           <>  "(theta, mu) = (100,x) \n"
           <>  "theta + mu \n"
           <>  "end"
      int = NoFun(Numeric (NonConst DMInt))
      ty = Fun([ForAll [] ([int :@ (inftyP)] :->*: int) :@ Just [JuliaType "Integer"]])

  parseEval pp "seems fixed (the example typechecks)" ex (pure ty)




