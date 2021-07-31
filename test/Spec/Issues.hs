
module Spec.Issues where

import Spec.Base

testIssues pp = do
  test25 pp
  test51 pp
  test58 pp

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


test58 pp = describe "issue 58" $ do
  let ex_1 = " function test()                     \n\
                \    function f()                  \n\
                \        a = 3                     \n\
                \        function g(h,z)           \n\
                \            h(z)                  \n\
                \        end                       \n\
                \        function h(b)             \n\
                \            a                     \n\
                \        end                       \n\
                \        a = g(h,a)                \n\
                \        a                         \n\
                \    end                           \n\
                \    f()                           \n\
                \ end"

  let ex_2 = " function test()                     \n\
                \    function f()                  \n\
                \        a = 3                     \n\
                \        function g(h)             \n\
                \            h()                   \n\
                \        end                       \n\
                \        function h()              \n\
                \            a                     \n\
                \        end                       \n\
                \        g(h)                      \n\
                \    end                           \n\
                \    f()                           \n\
                \ end"

           -- computed by julia

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([ForAll [] ([] :->: intc (Fin 3)) :@ Just []])

  parseEval pp "example variant 1" ex_1 (pure ty)
  parseEval pp "example variant 2" ex_2 (pure ty)



