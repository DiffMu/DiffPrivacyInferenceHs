
module Spec.Scoping where

import Spec.Base

testScoping pp = do
  describe "Scoping test" $ do
    testScope01 pp
    testScope02 pp
    testScope03 pp
    testScope04 pp


testScope01 pp = do
  let ex = " function test()               \n\
           \   function f(a)               \n\
           \      backup = a               \n\
           \      b = a * 2                \n\
           \      a = b                    \n\
           \      a = 3 * a                \n\
           \      b = a * b                \n\
           \      result = backup + a + b  \n\
           \      result                   \n\
           \   end                         \n\
           \   f(1)                        \n\
           \ end"
           -- backup = 1
           -- b = 1 * 2 = 2
           -- a = 2
           -- a = 3 * 2 = 6
           -- b = 6 * 2 = 12
           -- result = 1 + 6 + 12 = 19

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([ForAll [] ([] :->: intc (Fin 19)) :@ Just []])

  parseEval pp "01 works" ex (pure ty)


testScope02 pp = do
  let ex = " function test()          \n\
           \   function scope(z)      \n\
           \     y = 100              \n\
           \     g(x) = x+y           \n\
           \     y = g(z)             \n\
           \     g(z)                 \n\
           \   end                    \n\
           \   scope(3)               \n\
           \ end"

           -- y = 100
           -- g{y}(x) = x + y
           -- y = g{100}(3) = 3 + 100 = 103
           -- g{103}(3) = 3 + 103 = 106

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([ForAll [] ([] :->: intc (Fin 106)) :@ Just []])

  parseEval pp "02 works" ex (pure ty)


testScope03 pp = do
  let ex = " function test()          \n\
           \   function scope(z)      \n\
           \      h(x) = g(2)         \n\
           \      y = 100             \n\
           \      g(x) = x*y          \n\
           \      y = h(1)            \n\
           \      g(z)                \n\
           \   end                    \n\
           \   scope(3)               \n\
           \ end"

           -- h{g}(x) = g(2)
           -- y = 100
           -- g{y}(x) = x*y
           -- y = h{g{100}}(1) = g{100}(2) = 2*100 = 200
           -- g{200}(3) = 3*200 = 600

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([ForAll [] ([] :->: intc (Fin 600)) :@ Just []])

  parseEval pp "03 works" ex (pure ty)


testScope04 pp = do
  let ex = " function test()                   \n\
           \    function f(a)                  \n\
           \        function h(b)              \n\
           \            i(b) = 2*b + a         \n\
           \            i(b*5)                 \n\
           \        end                        \n\
           \        function g(h,a)            \n\
           \            x = h(a*7)             \n\
           \            y = h(a*7)             \n\
           \            x + y                  \n\
           \        end                        \n\
           \        a = g(h,a)                 \n\
           \        a = g(h,a)                 \n\
           \        function h(b)              \n\
           \            a*11                   \n\
           \        end                        \n\
           \        a = g(h,a)                 \n\
           \        a                          \n\
           \    end                            \n\
           \    f(13)                          \n\
           \ end"

           -- computed by julia

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([ForAll [] ([] :->: intc (Fin 138424)) :@ Just []])

  parseEval pp "04 works" ex (pure ty)
