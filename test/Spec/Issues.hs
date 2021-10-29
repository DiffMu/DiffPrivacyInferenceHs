
module Spec.Issues where

import Spec.Base

testIssues pp = do
  test25 pp
  test51 pp
  test58 pp
  test59 pp
  test60 pp
  test67 pp
  test21 pp

test25 pp = describe "issue 25" $ do
  let ex = " function test() \n\
           \   function a(b) \n\
           \       b + b     \n\
           \   end           \n\
           \   a(1)          \n\
           \ end"

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intc (Fin 2)) :@ Just []])

  parseEval pp "seems fixed (the example typechecks)" ex (pure ty)


test51 pp = describe "issue 53" $ do
  let ex = "function f(x::Integer) :: Priv() \n"
           <>  "(theta, mu) = (100,x) \n"
           <>  "theta + mu \n"
           <>  "end"
      int = NoFun(Numeric (NonConst DMInt))
      ty = Fun([([int :@ (inftyP)] :->*: int) :@ Just [JTInt]])

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
      ty = Fun([([] :->: intc (Fin 3)) :@ Just []])

  parseEval pp "example variant 1" ex_1 (pure ty)
  parseEval pp "example variant 2" ex_2 (pure ty)


test59 pp = describe "issue 59" $ do
  let ex_1 = " function test()                   \n\
             \    function f(a)                  \n\
             \        function g(h)              \n\
             \            h()                    \n\
             \        end                        \n\
             \        function h()               \n\
             \            a                      \n\
             \        end                        \n\
             \        function h()               \n\
             \            a                      \n\
             \        end                        \n\
             \        g(h)                       \n\
             \    end                            \n\
             \    f(3)                           \n\
             \ end                               "

  let ex_1_good
         = " function test()                 \n\
           \    function f(a)                  \n\
           \        function g(h)              \n\
           \            h()                    \n\
           \        end                        \n\
           \        function h()               \n\
           \            a                      \n\
           \        end                        \n\
           \        g(h)                       \n\
           \    end                            \n\
           \    f(3)                           \n\
           \ end                               "

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intc (Fin 3)) :@ Just []])

  parseEval pp "example variant 1 (bad)" ex_1 (pure ty)
  parseEval pp "example variant 1 (good)" ex_1_good (pure ty)


  let ex_2 = " function test()                   \n\
             \    function f(a,b)                \n\
             \        function g(h)              \n\
             \            h()                    \n\
             \        end                        \n\
             \        function h()               \n\
             \            b                      \n\
             \        end                        \n\
             \        function h()               \n\
             \            a                      \n\
             \        end                        \n\
             \        g(h)                       \n\
             \    end                            \n\
             \    f(2,3)                         \n\
             \ end                               "

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intc (Fin 2)) :@ Just []])

  parseEval pp "example variant 2" ex_2 (pure ty)



test60 pp = describe "issue 60" $ do
  let ex_1 = " function test()                  \n\
             \    function f(a)                 \n\
             \        function h(b)             \n\
             \            a                     \n\
             \        end                       \n\
             \        function g(h,a)           \n\
             \            h(a) + h(a)           \n\
             \        end                       \n\
             \        g(h,a)                    \n\
             \    end                           \n\
             \    f(3)                          \n\
             \ end"

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intc (Fin 6)) :@ Just []])

  parseEval pp "example variant 1" ex_1 (pure ty)


test67 pp = describe "issue 67 (same juliatype choice overwriting)" $ do
  let ex_1 =
         " function test()          \n\
         \     function f(a)        \n\
         \         function h(b)    \n\
         \             2*b+a        \n\
         \         end              \n\
         \         function g(h,a)  \n\
         \             h(a)         \n\
         \         end              \n\
         \         a = g(h,a)       \n\
         \         a = g(h,a)       \n\
         \         function h(b)    \n\
         \             a            \n\
         \         end              \n\
         \         a = g(h,a)       \n\
         \         a                \n\
         \     end                  \n\
         \     f(1)                 \n\
         \ end                      "

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intc (Fin 1)) :@ Just []])

  parseEval pp "example variant 1" ex_1 (pure ty)

  let ex_2 =
         " function test()      \n\
         \     function h(b)    \n\
         \         2            \n\
         \     end              \n\
         \     function h(b)    \n\
         \         1            \n\
         \     end              \n\
         \     h(0)             \n\
         \ end                  "

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intc (Fin 1)) :@ Just []])

  parseEval pp "example variant 2" ex_2 (pure ty)

  let ex_3 =
         " function test()      \n\
         \     function h(b)    \n\
         \         3            \n\
         \     end              \n\
         \     function h(b)    \n\
         \         2            \n\
         \     end              \n\
         \     function h(b)    \n\
         \         1            \n\
         \     end              \n\
         \     h(0)             \n\
         \ end                  "

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intc (Fin 1)) :@ Just []])

  parseEval pp "example variant 3" ex_3 (pure ty)

test21 pp = describe "issue 21 (FLet collection)" $ do
  let ex_1 =
         "  function test()     \n\
         \      f(a) = 1        \n\
         \      x = f(0,0)      \n\
         \      f(a,b) = 2      \n\
         \      x               \n\
         \  end                 "

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intc (Fin 2)) :@ Just []])

  parseEval pp "example variant 1" ex_1 (pure ty)

  let ex_2 =
         "  function test()     \n\
         \      x = f(0,0)      \n\
         \      f(a) = 1        \n\
         \      f(a,b) = 2      \n\
         \      x               \n\
         \  end                 "

  parseEvalFail pp "example variant 2 (needs to fail)" ex_2 (VariableNotInScope "f")




