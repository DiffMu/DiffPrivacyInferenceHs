
module Spec.TypecheckingExamples where

import Spec.Base


testTypecheckingExamples pp = do
  testSens pp
  testOps pp
  testPriv pp
  testBlackBox pp
  testSLoop pp
  testSample pp
--   testDPGD pp
  

testSens pp = do
  describe "checkSens" $ do
    parseEvalSimple pp"3 + 7 * 9" (pure $ NoFun (Numeric (Const (constCoeff (Fin 66)) DMInt)))
    parseEvalSimple pp"2.2 * 3"   (pure $ NoFun (Numeric (Const (constCoeff (Fin 6.6000004)) DMReal)))

    let test = "function test(a)\n"
            <> "  a\n"
            <> "end"
    let ty   = do
          τ <- newTVar ""
          return $ Fun([([TVar τ :@ oneId] :->: TVar τ) :@ Just [JTAny]])
    parseEvalUnify pp"Checks the identity function" test ty


testOps pp = describe "Ops" $ do
    let ex_num = "function foo(w::Integer, x::Integer, y::Integer, z::Integer) \n\
                 \ if z == 1 \n\
                 \    z1 = x + x + y - 3 \n\
                 \    5.0 * z1  \n\
                 \  else \n\
                 \     w1 = w + y/2 \n\
                 \     w1 + x \n\
                 \  end \n\
                 \ end"
        ex_mat = "function foo(x::Matrix{Integer}, y::Matrix{Integer}, z::Matrix{Integer}) \n\
                 \ 2.0*x + y - z \n\
                 \ end"
        int = NoFun(Numeric (NonConst DMInt))
        real = NoFun(Numeric (NonConst DMReal))
        ty_num = Fun([([int :@ (constCoeff (Fin 1)), int :@ (constCoeff (Fin 11)), int :@ (constCoeff (Fin 5.5)), int :@ inftyS] :->: real) :@ Just [JTInt, JTInt, JTInt, JTInt]])
        ty_mat :: TC DMMain = do
            n <- newVar
            m <- newVar
            let mat1 = NoFun (DMMat L1 U n m (Numeric (NonConst DMInt)))
            let mat2 = NoFun (DMMat L1 U n m (Numeric (NonConst DMReal)))
            return (Fun [([mat1 :@ constCoeff (Fin 2), mat1 :@ constCoeff (Fin 1), mat1 :@ constCoeff (Fin 1)] :->: mat2) :@ Just [JTMatrix JTInt, JTMatrix JTInt, JTMatrix JTInt]])
    parseEval pp "numeric ops sensitivity" ex_num (pure ty_num)
    parseEvalUnify pp "matrix ops sensitivity" ex_mat (ty_mat)

testPriv pp = describe "privacies" $ do
    let ret = "function f(x :: Integer) :: Priv() \n\
               \ x + x                 \n\
               \ end"
        inv = "function g(x :: Integer) :: Priv() \n\
               \ x = 0.1*x \n\
               \ gaussian_mechanism!(0.1, 0.1, 0.1, x) :: Robust() \n\
               \ 200*x \n\
               \ end"
        int = NoFun(Numeric (NonConst DMInt))
        real = NoFun(Numeric (NonConst DMReal))
        ty_r = Fun([([int :@ (inftyS, inftyS)] :->*: int) :@ Just [JTInt]])
        ty_i = Fun([([int :@ (constCoeff (Fin 0.1), constCoeff (Fin 0.1))] :->*: real) :@ Just [JTInt]])
    parseEval pp "return" ret (pure ty_r)
    parseEval pp "robust" inv (pure ty_i)


testBlackBox pp = describe "black box" $ do
    let bb = "function bb(x) :: BlackBox() \n\
             \   100 \n\
             \ end   \n\
             \ function j(x::Integer, y) \n\
             \    z = bb(y)     \n\
             \    x / z  \n\
             \ end"
        int = NoFun(Numeric (NonConst DMInt))
        real = NoFun(Numeric (NonConst DMReal))
        ty = Fun([([int :@ inftyS, real :@ inftyS] :->: real) :@ Just [JTInt, JTAny]])
    parseEvalUnify pp "numeric" bb (pure ty)


testSLoop pp = describe "Sensitivity loop" $ do
    let sloop = "function sloop(x::Integer) \n\
                 \   for i in 1:10 \n\
                 \      x = x + x \n\
                 \   end \n\
                 \   x \n\
                 \end"
        mloop = "function sloop(x::Integer) \n\
                 \   for i in 1:10 \n\
                 \      y = 100   \n\
                 \      x = x + x \n\
                 \      y = x     \n\
                 \   end \n\
                 \   x \n\
                 \end"
        vloop = "function sloop(x::Integer, n::Integer) \n\
                 \   for i in 1:2*n \n\
                 \      x = x + 5 \n\
                 \   end \n\
                 \   x \n\
                 \end"
        vloop2 = "function sloop(x::Integer, n::Integer) \n\
                 \   for i in 1:2:n \n\
                 \      x = x + n \n\
                 \   end \n\
                 \   x \n\
                 \end"
        uloop = "function sloop(x::Integer, n::Integer) \n\
                 \   for i in 1:2:n \n\
                 \      x = 2*x + 5 \n\
                 \   end \n\
                 \   x \n\
                 \end"
        int = NoFun(Numeric (NonConst DMInt))
        ty_s = Fun([([int :@ (constCoeff (Fin 1024))] :->: int) :@ Just [JTInt]])
        ty_v = Fun([([int :@ (constCoeff (Fin 1)), int :@ (constCoeff (Fin 2))] :->: int) :@ Just [JTInt, JTInt]])
        ty_v2 = Fun([([int :@ (constCoeff (Fin 1)), int :@ (inftyS)] :->: int) :@ Just [JTInt, JTInt]])
    parseEval pp "static" sloop (pure ty_s)
    parseEvalFail pp "overwriting" mloop (DemutationError "")
    parseEval pp "variable" vloop (pure ty_v)
    parseEval pp "variable2" vloop2 (pure ty_v2)
    parseEvalFail pp "variable (bad)" uloop (UnsatisfiableConstraint "")

testSample pp = describe "Sample" $ do
    let ex = "foo(d::Vector) :: BlackBox() = d \n\
              \function bar(data, b) :: Priv() \n\
              \  D, L = sample(b, data, data) \n\
              \  gs = foo(D[1,:]) \n\
              \  clip!(L2,gs) \n\
              \  norm_convert(gs) \n\
              \  gaussian_mechanism!(2, 0.2, 0.3, gs) :: Robust() \n\
              \  gs \n\
              \end"
        ty = "Fun([([NoFun(Matrix<n: L∞, c: τ_26>[s_9 × s_18](Num(Data))) @ (0.4⋅s_15⋅(1 / s_9),0.3⋅s_15⋅(1 / s_9)),NoFun(Num(Int[s_15])) @ (0,0)] ->* NoFun(Grads<n: L∞, c: U>[s_20](Num(Real[--])))) @ Just [Any,Any]])"
        cs = ""
    parseEvalString_customCheck pp "" ex (ty, cs) (pure $ Right ())
                                                                                   

testDPGD pp = describe "DPGD" $ do
  let ex = "import Flux \n\
          \ function unbounded_gradient(model::DMModel, d::Vector, l) :: BlackBox() \n\
          \    gs = Flux.gradient(Flux.params(model.model)) do \n\
          \            loss(d,l,model) \n\
          \         end \n\
          \    return DMGrads(gs) \n\
          \ end \n\
          \ function init_model() :: BlackBox() \n\
          \  DMModel(Flux.Chain( \n\
          \          Flux.Dense(28*28,40, Flux.relu), \n\
          \          Flux.Dense(40, 10), \n\
          \          Flux.softmax)) \n\
          \ end \n\
          \ loss(X, y, model) :: BlackBox() = Flux.crossentropy(model.model(X), y) \n\
          \ function train_dp(data, labels, eps::NoData(), del::NoData(), eta::NoData()) :: Priv() \n\
          \    model = init_model() \n\
          \    (dim, _) = size(data) \n\
          \    for i in 1:dim \n\
          \           d = data[i,:] \n\
          \           l = labels[i,:] \n\
          \           gs = unbounded_gradient(model, d, l) \n\
          \           gsc = norm_convert(clip(L2,gs)) \n\
          \           gsg :: Robust() = gaussian_mechanism(2/dim, eps, del, scale_gradient(1/dim,gsc)) \n\
          \           model :: Robust() = subtract_gradient(model, scale_gradient(eta * dim, gsg)) \n\
          \    end \n\
          \    model \n\
          \ end"

      ty = "Fun([([NoFun(Matrix<n: τ_16, c: τ_17>[s_16 × s_28](Num(Data))) @ (2.0⋅sqrt(2.0⋅(0.0 - ln(s_43))⋅ceil(s_16))⋅s_19,s_20⋅ceil(s_16) + s_43),NoFun(Matrix<n: τ_81, c: τ_82>[s_33 × s_34](Num(Data))) @ (2.0⋅sqrt(2.0⋅(0.0 - ln(s_43))⋅ceil(s_16))⋅s_19,s_20⋅ceil(s_16) + s_43),NoFun(Num(τ_101[s_19])) @ (0,0),NoFun(Num(τ_103[s_20])) @ (0,0),NoFun(Num(τ_129[s_47])) @ (∞,∞)] ->* NoFun(Params[s_44](Num(Real[--])))) @ Just [Any,Any,Any,Any,Any]])"

      cs = "constr_16 : [final,worst,global,exact,special] IsLess (s_20,1),\
          \\nconstr_38 : [final,worst,global,exact,special] IsLess (0,s_43),\
          \\nconstr_15 : [final,worst,global,exact,special] IsLess (s_19,1),\
          \\nconstr_17 : [final,worst,global,exact,special] IsLess (0,s_19),\
          \\nconstr_18 : [final,worst,global,exact,special] IsLess (0,s_20),\
          \\nconstr_37 : [final,worst,global,exact,special] IsLessEqual (s_43,1)"
  parseEvalString_customCheck pp "a DP version of basic gradient descent" ex (ty, cs) (pure $ Right ())



