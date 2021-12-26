
module Spec.TypecheckingExamples where

import Spec.Base


testTypecheckingExamples pp = do
  testSens pp
  testOps pp
  testPriv pp
  testBlackBox pp
  testSLoop pp
  testDPGD pp
  

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
               \ y :: Robust() = gaussian_mechanism(0.1, 0.1, 0.1, 0.1*x) \n\
               \ 200*y \n\
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
             \    y = bb(y)     \n\
             \    x / y  \n\
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
    parseEval pp "variable" vloop (pure ty_v)
    parseEval pp "variable2" vloop2 (pure ty_v2)
    parseEvalFail pp "variable (bad)" uloop (UnsatisfiableConstraint "")

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
          \ function train_dp(data, labels, eps::NoData(), del::NoData(), n::NoData(), eta::NoData()) :: Priv() \n\
          \    model = init_model() \n\
          \    (dim, _) = size(data) \n\
          \    aloss = 0 \n\
          \    for _ in 1:n \n\
          \        for i in 1:dim \n\
          \           d = data[i,:] \n\
          \           l = labels[i,:] \n\
          \           gs = unbounded_gradient(model, d, l) \n\
          \  \n\
          \           gs = norm_convert(clip(L2,gs)) \n\
          \           gs :: Robust() = gaussian_mechanism(2/dim, eps, del, scale_gradient(1/dim,gs)) \n\
          \           model :: Robust() = subtract_gradient(model, scale_gradient(eta * dim, gs)) \n\
          \     #      aloss += loss(d,l,model)/(n*dim) \n\
          \        end \n\
          \    end \n\
          \    model \n\
          \ end"

      ty = "Fun([([NoFun(Matrix<n: τ_30, c: τ_31>[s_23 × s_35](Num(Data))) @ (4.0⋅s_26⋅sqrt(2.0⋅ceil(s_23)⋅(0.0 - ln(s_50)))⋅sqrt(2.0⋅ceil(s_55)⋅(0.0 - ln(s_52))),ceil(s_23)⋅ceil(s_55)⋅s_27 + s_50⋅ceil(s_55) + s_52),NoFun(Matrix<n: τ_85, c: τ_86>[s_40 × s_41](Num(Data))) @ (4.0⋅s_26⋅sqrt(2.0⋅ceil(s_23)⋅(0.0 - ln(s_50)))⋅sqrt(2.0⋅ceil(s_55)⋅(0.0 - ln(s_52))),ceil(s_23)⋅ceil(s_55)⋅s_27 + s_50⋅ceil(s_55) + s_52),NoFun(Num(τ_106[s_26])) @ (0,0),NoFun(Num(τ_108[s_27])) @ (0,0),NoFun(Num(τ_125[s_55])) @ (0,0),NoFun(Num(τ_141[s_57])) @ (∞,∞)] ->* NoFun(Params[s_53](Num(Real[--])))) @ Just [Any,Any,Any,Any,Any,Any]])"

      cs = "constr_21 : [final,worst,global,exact,special] IsLess (0,s_27),\
           \\nconstr_43 : [final,worst,global,exact,special] IsLess (0,s_52),\
           \\nconstr_18 : [final,worst,global,exact,special] IsLess (s_26,1),\
           \\nconstr_40 : [final,worst,global,exact,special] IsLess (0,s_50),\
           \\nconstr_20 : [final,worst,global,exact,special] IsLess (0,s_26),\
           \\nconstr_39 : [final,worst,global,exact,special] IsLessEqual (s_50,1),\
           \\nconstr_42 : [final,worst,global,exact,special] IsLessEqual (s_52,1),\
           \\nconstr_19 : [final,worst,global,exact,special] IsLess (s_27,1)"
  parseEvalString_customCheck pp "a DP version of basic gradient descent" ex (ty, cs) (pure $ Right ())



