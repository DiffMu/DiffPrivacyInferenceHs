
module Spec.TypecheckingExamples where

import Spec.Base


testCheckSens parse = do
  describe "checkSens" $ do
    parseEvalSimple parse "3 + 7 * 9" (pure $ NoFun (Numeric (Const (constCoeff (Fin 66)) DMInt)))
    parseEvalSimple parse "2.2 * 3"   (pure $ NoFun (Numeric (Const (constCoeff (Fin 6.6000004)) DMReal)))

    let test = "function test(a)\n"
            <> "  a\n"
            <> "end"
    let ty   = do
          τ <- newTVar ""
          return $ Fun([([TVar τ :@ oneId] :->: TVar τ) :@ Just [JTAny]])
    parseEvalUnify parse "Checks the identity function" test ty


testOps pp = describe "Ops" $ do
    let ex_num = "function foo(w::Integer, x::Integer, y::Integer, z::Integer) \n\
                 \ if z == 1 \n\
                 \    z = x + x + y - 3 \n\
                 \    5.0 * z  \n\
                 \  else \n\
                 \     w = w + y/2 \n\
                 \     w + x \n\
                 \  end \n\
                 \ end"
        ex_mat = "function foo(x::Matrix{Real}, y::Matrix{Real}, z::Matrix{Real}) \n\
                 \ 2*x + y - z \n\
                 \ end"
              

        int = NoFun(Numeric (NonConst DMInt))
        real = NoFun(Numeric (NonConst DMReal))
        ty_num = Fun([([int :@ (constCoeff (Fin 1)), int :@ (constCoeff (Fin 11)), int :@ (constCoeff (Fin 5.5)), int :@ inftyS] :->: real) :@ Just [JTInt, JTInt, JTInt, JTInt]])
    parseEval pp "numeric ops sensitivity" ex_num (pure ty_num)
    parseEval pp "matrix ops sensitivity" ex_mat (pure ty_num)


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

      intc c = NoFun(Numeric (Const (constCoeff c) DMInt))
      ty = Fun([([] :->: intc (Fin 2)) :@ Just []])

  parseEval pp "a DP version of basic gradient descent" ex (pure ty)




