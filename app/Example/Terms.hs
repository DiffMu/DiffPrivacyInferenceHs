
module Example.Terms where

import DiffMu.Prelude
import DiffMu.Core

import Foreign.Ptr

var s = Var (Symbol s) (JTAny) IsRelevant
arg a = (Symbol a :- (JTAny))
sng n = Sng n JTNumInt
plus a b = Op (IsBinary DMOpAdd) [a, b]
times a b = Op (IsBinary DMOpMul) [a, b]


t2 :: DMTerm
t2 = Sng 2 JTNumInt

t4 = Op (IsBinary DMOpAdd) [var "x", var "x"]

t5 a b = Op (IsBinary DMOpAdd) [a, b]

simplelam = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- (JTAny)] (var "y")
simplelam2 = Lam [Symbol "y" :- (JTAny)] (var "y")
simpleflet =  FLet (Symbol "f") simplelam (FLet (Symbol "f") simplelam2 (var "f"))
simpleapply = Lam [Symbol "z" :- (JTAny)] (Apply simpleflet [(var "z")])

t6 = Lam [Symbol "y" :- (JTAny)] (SLet (Symbol "x" :- (JTAny)) (Sng 3 JTNumInt) (Op (IsBinary DMOpAdd) [(var "x"), (var "y")]))

t7 = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- (JTAny)] (t5 t4 t2)

t8 = FLet (Symbol "f") t7 (FLet (Symbol "f") t6 (FLet (Symbol "f") t6 (var "f") ))

t9 = Apply t8 [t2, t2]

t10 = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- (JTAny)] (Phi (var "x") t2 (var "y"))

t11 = SLet (Symbol "z" :- (JTAny)) (Sng 1 JTNumInt) (SLet (Symbol "z" :- (JTAny)) (t5 (Sng 1 JTNumInt) (var "z")) (SLet (Symbol "z" :- (JTAny)) (t5 (Sng 2 JTNumInt) (var "z")) (var "z")))

t12 = LamStar [((Symbol "x" :- (JTNumInt)), IsRelevant), ((Symbol "y" :- (JTAny)), IsRelevant)] (Ret (Phi (var "x") t2 (var "y")))

t13 = Ret (Phi (var "x") t2 (var "y"))

t14 = (Apply t12 [(var "x"), (var "x")])

t15 = Phi t2 t13 t2

t16 = Gauss t2 t2 t2 t4

t16s = LamStar [((Symbol "x" :- (JTNumInt)), IsRelevant), ((Symbol "y" :- (JTAny)), IsRelevant)] t16

t17 s = MCreate (Sng 1 JTNumInt) (Sng 1 JTNumInt) (Symbol "x1", Symbol "x2") (var s)

t18 = LamStar [(Symbol "y" :- (JTAny), IsRelevant)] (Gauss t2 t2 t2 (t17 "y"))

--t19 = ClipM (Clip L1) (Gauss t2 t2 t2 (t17 "y") (Apply t18 [t2]))

t20 = (Tup [t5 t2 t2, (var "x"), t5 (var "x") (var "x")])


t21 = Lam [Symbol "x" :- (JTNumInt)] (TLet [arg "x", arg "y", arg "z"] t20 (Op (IsBinary DMOpAdd) [var "y", t5 (var "y") (var "z")]))

t22 = Lam [] (FLet (Symbol "app") (Lam [arg "f"] (Lam [arg "x"] (Apply (var "f") [var "x"]))) (SLet (arg "a") (sng 3) (SLet (arg "g") (Apply (var "app") [Lam [arg "x"] (times (var "x") (var "c"))]) (SLet (arg "c") (plus (var "a") (sng 1)) (SLet (arg "a") (sng 100) (Apply (var "g") [sng 1]))))))

t23 = Lam [] (FLet (Symbol "app") (Lam [arg "f"] (Lam [arg "x"] (Apply (var "f") [Apply (var "f") [var "x"]]))) (SLet (arg "c") (sng 10) (SLet (arg "g") (Apply (var "app") [Lam [arg "x"] (times (var "x") (var "c"))]) (SLet (arg "c") (sng 5) (Apply (var "g") [sng 1])))))

