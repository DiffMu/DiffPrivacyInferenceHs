
module Example.Terms where

import DiffMu.Prelude
import DiffMu.Core

import Foreign.Ptr

var s = Var (Symbol s) (JTAny)
arg a = (Symbol a :- (JTAny))
sng n = Sng n JTNumInt
plus a b = Op (IsBinary DMOpAdd) [a, b]
times a b = Op (IsBinary DMOpMul) [a, b]


t2 :: DMTerm
t2 = Sng 2 JTNumInt

t3 a = Arg (Symbol a) (JTAny) IsRelevant

t4 = Op (IsBinary DMOpAdd) [t3 "x", t3 "x"]

t5 a b = Op (IsBinary DMOpAdd) [a, b]

simplelam = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- (JTAny)] (t3 "y")
simplelam2 = Lam [Symbol "y" :- (JTAny)] (t3 "y")
simpleflet =  FLet (Symbol "f") [JTNumInt, (JTAny)] simplelam (FLet (Symbol "f") [JTNumInt] simplelam2 (var "f"))
simpleapply = Lam [Symbol "z" :- (JTAny)] (Apply simpleflet [(t3 "z")])

t6 = Lam [Symbol "y" :- (JTAny)] (SLet (Symbol "x" :- (JTAny)) (Sng 3 JTNumInt) (Op (IsBinary DMOpMul) [(var "x"), (var "y")]))

t7 = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- (JTAny)] (t5 t4 t2)

t8 = FLet (Symbol "f") [JTNumInt, (JTAny)] t7 (FLet (Symbol "f") [JTNumInt, (JTAny)] t6 (FLet (Symbol "f") [(JTAny), (JTAny)] t6 (var "f") ))

t9 = Apply t8 [t2, t2]

t10 = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- (JTAny)] (Phi (t3 "x") t2 (t3 "y"))

vz = Var (Symbol "z") (JTAny)
t11 = SLet (Symbol "z" :- (JTAny)) (Sng 1 JTNumInt) (SLet (Symbol "z" :- (JTAny)) (t5 (Sng 1 JTNumInt) vz) (SLet (Symbol "z" :- (JTAny)) (t5 (Sng 2 JTNumInt) vz) vz))

t12 = LamStar [((Symbol "x" :- (JTNumInt)), IsRelevant), ((Symbol "y" :- (JTAny)), IsRelevant)] (Ret (Phi (t3 "x") t2 (t3 "y")))

t13 = Ret (Phi (t3 "x") t2 (t3 "y"))

t14 = (Apply t12 [(var "x"), (var "x")])

t15 = Phi t2 t13 t2

t16 = Gauss t2 t2 t2 t4

t16s = LamStar [((Symbol "x" :- (JTNumInt)), IsRelevant), ((Symbol "y" :- (JTAny)), IsRelevant)] t16

t17 = MCreate (Sng 1 JTNumInt) (Sng 1 JTNumInt) (Lam [Symbol "x1" :- JTNumInt, Symbol "x2" :- (JTAny)] (var "y"))

t18 = Gauss t2 t2 t2 (Lam [Symbol "y" :- (JTAny)] t17)

t19 = ClipM (Clip L1) (Apply t18 [t2])

t20 = (Tup [t5 t2 t2, (var "x"), t5 (var "x") (var "x")])


t21 = Lam [Symbol "x" :- (JTNumInt)] (TLet [arg "x", arg "y", arg "z"] t20 (Op (IsBinary DMOpAdd) [t3 "y", t5 (t3 "y") (t3 "z")]))

t22 = Lam [] (FLet (Symbol "app") [(JTAny)] (Lam [arg "f"] (Lam [arg "x"] (Apply (var "f") [var "x"]))) (SLet (arg "a") (sng 3) (SLet (arg "g") (Apply (var "app") [Lam [arg "x"] (times (var "x") (var "c"))]) (SLet (arg "c") (plus (var "a") (sng 1)) (SLet (arg "a") (sng 100) (Apply (var "g") [sng 1]))))))

t23 = Lam [] (FLet (Symbol "app") [(JTAny)] (Lam [arg "f"] (Lam [arg "x"] (Apply (var "f") [Apply (var "f") [var "x"]]))) (SLet (arg "c") (sng 10) (SLet (arg "g") (Apply (var "app") [Lam [arg "x"] (times (var "x") (var "c"))]) (SLet (arg "c") (sng 5) (Apply (var "g") [sng 1])))))

