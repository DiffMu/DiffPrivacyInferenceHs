
module Example.Terms where

import DiffMu.Prelude
import DiffMu.Core

import Foreign.Ptr

t1 s = Var (Symbol s) (JTAny)

t2 :: DMTerm
t2 = Sng 2 JTNumInt

t3 a = Arg (Symbol a) (JTAny) IsRelevant

t₄ = Op (IsBinary DMOpAdd) [t3 "x", t3 "x"]

t5 a b = Op (IsBinary DMOpAdd) [a, b]

t₆ = Lam [Symbol "y" :- (JTAny)] (SLet (Symbol "x" :- (JTAny)) (Sng 3 JTNumInt) (Op (IsBinary DMOpMul) [(t1 "x"), (t1 "y")]))

t₇ = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- (JTAny)] (t5 t₄ t2)

t8 = FLet (Symbol "f") [JTNumInt, (JTAny)] t₇ (FLet (Symbol "f") [JTNumInt, (JTAny)] t₆ (FLet (Symbol "f") [(JTAny), (JTAny)] t₆ (t1 "f") ))

t9 = Apply t8 [t2, t2]

t10 = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- (JTAny)] (Phi (t3 "x") t2 (t3 "y"))

vz = Var (Symbol "z") (JTAny)
t11 = SLet (Symbol "z" :- (JTAny)) (Sng 1 JTNumInt) (SLet (Symbol "z" :- (JTAny)) (t5 (Sng 1 JTNumInt) vz) (SLet (Symbol "z" :- (JTAny)) (t5 (Sng 2 JTNumInt) vz) vz))

t12 = LamStar [((Symbol "x" :- (JTNumInt)), IsRelevant), ((Symbol "y" :- (JTAny)), IsRelevant)] (Ret (Phi (t3 "x") t2 (t3 "y")))

t13 = Ret (Phi (t3 "x") t2 (t3 "y"))

t14 = (Apply t12 [(t1 "x"), (t1 "x")])

t15 = Phi t2 t13 t2

t16 = Gauss t2 t2 t2 t₆

t17 = MCreate (Sng 1 JTNumInt) (Sng 1 JTNumInt) (Lam [Symbol "x1" :- JTNumInt, Symbol "x2" :- (JTAny)] (t1 "y"))

t18 = Gauss t2 t2 t2 (Lam [Symbol "y" :- (JTAny)] t17)

t19 = ClipM (Clip L1) (Apply t18 [t2])
--
t20 = (Tup [t5 t2 t2, (t1 "x"), t5 (t1 "x") (t1 "x")])

arg a = (Symbol a :- (JTAny))

t21 = Lam [Symbol "x" :- (JTNumInt)] (TLet [arg "x", arg "y", arg "z"] t20 (Op (IsBinary DMOpAdd) [t3 "y", t5 (t3 "y") (t3 "z")]))
