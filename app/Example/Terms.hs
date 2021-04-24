
module Example.Terms where

import DiffMu.Prelude
import DiffMu.Core

import Foreign.Ptr

t₁ :: DMTerm
t₁ = Var (Symbol "x") (JTAny)

t₂ :: DMTerm
t₂ = Sng 2 JTNumInt

t₃ a = Arg (Symbol a) (JTAny)

t₄ = Op (IsBinary DMOpAdd) [t₃ "x", t₃ "x"]

t₅ a b = Op (IsBinary DMOpAdd) [a, b]

t₆ = Lam [Symbol "y" :- (JTAny)] (SLet (Symbol "x" :- (JTAny)) (Sng 3 JTNumInt) (Op (IsBinary DMOpMul) [t₁, Var (Symbol "y") (JTAny)]))

t₇ = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- (JTAny)] (t₅ t₄ t₂)

t8 = FLet (Symbol "f") [JTNumInt, (JTAny)] t₇ (FLet (Symbol "f") [JTNumInt, (JTAny)] t₆ (FLet (Symbol "f") [(JTAny), (JTAny)] t₆ (Var (Symbol "f") (JTAny))))

t9 = Apply t8 [t₂, t₂]

t10 = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- (JTAny)] (Phi (t₃ "x") t₂ (t₃ "y"))

vz = Var (Symbol "z") (JTAny)
t11 = SLet (Symbol "z" :- (JTAny)) (Sng 1 JTNumInt) (SLet (Symbol "z" :- (JTAny)) (t₅ (Sng 1 JTNumInt) vz) (SLet (Symbol "z" :- (JTAny)) (t₅ (Sng 2 JTNumInt) vz) vz))

t12 = LamStar [Symbol "x" :- (JTNumInt), Symbol "y" :- (JTAny)] (Ret (Phi (t₃ "x") t₂ (t₃ "y")))

t13 = Ret (Phi (t₃ "x") t₂ (t₃ "y"))

t14 = (Apply t12 [t₁, t₁])

t15 = Phi t₂ t13 t₂

t16 = Gauss t₂ t₂ t₂ t₆

t17 = MCreate (Sng 1 JTNumInt) (Sng 1 JTNumInt) (Lam [Symbol "x" :- JTNumInt, Symbol "y" :- (JTAny)] t₂)

t18 = Gauss t₂ t₂ t₂ (Lam [Symbol "y" :- (JTAny)] t17)
--t19 = ClipM (Clip L1) t17
--
t20 = Tup [t₅ t₂ t₂, t₂, t₂]

arg a = (Symbol a :- (JTAny))

t21 = TLet [arg "x", arg "y", arg "z"] t20 (Op (IsBinary DMOpAdd) [t₃ "x", t₃ "y"])
