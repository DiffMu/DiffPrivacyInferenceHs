
module Example.Terms where

import DiffMu.Prelude
import DiffMu.Core

import Foreign.Ptr

t₁ :: DMTerm
t₁ = Var (Symbol "x") (JTAny nullPtr)

t₂ :: DMTerm
t₂ = Sng 2 (JTNumInt nullPtr)

t₃ a = Arg (Symbol a) (JTAny nullPtr)

t₄ = Op (IsBinary DMOpAdd) [t₃ "x", t₃ "x"]

t₅ a b = Op (IsBinary DMOpAdd) [a, b]

t₆ = Lam [Symbol "y" :- (JTAny nullPtr)] (SLet (Symbol "x" :- (JTAny nullPtr)) (Sng 3 (JTNumInt nullPtr)) (Op (IsBinary DMOpMul) [t₁, Var (Symbol "y") (JTAny nullPtr)]))

t₇ = Lam [Symbol "x" :- ((JTNumInt nullPtr)), Symbol "y" :- (JTAny nullPtr)] (t₅ t₄ t₂)

t8 = FLet (Symbol "f") [(JTNumInt nullPtr), (JTAny nullPtr)] t₇ (FLet (Symbol "f") [(JTNumInt nullPtr), (JTAny nullPtr)] t₆ (FLet (Symbol "f") [(JTAny nullPtr), (JTAny nullPtr)] t₆ (Var (Symbol "f") (JTAny nullPtr))))

t9 = Apply t8 [t₂, t₂]

t10 = Lam [Symbol "x" :- ((JTNumInt nullPtr)), Symbol "y" :- (JTAny nullPtr)] (Phi (t₃ "x") t₂ (t₃ "y"))

vz = Var (Symbol "z") (JTAny nullPtr)
t11 = SLet (Symbol "z" :- (JTAny nullPtr)) (Sng 1 (JTNumInt nullPtr)) (SLet (Symbol "z" :- (JTAny nullPtr)) (t₅ (Sng 1 (JTNumInt nullPtr)) vz) (SLet (Symbol "z" :- (JTAny nullPtr)) (t₅ (Sng 2 (JTNumInt nullPtr)) vz) vz))

t12 = LamStar [Symbol "x" :- ((JTNumInt nullPtr)), Symbol "y" :- (JTAny nullPtr)] (Ret (Phi (t₃ "x") t₂ (t₃ "y")))

t13 = Ret (Phi (t₃ "x") t₂ (t₃ "y"))

t14 = (Apply t12 [t₁, t₁])

t15 = Phi t₂ t13 t₂

t16 = Gauss t₂ t₂ t₂ t₆

t17 = MCreate (Sng 1 JTNumInt) (Sng 1 JTNumInt) (Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- JTAny] t₂)


