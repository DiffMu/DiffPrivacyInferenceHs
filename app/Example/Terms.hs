
module Example.Terms where

import DiffMu.Prelude
import DiffMu.Core

t₁ :: DMTerm
t₁ = Var (Symbol "x") JTAny

t₂ :: DMTerm
t₂ = Sng 2 JTNumInt

t₃ a = Arg (Symbol a) JTAny

t₄ = Op (IsBinary DMOpAdd) [t₃ "x", t₃ "x"]

t₅ a b = Op (IsBinary DMOpAdd) [a, b]

t₆ = Lam [Symbol "y" :- JTAny] (SLet (Symbol "x" :- JTAny) (Sng 3 JTNumInt) (Op (IsBinary DMOpMul) [t₁, Var (Symbol "y") JTAny]))

t₇ = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- JTAny] (t₅ t₄ t₂)

t8 = FLet (Symbol "f") [JTNumInt, JTAny] t₇ (FLet (Symbol "f") [JTNumInt, JTAny] t₆ (FLet (Symbol "f") [JTAny, JTAny] t₆ (Var (Symbol "f") JTAny)))

t9 = Apply t8 [t₂, t₂]

t10 = Lam [Symbol "x" :- (JTNumInt), Symbol "y" :- JTAny] (Phi (t₃ "x") t₂ (t₃ "y"))

vz = Var (Symbol "z") JTAny
t11 = SLet (Symbol "z" :- JTAny) (Sng 1 JTNumInt) (SLet (Symbol "z" :- JTAny) (t₅ (Sng 1 JTNumInt) vz) (SLet (Symbol "z" :- JTAny) (t₅ (Sng 2 JTNumInt) vz) vz))

t12 = LamStar [Symbol "x" :- (JTNumInt), Symbol "y" :- JTAny] (Ret (Phi (t₃ "x") t₂ (t₃ "y")))

t13 = Ret (Phi (t₃ "x") t₂ (t₃ "y"))

