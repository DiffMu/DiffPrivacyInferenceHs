
module Example.Terms where

import DiffMu.Prelude
import DiffMu.Core

t₁ :: DMTerm
t₁ = Var (Symbol "x") JTAny

t₂ :: DMTerm
t₂ = Sng 2 JTNumInt

t₃ a = Var (Symbol a) JTAny

t₄ = Op (IsBinary DMOpAdd) [t₃ "x", t₃ "x"]

t₅ a b = Op (IsBinary DMOpAdd) [a, b]

t₇ = Lam (Lam_ [Symbol "x" :- (JTNum JTNumInt), Symbol "y" :- JTAny] (t₅ t₄ t₂))



