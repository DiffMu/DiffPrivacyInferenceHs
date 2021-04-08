
module Example.Terms where

import DiffMu.Prelude
import DiffMu.Core

t₁ :: DMTerm
t₁ = Var (Symbol "x") JTAny

t₂ :: DMTerm
t₂ = Sng 2 JTAny

t₃ a = Arg (Symbol a) JTAny

t₄ = Op (IsBinary DMOpAdd) [t₃ "x", t₃ "x"]

t₅ = Op (IsBinary DMOpAdd) [t₂, t₂]

