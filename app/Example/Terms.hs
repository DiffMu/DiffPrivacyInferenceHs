
module Example.Terms where

import DiffMu.Prelude
import DiffMu.Core

t₁ :: DMTerm
t₁ = Var (Symbol "x") JTAny

t₂ :: DMTerm
t₂ = Sng 2 JTAny

t₃ = Arg (Symbol "x") JTAny
