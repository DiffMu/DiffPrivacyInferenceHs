
module DiffMu.Core.Definitions where

import DiffMu.Prelude
import {-# SOURCE #-} DiffMu.Core.Symbolic

data DMKind
type role DMTypeOf nominal
data DMTypeOf (k :: DMKind) where
data DMException

type TVarOf = SymbolOf @DMKind
type SVarOf = SymbolOf @SensKind






