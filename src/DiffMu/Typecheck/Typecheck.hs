
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Core

checkSens :: DMTerm -> STC DMType
-- checkSens (Var x τ) = throwError GeneralException
-- checkSens (Sng n τ) = undefined
  -- let s = injectCoeff n
  -- in return (ConstNum τ (Sens s))
checkSens t = throwError (UnsupportedTermError t)



