
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.MonadicPolynomial
import DiffMu.Core.TC

checkSens :: DMTerm -> STC DMType
-- checkSens (Var x τ) = throwError GeneralException
checkSens (Sng η τ) = ConstNum τ <$> (injectCoeff (Fin η))
checkSens t = throwError (UnsupportedTermError t)



