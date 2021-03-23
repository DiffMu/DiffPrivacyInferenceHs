
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.MonadicPolynomial
import DiffMu.Core.TC

import Data.HashMap.Strict as H

makeType :: JuliaType -> TC e DMType
makeType JTInt = pure DMInt
makeType JTReal = pure DMReal
makeType JTAny = newType "any"

type Scope = HashMap Symbol [DMTerm]


checkSens :: DMTerm -> Scope -> STC DMType
checkSens (Var x τ) scope = undefined
checkSens (Sng η τ) scope = Const <$> (injectCoeff (Fin η)) <*> makeType τ
checkSens t scope = throwError (UnsupportedTermError t)



