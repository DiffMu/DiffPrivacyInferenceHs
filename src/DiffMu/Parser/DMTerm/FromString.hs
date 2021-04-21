
module DiffMu.Parser.DMTerm.FromString where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core

pDMTermFromString :: String -> Either DMException DMTerm
pDMTermFromString s = Right (Arg (Symbol "a") JTAny)

