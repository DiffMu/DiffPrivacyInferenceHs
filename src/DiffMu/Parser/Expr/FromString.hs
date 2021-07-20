
module DiffMu.Parser.Expr.FromString where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core

parseExprFromString :: String -> Either String DMTerm
parseExprFromString input = Left $ "The expr parser is currently not implemented!\n"
                            <> "But anyways, since we are here, I was called with the string:\n\n"
                            <> input



