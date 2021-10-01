
module DiffMu.Parser.Expr.JExprToDMTerm where

import DiffMu.Prelude
--import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Parser.Expr.FromString

type ParseState = (StateT (String,Int) (Except DMException))

pList :: [JExpr] -> ParseState ParseDMTerm
pList [] = error "bla"
pList (s : []) = error "bla"
pList (s : tail) = case s of
                        JELineNumber file line -> do
                                                    put (file, line)
                                                    s <- (pList tail)
                                                    return s
                        JEReturn ret -> pSingle ret -- drop tail, just end the expression



pSingle :: JExpr -> ParseState ParseDMTerm
pSingle e = case e of
                 JEBlock stmts -> pList stmts
                 JEInteger n -> pure $ Sng n (JuliaType "Integer")
                 JEReal r -> pure $ Sng r (JuliaType "Real")
                 JEReturn ret -> pSingle ret


                 -- JECall JExpr [JExpr]

               --  JESymbol Symbol
               --  JELineNumber file line -> putState (file, line)
               -- JEUnsupported String
               -- JEBlock [JExpr]
               -- JETypeAnnotation JExpr JuliaType
               -- JEIter JExpr JExpr JExpr
               -- JELoop JExpr JExpr JExpr
               -- JELam [JExpr] JExpr
               -- JELamStar [JExpr] JExpr
               -- JEFunction JExpr JExpr
               -- JEAssignment JExpr JExpr
               -- JETupAssignemnt [JExpr] JExpr
               -- JEIfElse JExpr JExpr JExpr


