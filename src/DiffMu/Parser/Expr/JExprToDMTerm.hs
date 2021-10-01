
module DiffMu.Parser.Expr.JExprToDMTerm where

import DiffMu.Prelude
--import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Parser.Expr.FromString
import qualified Data.Text as T

type ParseState = (StateT (String,Int) (Except DMException))

parseError :: String -> ParseState a
parseError message = do
  (file,line) <- get
  throwError (ParseError message file line)

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


pCall :: JExpr -> [JExpr] -> ParseState ParseDMTerm
-- if the term is a symbol, we check if it
-- is a builtin/op, if so, we construct the appropriate DMTerm
pCall (JESymbol (Symbol sym)) args = case (sym,args) of

  (t@":gaussian_mechanism!", [a1, a2, a3, a4]) -> Gauss <$> pSingle a1 <*> pSingle a2 <*> pSingle a3 <*> pSingle a4
  (t@":gaussian_mechanism!", args) -> parseError $ "The builtin '" <> T.unpack t <> "' requires 4 arguments, but has been given " <> show (length args)

  (t@":subtract_gradient!", [a1, a2]) -> SubGrad <$> pSingle a1 <*> pSingle a2
  (t@":subtract_gradient!", args) -> parseError $ "The builtin '" <> T.unpack t <> "' requires 2 arguments, but has been given " <> show (length args)

  (t@":clip!", [a1,a2]) -> ClipM <$> undefined <*> pSingle a2
  (t@":clip!", args) -> parseError $ "The builtin '" <> T.unpack t <> "' requires 2 arguments, but has been given " <> show (length args)

  _ -> undefined

pCall term args = throwError (UnsupportedError $ "Term " <> show term <> " currently not supported")


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


