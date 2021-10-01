
module DiffMu.Parser.Expr.JExprToDMTerm where

import DiffMu.Prelude
--import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Parser.Expr.FromString

type ParseState = (StateT (String,Int) (Except DMException))

parseError :: String -> ParseState a
parseError message = do
                       (file,line) <- get
                       throwError (ParseError message file line)

pList :: [JExpr] -> ParseState ParseDMTerm
pList [] = error "bla"
pList (s : []) = pSingle s
pList (s : tail) = case s of
                        JELineNumber file line -> do
                                                    put (file, line)
                                                    s <- (pList tail)
                                                    return s
                        JEReturn ret -> pSingle ret -- drop tail, just end the expression
                        JEAssignment aee amt -> pJSLet aee amt tail

pJLam args body = let pArg arg = case arg of
                                      JESymbol s -> return ((UserTeVar s) :- JTAny)
                                      JETypeAnnotation (JESymbol s) τ -> return ((UserTeVar s) :- τ)
                                      a -> parseError ("Invalid function argument " <> show a)
                  in do
                       dargs <- mapM pArg args
                       dbody <- pSingle body
                       return (Lam dargs dbody)

pJLamStar args body =
   let pArg arg = case arg of
                       JESymbol s -> return ((UserTeVar s) :- (JTAny, IsRelevant))
                       JETypeAnnotation (JESymbol s) τ -> return ((UserTeVar s) :- (τ, IsRelevant))
                       JENotRelevant (JESymbol s) τ -> return ((UserTeVar s) :- (τ, NotRelevant))
                       a -> parseError ("Invalid function argument " <> show a)
   in do
        dargs <- mapM pArg args
        dbody <- pSingle body
        return (LamStar dargs dbody)

pJSLet assignee assignment tail =
   case assignee of
        JESymbol s -> do
                        dasgmt <- pSingle assignment
                        dtail <- pList tail
                        return (SLet ((UserTeVar s) :- JTAny) dasgmt dtail)
        JETypeAnnotation _ _ -> parseError "Type annotations on variables are not supported."
        JENotRelevant _ _ -> parseError "Type annotations on variables are not supported."
        _ -> parseError ("Invalid assignee " <> (show assignee) <> ", must be a variable.")

pSingle :: JExpr -> ParseState ParseDMTerm
pSingle e = case e of
                 JEBlock stmts -> pList stmts
                 JEInteger n -> pure $ Sng n (JuliaType "Integer")
                 JEReal r -> pure $ Sng r (JuliaType "Real")
                 JEReturn ret -> pSingle ret
                 JESymbol s -> return (Var ((UserTeVar s) :- JTAny))
                 JELam args body -> pJLam args body
                 JELamStar args body -> pJLamStar args body
                 JEAssignment aee amt -> pJSLet aee amt [aee]

                 -- JECall JExpr [JExpr]

               -- JELineNumber file line -> putState (file, line)
               -- JEUnsupported String
               -- JEBlock [JExpr]
               -- JETypeAnnotation JExpr JuliaType
               -- JENotRelevant JExpr JuliaType
               -- JEIter JExpr JExpr JExpr
               -- JELoop JExpr JExpr JExpr
               -- JELam [JExpr] JExpr
               -- JELamStar [JExpr] JExpr
               -- JEFunction JExpr JExpr
               -- JEAssignment JExpr JExpr
               -- JETupAssignemnt [JExpr] JExpr
               -- JEIfElse JExpr JExpr JExpr


