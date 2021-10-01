
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


pClip :: JExpr -> ParseState (DMTypeOf ClipKind)
pClip (JESymbol (Symbol ":L1"))   = pure (Clip L1)
pClip (JESymbol (Symbol ":L2"))   = pure (Clip L2)
pClip (JESymbol (Symbol ":LInf")) = pure (Clip LInf)
pClip term = parseError $ "The term " <> show term <> "is not a valid clip value."


pCall :: JExpr -> [JExpr] -> ParseState ParseDMTerm
-- if the term is a symbol, we check if it
-- is a builtin/op, if so, we construct the appropriate DMTerm
pCall (JESymbol (Symbol sym)) args = case (sym,args) of

  -----------------
  -- binding builtins (use lambdas)
  (t@":mcreate", [a1, a2, a3]) -> f <$> pSingle a1 <*> pSingle a2 <*> extractLambdaArgs a3
    where
      f a b (c,d) = MCreate a b c d
      extractLambdaArgs (JELam args body) = case args of
        -- 2 bound vars? yes
        [v1,v2] -> case (v1,v2) of

          -- symbols? yes
          (JESymbol v1, JESymbol v2) -> do
            body' <- pSingle body
            pure ((UserTeVar v1, UserTeVar v2) , body')

          -- symbols? no => error
          (v1,v2) -> parseError $ "In the 3rd argument of " <> T.unpack t
                                  <> ", could not parse the bound variables: " <> show (v1,v2)

        -- 2 bound vars? no => error
        args -> parseError $ "In the 3rd argument of " <> T.unpack t
                              <> ", expected a lambda term which binds two variables, but the one given binds: "
                              <> show (length args)

      -- lambda? no => error
      extractLambdaArgs term = parseError $ "In the 3rd argument of " <> T.unpack t
                                            <> ", expected a lambda term, got: " <> show term

  -- 3 args? no => error
  (t@":mcreate", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

  ------------
  -- the non binding builtins

  -- 4 arguments
  (t@":gaussian_mechanism!", [a1, a2, a3, a4]) -> Gauss <$> pSingle a1 <*> pSingle a2 <*> pSingle a3 <*> pSingle a4
  (t@":gaussian_mechanism!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 4 arguments, but has been given " <> show (length args)

  -- 3 arguments
  (t@":index", [a1, a2, a3]) -> Index <$> pSingle a1 <*> pSingle a2 <*> pSingle a3
  (t@":index", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

  -- 2 arguments

  (t@":subtract_gradient!", [a1, a2]) -> SubGrad <$> pSingle a1 <*> pSingle a2
  (t@":subtract_gradient!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)

  (t@":clip!", [a1,a2]) -> ClipM <$> pClip a1 <*> pSingle a2
  (t@":clip!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)

  -- 1 argument
  (t@":convert!", [a1]) -> ConvertM <$> pSingle a1
  (t@":convert!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

  (t@":transpose", [a1]) -> Transpose <$> pSingle a1
  (t@":transpose", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

  ----------------------
  -- the ops
  -- the :+ and :* operators allow lists as arguments
  (t@":+", [])   -> parseError "The builtin operation (+) requires at least 2 arguments, but has been given none."
  (t@":+", [a])  -> parseError "The builtin operation (+) requires at least 2 arguments, but has only been given 1."
  (t@":+", args) -> foldl1 (\a b -> Op (IsBinary DMOpAdd) [a,b]) <$> (mapM pSingle args)


  (t@":*", [])   -> parseError "The builtin operation (*) requires at least 2 arguments, but has been given none."
  (t@":*", [a])  -> parseError "The builtin operation (*) requires at least 2 arguments, but has only been given 1."
  (t@":*", args) -> foldl1 (\a b -> Op (IsBinary DMOpMul) [a,b]) <$> (mapM pSingle args)

  -- all unary operations.
  (t@":ceil", [a])  -> (\a -> Op (IsUnary DMOpCeil) [a]) <$> pSingle a
  (t@":ceil", args) -> parseError $ "The builtin operation (ceil) requires exactly 1 argument, but it has been given " <> show (length args)

  -- all binary operations.
  (t@":/", [a,b]) -> (\a b -> Op (IsBinary DMOpDiv) [a,b]) <$> pSingle a <*> pSingle b
  (t@":/", args)  -> parseError $ "The builtin operation (/) requires exactly 2 arguments, but it has been given " <> show (length args)

  (t@":%", [a,b]) -> (\a b -> Op (IsBinary DMOpMod) [a,b]) <$> pSingle a <*> pSingle b
  (t@":%", args)  -> parseError $ "The builtin operation (%) requires exactly 2 arguments, but it has been given " <> show (length args)

  (t@":==", [a,b]) -> (\a b -> Op (IsBinary DMOpEq) [a,b]) <$> pSingle a <*> pSingle b
  (t@":==", args)  -> parseError $ "The builtin operation (==) requires exactly 2 arguments, but it has been given " <> show (length args)

  ---------------------
  -- other symbols
  --
  -- all other symbols turn into calls on TeVars
  (sym, args) -> Apply (Var (UserTeVar (Symbol sym) :- JTAny)) <$> mapM pSingle args

-- all other terms turn into calls
pCall term args = Apply <$> pSingle term <*> mapM pSingle args


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


