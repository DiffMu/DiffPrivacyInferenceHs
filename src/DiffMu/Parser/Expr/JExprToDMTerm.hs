
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
pList (s : []) = pSingle s
pList (s : tail) = case s of
                        JELineNumber file line -> do
                                                    put (file, line)
                                                    s <- (pList tail)
                                                    return s
                        JEReturn ret -> pSingle ret -- drop tail, just end the expression
                        JEAssignment aee amt -> pJSLet aee amt tail
                        JEIfElse _ _ _ -> throwError (InternalError "Conditionals should not have tails!")
                        JEUnsupported s -> parseError ("Unsupported expression " <> show s)

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






pJLoop ivar iter body =
  let pIter start step end = do
       dstart <- pSingle start
       dstep <- pSingle step
       dend <- pSingle end
       let div = Op (IsBinary DMOpDiv)
       let sub = Op (IsBinary DMOpSub)
       let ceil = Op (IsUnary DMOpCeil)
       return (ceil [div [sub [dend, sub [dstart, (Sng 1 (JuliaType "Integer"))]], dstep]]) -- compute number of steps
  in case ivar of
       JESymbol i -> case iter of
                          JEIter start step end -> do
                                                     dbody <- pSingle body
                                                     nit <- pIter start step end
                                                     return (Extra (SERight (MutLoop nit (UserTeVar $ i) dbody)))
                          it -> parseError ("Invalid iterator " <> show it <> ", must be a range.")
       i -> parseError ("Invalid iteration variable " <> (show i) <> ".")




               -- JEIter JExpr JExpr JExpr
               -- JELoop JExpr JExpr JExpr


pSingle :: JExpr -> ParseState ParseDMTerm
pSingle e = case e of
                 JEUnsupported s -> parseError ("Unsupported expression " <> show s)
                 JEBlock stmts -> pList stmts
                 JEInteger n -> pure $ Sng n (JuliaType "Integer")
                 JEReal r -> pure $ Sng r (JuliaType "Real")
                 JEReturn ret -> pSingle ret
                 JESymbol s -> return (Var ((UserTeVar s) :- JTAny))
                 JELam args body -> pJLam args body
                 JELamStar args body -> pJLamStar args body
                 JEAssignment aee amt -> pJSLet aee amt [aee]
                 JEIfElse cond ifb elseb -> (Phi <$> pSingle cond <*> pSingle ifb <*> pSingle elseb)
                 JELoop ivar iter body -> pJLoop ivar iter body

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
               -- JENotRelevant JExpr JuliaType
               -- JEIter JExpr JExpr JExpr
               -- JELoop JExpr JExpr JExpr
               -- JELam [JExpr] JExpr
               -- JELamStar [JExpr] JExpr
               -- JEFunction JExpr JExpr
               -- JEAssignment JExpr JExpr
               -- JETupAssignemnt [JExpr] JExpr
               -- JEIfElse JExpr JExpr JExpr


