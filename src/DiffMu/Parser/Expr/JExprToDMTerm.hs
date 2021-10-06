
module DiffMu.Parser.Expr.JExprToDMTerm where

import DiffMu.Prelude
--import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Parser.Expr.FromString
import qualified Data.Text as T

import Debug.Trace

type ParseState = (StateT (String,Int) (Except DMException))

parseError :: String -> ParseState a
parseError message = do
                       (file,line) <- get
                       throwError (ParseError message file line)

pSingle :: JExpr -> ParseState MutDMTerm
pSingle e = case e of
                 JEBlock stmts -> pList stmts
                 JEInteger n -> pure $ Sng n (JuliaType "Integer")
                 JEReal r -> pure $ Sng r (JuliaType "Real")
                 JEBlackBox args -> BlackBox <$> mapM pArg args
                 JESymbol s -> return (Var ((UserTeVar s) :- JTAny))
                 JETup elems -> (Tup <$> (mapM pSingle elems))
                 JELam args body -> pJLam args body
                 JELamStar args body -> pJLamStar args body
                 JEIfElse cond ifb elseb -> (Phi <$> pSingle cond <*> pSingle ifb <*> pSingle elseb)
                 JELoop ivar iter body -> pJLoop ivar iter body
                 JEAssignment aee amt -> pJSLet aee amt [aee]
                 JETupAssignment aee amt -> pJTLet aee amt [JETup aee]
                 JEFunction name term -> pJFLet name term [name]
                 JECall name args -> pJCall name args
                 JEUnsupported s -> parseError ("Unsupported expression " <> show s)
                 JEIter _ _ _ -> parseError ("Iterators can only be used in for-loop statements directly.")
                 JETypeAnnotation _ _ -> parseError "Type annotations are only supported on function arguments."
                 JENotRelevant _ _ -> parseError "Type annotations are only supported on function arguments."
                 JELineNumber _ _ -> throwError (InternalError "What now?") -- TODO


pList :: [JExpr] -> ParseState MutDMTerm
pList [] = error "bla"
pList (s : []) = pSingle s
pList (s : tail) = case s of
                        JELineNumber file line -> do
                                                    put (file, line)
                                                    s <- (pList tail)
                                                    return s
                        JEAssignment aee amt -> pJSLet aee amt tail
                        JETupAssignment aee amt -> pJTLet aee amt tail
                        JEFunction name term -> pJFLet name term tail
                        JELoop ivar iter body -> pMutLet (pJLoop ivar iter body) tail
                        JECall name args -> pMutLet (pJCall name args) tail
                        JEIfElse _ _ _ -> throwError (InternalError "Conditionals should not have tails!")
                        JEUnsupported s -> parseError ("Unsupported expression " <> show s)
                        _ -> parseError ("Expression " <> show s <> " does not have any effect.")


pMutLet m tail = do
                   assignee <- m
                   dtail <- pList tail
                   return (Extra (MutLet assignee dtail))

pArg arg = case arg of
                     JESymbol s -> return ((UserTeVar s) :- JTAny)
                     JETypeAnnotation (JESymbol s) τ -> return ((UserTeVar s) :- τ)
                     JENotRelevant _ _ -> parseError ("Relevance annotation on a sensitivity function is not permitted.")
                     a -> parseError ("Invalid function argument " <> show a)

pArgRel arg = case arg of
                       JESymbol s -> return ((UserTeVar s) :- (JTAny, IsRelevant))
                       JETypeAnnotation (JESymbol s) τ -> return ((UserTeVar s) :- (τ, IsRelevant))
                       JENotRelevant (JESymbol s) τ -> return ((UserTeVar s) :- (τ, NotRelevant))
                       a -> parseError ("Invalid function argument " <> show a)


pJLam args body = do
                   dargs <- mapM pArg args
                   dbody <- pSingle body
                   return (Lam dargs dbody)

pJLamStar args body = do
                       dargs <- mapM pArgRel args
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
                                                     return (Extra (MutLoop nit (UserTeVar $ i) dbody))
                          it -> parseError ("Invalid iterator " <> show it <> ", must be a range.")
       i -> parseError ("Invalid iteration variable " <> (show i) <> ".")


pJTLet assignees assignment tail = do
  -- make sure that all assignees are simply symbols
  let ensureSymbol (JESymbol s) = return s
      ensureSymbol (JETypeAnnotation _ _) = parseError "Type annotations on variables are not supported."
      ensureSymbol (JENotRelevant _ _) = parseError "Type annotations on variables are not supported."
      ensureSymbol x = parseError ("Invalid assignee " <> (show x) <> ", must be a variable.")

  assignee_vars <- mapM ensureSymbol assignees

  -- parse assignment, tail; and build term
  dasgmt <- pSingle assignment
  dtail <- pList tail
  return (TLet [(UserTeVar s) :- JTAny | s <- assignee_vars] dasgmt dtail)

pJFLet name assignment tail =
  case name of
    JESymbol name -> do
                       dasgmt <- pSingle assignment
                       dtail <- pList tail
                       return (FLet (UserTeVar name) dasgmt dtail)
    _ -> parseError $ "Invalid function name expression " <> show name <> ", must be a symbol."

pClip :: JExpr -> ParseState (DMTypeOf ClipKind)
pClip (JESymbol (Symbol "L1"))   = pure (Clip L1)
pClip (JESymbol (Symbol "L2"))   = pure (Clip L2)
pClip (JESymbol (Symbol "LInf")) = pure (Clip LInf)
pClip term = parseError $ "The term " <> show term <> "is not a valid clip value."


pJCall :: JExpr -> [JExpr] -> ParseState MutDMTerm
-- if the term is a symbol, we check if it
-- is a builtin/op, if so, we construct the appropriate DMTerm
pJCall (JESymbol (Symbol sym)) args = case (sym,args) of

  -----------------
  -- binding builtins (use lambdas)
  --
  -- NOTE: This is term is currently not generated on the julia side
  --
  (t@"mcreate", [a1, a2, a3]) -> f <$> pSingle a1 <*> pSingle a2 <*> extractLambdaArgs a3
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
  (t@"mcreate", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

  ------------
  -- the non binding builtins

  -- 4 arguments
  (t@"gaussian_mechanism!", [a1, a2, a3, a4]) -> Gauss <$> pSingle a1 <*> pSingle a2 <*> pSingle a3 <*> pSingle a4
  (t@"gaussian_mechanism!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 4 arguments, but has been given " <> show (length args)

  -- 3 arguments
  (t@"index", [a1, a2, a3]) -> Index <$> pSingle a1 <*> pSingle a2 <*> pSingle a3
  (t@"index", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

  -- 2 arguments

  (t@"subtract_gradient!", [a1, a2]) -> SubGrad <$> pSingle a1 <*> pSingle a2
  (t@"subtract_gradient!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)

  (t@"clip!", [a1,a2]) -> ClipM <$> pClip a1 <*> pSingle a2
  (t@"clip!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)

  -- 1 argument
  (t@"convert!", [a1]) -> ConvertM <$> pSingle a1
  (t@"convert!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

  (t@"transpose", [a1]) -> Transpose <$> pSingle a1
  (t@"transpose", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

  ----------------------
  -- the ops
  -- the + and * operators allow lists as arguments
  (t@"+", [])   -> parseError "The builtin operation (+) requires at least 2 arguments, but has been given none."
  (t@"+", [a])  -> parseError "The builtin operation (+) requires at least 2 arguments, but has only been given 1."
  (t@"+", args) -> foldl1 (\a b -> Op (IsBinary DMOpAdd) [a,b]) <$> (mapM pSingle args)


  (t@"*", [])   -> parseError "The builtin operation (*) requires at least 2 arguments, but has been given none."
  (t@"*", [a])  -> parseError "The builtin operation (*) requires at least 2 arguments, but has only been given 1."
  (t@"*", args) -> foldl1 (\a b -> Op (IsBinary DMOpMul) [a,b]) <$> (mapM pSingle args)

  -- all unary operations.
  (t@"ceil", [a])  -> (\a -> Op (IsUnary DMOpCeil) [a]) <$> pSingle a
  (t@"ceil", args) -> parseError $ "The builtin operation (ceil) requires exactly 1 argument, but it has been given " <> show (length args)

  -- all binary operations.
  (t@"/", [a,b]) -> (\a b -> Op (IsBinary DMOpDiv) [a,b]) <$> pSingle a <*> pSingle b
  (t@"/", args)  -> parseError $ "The builtin operation (/) requires exactly 2 arguments, but it has been given " <> show (length args)

  (t@"%", [a,b]) -> (\a b -> Op (IsBinary DMOpMod) [a,b]) <$> pSingle a <*> pSingle b
  (t@"%", args)  -> parseError $ "The builtin operation (%) requires exactly 2 arguments, but it has been given " <> show (length args)

  (t@"==", [a,b]) -> (\a b -> Op (IsBinary DMOpEq) [a,b]) <$> pSingle a <*> pSingle b
  (t@"==", args)  -> parseError $ "The builtin operation (==) requires exactly 2 arguments, but it has been given " <> show (length args)

  ---------------------
  -- other symbols
  --
  -- all other symbols turn into calls on TeVars
  (sym, args) -> (Apply (Var (UserTeVar (Symbol sym) :- JTAny)) <$> mapM pSingle args)

-- all other terms turn into calls
pJCall term args = Apply <$> pSingle term <*> mapM pSingle args


parseDMTermFromJExpr :: JExpr -> Either DMException MutDMTerm
parseDMTermFromJExpr expr =
  let x = runStateT (pSingle expr) ("unknown",0)
      y = case runExcept x of
        Left err -> Left err
        Right (term, _) -> Right term
  in y


