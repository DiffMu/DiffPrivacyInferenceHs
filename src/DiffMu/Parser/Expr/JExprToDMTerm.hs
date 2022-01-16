
module DiffMu.Parser.Expr.JExprToDMTerm where

import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Parser.Expr.FromString
import qualified Data.Text as T

import Debug.Trace


-- parse state is (filename, line number, are we inside a function)
-- the former are for pretty error messages.
-- the latter is used to error upon non-toplevel back box definitions.
type ParseState = (StateT (String,Int, Bool) (Except DMException))

parseError :: String -> ParseState a
parseError message = do
                       (file,line,_) <- get
                       throwOriginalError (ParseError message file line)

-- set parse state to be inside a function
enter = do
          (file, line, _) <- get
          put (file, line, True)

-- set parse state to be outside a function
exit = do
          (file, line, _) <- get
          put (file, line, False)

pSingle :: JExpr -> ParseState MutDMTerm
pSingle e = case e of
                 JEBlock stmts -> pList stmts
                 JEInteger n -> pure $ Sng n JTInt
                 JEReal r -> pure $ Sng r JTReal
                 JESymbol s -> return (Var (Just (UserTeVar s) :- JTAny))
                 JETup elems -> (Tup <$> (mapM pSingle elems))
                 JELam args body -> pJLam args body
                 JELamStar args body -> pJLamStar args body
                 JEIfElse cond ifb elseb -> (Phi <$> pSingle cond <*> pSingle ifb <*> pSingle elseb)
                 JELoop ivar iter body -> pJLoop ivar iter body
                 JEAssignment aee amt -> pJLet SLet aee amt [aee] (Extra . DefaultRet)
                 JETupAssignment aee amt -> pJTLet aee amt [JETup aee] (Extra . DefaultRet)
                 JEFunction name term -> pJFLet name term [name] (Extra . DefaultRet)
                 JEBlackBox name args -> pJBlackBox name args [name] (Extra . DefaultRet)
                 JERef name refs -> pJRef name refs
                 JECall name args -> pJCall name args
                 JEHole -> parseError "Holes (_) are only allowed in assignments."
                 JEUnsupported s -> parseError ("Unsupported expression " <> show s)
                 JEIter _ _ _ -> parseError ("Iterators can only be used in for-loop statements directly.")
                 JEColon -> parseError "Colon (:) can only be used to access matrix rows like in M[1,:]."
                 JETypeAnnotation _ _ -> parseError "Type annotations are only supported on function arguments."
                 JENotRelevant _ _ -> parseError "Type annotations are only supported on function arguments."
                 JELineNumber _ _ -> throwOriginalError (InternalError "What now?") -- TODO


pList :: [JExpr] -> ParseState MutDMTerm
pList [] = error "bla" -- TODO
pList (s : []) = pSingle s
pList (s : tail) = case s of
                        JELineNumber file line -> do
                                                    (_,_,d) <- get
                                                    put (file, line, d)
                                                    s <- (pList tail)
                                                    return s
                        JEAssignment aee amt -> pJLet SLet aee amt tail (\x -> x)
                        JETupAssignment aee amt -> pJTLet aee amt tail (\x -> x)
                        JEFunction name term -> pJFLet name term tail (\x -> x)
                        JEBlackBox name args -> pJBlackBox name args tail (\x -> x)
                        JELoop ivar iter body -> pLoopRes (pJLoop ivar iter body) (pList tail)
                        JECall name args -> pMut (pJCall name args) (pList tail)
                        JEIfElse _ _ _ -> throwOriginalError (InternalError "Conditionals should not have tails!")
                        JEUnsupported s -> parseError ("Unsupported expression " <> show s)
                        _ -> parseError ("Expression " <> show s <> " does not have any effect.")


pLoopRes m ptail = do
                   assignee <- m
                   dtail <- ptail
                   return (Extra (MutLet PureLet assignee dtail))

pMut m ptail = do
                   assignee <- m
                   dtail <- ptail
                   return (Extra (MutLet PureLet assignee dtail))

pSample args = case args of
                    [n, m1, m2] -> do
                                     tn <- pSingle n
                                     tm1 <- pSingle m1
                                     tm2 <- pSingle m2
                                     return (Sample tn tm1 tm2)
                    _ -> parseError ("Invalid number of arguments for sample, namely " <> (show (length args)) <> " instead of 2.")

pJRef name refs = case refs of
                       [i1,JEColon] -> do
                                       t1 <- pSingle i1
                                       referee <- pSingle name
                                       return (Row referee t1)
                       [JEColon,_] -> parseError "Acessing columns of matrices as Vectors is not permitted."
                       [i1,i2] -> do
                                  t1 <- pSingle i1
                                  t2 <- pSingle i2
                                  referee <- pSingle name
                                  return (Index referee t1 t2)
                       [i] -> do -- single indices are only allowed for vectors
                                  t <- pSingle i
                                  referee <- pSingle name
                                  return (VIndex referee t)
                       _ -> parseError ("Only double indexing to matrix elements and single indexing to vector entries supported, but you gave " <> show refs)

pArg arg = case arg of
                     JEHole -> return (Nothing :- JTAny)
                     JESymbol s -> return (Just (UserTeVar s) :- JTAny)
                     JETypeAnnotation (JESymbol s) τ -> return (Just (UserTeVar s) :- τ)
                     JENotRelevant _ _ -> parseError ("Relevance annotation on a sensitivity function is not permitted.")
                     a -> parseError ("Invalid function argument " <> show a)

pArgRel arg = case arg of
                       JEHole -> return (Nothing :- (JTAny, IsRelevant))
                       JESymbol s -> return (Just (UserTeVar s) :- (JTAny, IsRelevant))
                       JETypeAnnotation (JESymbol s) τ -> return (Just (UserTeVar s) :- (τ, IsRelevant))
                       JENotRelevant (JESymbol s) τ -> return (Just (UserTeVar s) :- (τ, NotRelevant))
                       a -> parseError ("Invalid function argument " <> show a)


pJLam args body = do
                   dargs <- mapM pArg args
                   enter
                   dbody <- pSingle body
                   exit
                   return (Lam dargs dbody)

pJLamStar args body = do
                       dargs <- mapM pArgRel args
                       enter
                       dbody <- pSingle body
                       exit
                       return (LamStar dargs dbody)

pJBlackBox name args tail wrapper =
  case name of
    JESymbol pname -> do
                    (_,_,insideFunction) <- get
                    case insideFunction of
                         True -> parseError ("Black boxes can only be defined on top-level scope.")
                         False -> do
                                    pargs <- mapM pArg args
                                    ptail <- pList tail
                                    return (BBLet (UserTeVar pname) (sndA <$> pargs) ptail)
    _ -> parseError $ "Invalid function name expression " <> show name <> ", must be a symbol."


pJLet ctor assignee assignment tail wrapper = do
   dasgmt <- pSingle assignment
   dtail <- pList tail
   case assignee of
        JEHole     -> return (ctor (Nothing :- JTAny) dasgmt (wrapper dtail))
        JESymbol s -> return (ctor (Just (UserTeVar s) :- JTAny) dasgmt (wrapper dtail))
        JETypeAnnotation _ _ -> parseError "Type annotations on variables are not supported."
        JENotRelevant _ _    -> parseError "Type annotations on variables are not supported."
        _                    -> parseError ("Invalid assignee " <> (show assignee) <> ", must be a variable.")


pJLoop ivar iter body =
  let pIter start step end = do
       dstart <- pSingle start
       dstep <- pSingle step
       dend <- pSingle end
       let div = Op (IsBinary DMOpDiv)
       let sub = Op (IsBinary DMOpSub)
       let ceil = Op (IsUnary DMOpCeil)
       return (ceil [div [sub [dend, sub [dstart, (Sng 1 JTInt)]], dstep]]) -- compute number of steps
  in case iter of
       JEIter start step end -> do
                                 dbody <- pSingle body
                                 nit <- pIter start step end
                                 i <- case ivar of
                                              JEHole -> pure Nothing
                                              JESymbol s -> pure $ Just (UserTeVar $ s)
                                              i -> parseError ("Invalid iteration variable " <> (show i) <> ".")
                                 return (Extra (MutLoop nit i dbody))
       it -> parseError ("Invalid iterator " <> show it <> ", must be a range.")


pJTLet assignees assignment tail wrapper = do
  -- make sure that all assignees are simply symbols
  let ensureSymbol (JESymbol s) = return (Just (UserTeVar s) :- JTAny)
      ensureSymbol JEHole = return (Nothing :- JTAny)
      ensureSymbol (JETypeAnnotation _ _) = parseError "Type annotations on variables are not supported."
      ensureSymbol (JENotRelevant _ _) = parseError "Type annotations on variables are not supported."
      ensureSymbol x = parseError ("Invalid assignee " <> (show x) <> ", must be a variable.")

  assignee_vars <- mapM ensureSymbol assignees

  case assignment of
                    JECall (JESymbol (Symbol "sample")) args -> do
                           smp <- pSample args
                           dtail <- pList tail
                           return (SmpLet assignee_vars smp (wrapper dtail))
                    _ -> do  -- parse assignment, tail; and build term
                           dasgmt <- pSingle assignment
                           dtail <- pList tail
                           return (TLet assignee_vars dasgmt (wrapper dtail))

pJFLet name assignment tail wrapper =
  case name of
    JESymbol name -> do
                       dasgmt <- pSingle assignment
                       dtail <- pList tail
                       return (FLet (UserTeVar name) dasgmt (wrapper dtail))
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

  (t@"laplacian_mechanism!", [a1, a2, a3]) -> Laplace <$> pSingle a1 <*> pSingle a2 <*> pSingle a3
  (t@"laplacian_mechanism!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

-- 2 arguments

  (t@"subtract_gradient!", [a1, a2]) -> SubGrad <$> pSingle a1 <*> pSingle a2
  (t@"subtract_gradient!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)

  (t@"scale_gradient!", [a1, a2]) -> ScaleGrad <$> pSingle a1 <*> pSingle a2
  (t@"scale_gradient!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)
  
  (t@"sum_gradients", [a1, a2]) -> SumGrads <$> pSingle a1 <*> pSingle a2
  (t@"sum_gradients", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 argument, but has been given " <> show (length args)
  
  (t@"clip!", [a1,a2]) -> ClipM <$> pClip a1 <*> pSingle a2
  (t@"clip!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)

  -- 1 argument
  (t@"norm_convert!", [a1]) -> ConvertM <$> pSingle a1
  (t@"norm_convert!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

  (t@"transpose", [a1]) -> Transpose <$> pSingle a1
  (t@"transpose", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

  (t@"size", [a1]) -> Size <$> pSingle a1
  (t@"size", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

  (t@"length", [a1]) -> Length <$> pSingle a1
  (t@"length", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)
  
  (t@"zero_gradient", [a]) -> ZeroGrad <$> pSingle a
  (t@"zero_gradient", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

  (t@"internal_expect_const", [a1]) -> InternalExpectConst <$> pSingle a1
  (t@"internal_expect_const", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

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

  (t@"-", [a,b]) -> (\a b -> Op (IsBinary DMOpSub) [a,b]) <$> pSingle a <*> pSingle b
  (t@"-", args)  -> parseError $ "The builtin operation (-) requires exactly 2 arguments, but it has been given " <> show (length args)

  (t@"%", [a,b]) -> (\a b -> Op (IsBinary DMOpMod) [a,b]) <$> pSingle a <*> pSingle b
  (t@"%", args)  -> parseError $ "The builtin operation (%) requires exactly 2 arguments, but it has been given " <> show (length args)

  (t@"==", [a,b]) -> (\a b -> Op (IsBinary DMOpEq) [a,b]) <$> pSingle a <*> pSingle b
  (t@"==", args)  -> parseError $ "The builtin operation (==) requires exactly 2 arguments, but it has been given " <> show (length args)

  ---------------------
  -- other symbols
  --
  -- all other symbols turn into calls on TeVars
  (sym, args) -> (Apply (Var (Just (UserTeVar (Symbol sym)) :- JTAny)) <$> mapM pSingle args)

-- all other terms turn into calls
pJCall term args = Apply <$> pSingle term <*> mapM pSingle args


parseDMTermFromJExpr :: JExpr -> Either DMException MutDMTerm
parseDMTermFromJExpr expr =
  let x = runStateT (pSingle expr) ("unknown",0,False)
      y = case runExcept x of
        Left err -> Left err
        Right (term, _) -> Right term
  in y


