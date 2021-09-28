
module DiffMu.Parser.Expr.FromString where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core

import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer

import qualified Data.Text as T

-- carry line number information as user state
type LnParser = ParsecT () String (DiffMu.Prelude.State Int)

pTLet = do
         (vars, assignment) <- with ":(=)" ((,) <$> (with ":tuple" (pAsgmt `sepBy` sep)) <*､> pExpr)
         tail <- pTail (Tup (Var <$> vars))
         return $ (TLet vars assignment tail)

pSLet = do
         (var, assignment) <- with ":(=)" ((,) <$> pAsgmt <*､> pExpr)
         tail <- pTail (Var var)
         return $ (SLet var assignment tail)


with :: String -> LnParser a -> LnParser a
with name content = between (wskip '(') (wskip ')') (((string name) >> sep) >> content)

skippable :: LnParser String
skippable = (many (oneOf @[] " \n"))

wskip c = between skippable skippable (char c)

sep :: LnParser Char
sep = wskip ','


pLineNumber :: LnParser ()
pLineNumber =
   let p = (char ':') >> (between (string "(#= ") (string " =#)") ((string "none:") >> decimal))
   in do
      ln <- p
      put ln
      return ()



pSng :: LnParser ParseDMTerm
pSng = let pInt = do
                    n <- decimal
                    let ident = "Integer"
                    return $ Sng (fromIntegral n) (JuliaType ident)
           pReal = do
                    n <- float
                    let ident = "Real"
                    return $ Sng n (JuliaType ident)
       in try pInt <|> pReal


pIdentifier :: LnParser String
pIdentifier = some (noneOf @[] "(),[]\"")

pSymbol :: LnParser Symbol
pSymbol = (Symbol . T.pack) <$> (try (char ':' *> pIdentifier)
                                 <|> try (string "Symbol" *> between (string "(\"") (string "\")") pIdentifier))
pVar :: LnParser ParseDMTerm
pVar = do
         s <- pSymbol
         return (Var ((UserTeVar $ s) :- JTAny))

pJuliaType :: LnParser JuliaType
pJuliaType = do
  ident <- pIdentifier
  return (JuliaType ident)


pTeVar :: LnParser TeVar
pTeVar = UserTeVar <$> pSymbol

pRelevance :: LnParser (JuliaType, Relevance)
pRelevance = let tupl τ = pure (τ, IsRelevant)
                 tupln τ = pure (τ, NotRelevant)
          in
             try (":call" `with` (((string ":NoData") >> sep >> pJuliaType >>= tupln)))
             <|> try ((string ":NoData") >> (return (JTAny, NotRelevant)))
             <|> (pJuliaType >>= tupl)


--pMaybeAnn :: LnParser t -> LnParser (t, (Maybe JuliaType))
pMaybeAnn pAssignee pAnnotation noAnn = let pAnn = do
                                              name <- pAssignee
                                              sep
                                              typ <- pAnnotation
                                              return (name :- typ)
                                            pNoAnn = do
                                                       name <- pAssignee
                                                       return (name :- noAnn)
                      in     try (":(::)" `with` pAnn)
                         <|> try pNoAnn



pAsgmt :: LnParser (Asgmt JuliaType)
pAsgmt = pMaybeAnn pTeVar pJuliaType JTAny

pAsgmtRel :: LnParser (Asgmt (JuliaType, Relevance))
pAsgmtRel = pMaybeAnn pTeVar pRelevance (JTAny, IsRelevant)

pCall :: LnParser s -> LnParser t -> LnParser (s, [t])
pCall pcallee pargs = (":call" `with` ((,) <$> pcallee <*､> (pargs `sepBy` sep)))

pCallSign :: String -> LnParser t -> LnParser t
pCallSign name psign = (":call" `with` ((string name) >> sep >> psign))

pLam :: LnParser ParseDMTerm
pLam = let pargs = try (":tuple" `with` (pAsgmt `sepBy` sep)) <|> ((\x->[x]) <$> pAsgmt)
       in do
         (args, body) <- (":->" `with` ((,) <$> pargs <*､> pExpr))
         return (Lam args body)


pFunc :: LnParser (TeVar, ParseDMTerm)
pFunc = do
            (name, args) <- pCall pTeVar pAsgmt
            sep
            body <- pExpr
            return (name, (Lam args body))

pFuncStar :: LnParser (TeVar, ParseDMTerm)
pFuncStar = let pStar = do
                       sign <- pCall pTeVar pAsgmtRel
                       sep
                       string ":Priv"
                       return sign
        in do
            (name, args) <- (":(::)" `with` pStar)
            sep
            body <- pExpr
            return (name, (LamStar args body))

pFLet :: LnParser ParseDMTerm
pFLet = do
          (name, lam) <- try (":function" `with` (try pFuncStar <|> try pFunc))
                         <|> try (":(=)" `with` (try pFuncStar <|> try pFunc))
          tail <- pTail (Var (name :- JTAny))
          return (FLet name lam tail)

pTail :: ParseDMTerm -> LnParser ParseDMTerm
pTail noTail = try (sep >> pExpr) <|> (return noTail)

--pTail1 = try (sep >> pExpr) <|> (unexpected "bla")

pOpSym :: LnParser DMTypeOp_Some
pOpSym =
      try (string ":+" >> pure (IsBinary DMOpAdd))
  <|> try (string ":*" >> pure (IsBinary DMOpMul))
  <|> try (string ":-" >> pure (IsBinary DMOpSub))
  <|> try (string ":/" >> pure (IsBinary DMOpDiv))
  <|> try (string ":%" >> pure (IsBinary DMOpMod))
  <|> try (string ":(==)" >> pure (IsBinary DMOpEq))
  <|> try (string ":ceil" >> pure (IsUnary DMOpCeil))

pNorm =
     try ((string ":L1") >> pure (Clip L1))
     <|> try ((string ":L2") >> pure (Clip L2))
     <|> ((string ":LInf") >> pure (Clip LInf))

pIter ::LnParser ParseDMTerm
pIter = let one = (Sng 1 (JuliaType "Integer"))
            psign2 = do
                       (start, end) <- pCallSign ":(:)" ((,) <$> pExpr <*､> pExpr)
                       return (start, one, end)
            psign3 = pCallSign ":(:)" ((,,) <$> pExpr <*､> pExpr <*､> pExpr)
        in do
          (start, step, end) <- try psign2 <|> psign3

          let div = Op (IsBinary DMOpDiv)
          let sub = Op (IsBinary DMOpSub)
          let ceil = Op (IsUnary DMOpCeil)
          return (ceil [div [sub [end, sub [start, one]], step]]) -- compute number of steps

pLoop = let pit = ":(=)" `with` ((,) <$> pTeVar <*､> pIter)
        in do
              ((ivar, nit), body) <- ":for" `with` ((,) <$> pit <*､> pExpr)
              return (Extra (SERight (MutLoop nit ivar body)))

pReturn = do
            ret <- ":return" `with` pExpr
            return (Extra (SELeft (JuliaReturn ret)))

pTup = do
         ts <- (with ":tuple" (pExpr `sepBy` sep))
         return (Tup ts)

--pIf :: LnParser ParseDMTerm
--pIf = do
--        (cond, body) <- (":if" `with` ((,) <$> pExpr <*､> pExpr))
--        tail <- pTail (Extra (SELeft Tail))
--        return (Extra (SELeft (If cond body tail)))

pApply :: LnParser ParseDMTerm
pApply = let pmut = do -- mutating calls annotated by !
                         (name, args) <- pCall (string ":!" *> pIdentifier) pExpr
                         let callee = Var (((UserTeVar . Symbol . T.pack) ("!" <> name)) :- JTAny)
                         tail <- pTail (Extra (SERight MutRet))
                         return (Extra (SERight (MutLet (Apply callee args) tail)))
             pop = do -- builtin operations
                         (op, args) <- pCall pOpSym pExpr
                         case op of
                            IsUnary _ -> return (Op op args)
                            IsBinary _ -> return (foldl1 (\x y -> (Op op [x,y])) args) -- fold to handle (+,a,b,c) -> (a+b)+c
             pbuiltin = let pgauss = do
                                      let sign = ((,,,) <$> pExpr <*､> pExpr <*､> pExpr <*､> pExpr)
                                      (a,b,c,d) <- pCallSign ":gaussian_mechanism!" sign
                                      return (Gauss a b c d)
                            psubgr = do
                                      let sign = ((,) <$> pExpr <*､> pExpr)
                                      (a,b) <- pCallSign ":subtract_gradient!" sign
                                      return (SubGrad a b)
                            pclip = do
                                      let sign = ((,) <$> pNorm <*､> pExpr)
                                      (a,b) <- pCallSign ":clip!" sign
                                      return (ClipM a b)
                        in try pgauss <|> try psubgr <|> try pclip
             papp = do -- regular calls
                         (callee, args) <- pCall pExpr pExpr
                         return (Apply callee args) -- TODO error properly upon non-empty tail
         in try pmut <|> try pop <|> try pbuiltin <|> papp

infixl 2 <*､>
(<*､>) :: LnParser (a -> b) -> LnParser a -> LnParser b
(<*､>) f a = (f <* sep) <*> a

pExpr :: LnParser ParseDMTerm
pExpr =
             try (pLineNumber >> sep >> pExpr) -- put line number into user state, continue
         <|> try (":block"       `with` pExpr) -- discard :block
         <|> try pLam
         <|> try pApply
         <|> try pSLet
         <|> try pTLet
         <|> try pFLet
         <|> try pSng
         <|> try pVar
         <|> try pLoop
         <|> try pTup
         <|> try pReturn








parseExprFromString :: String -> Either DMException ParseDMTerm
parseExprFromString input =
  let (res, _) = runState (runParserT pExpr "jl-hs-communication" input) 0
  in case res of
    Left e  -> Left (InternalError $ "Communication Error: Could not parse ParseDMTerm from string\n\n----------------------\n" <> input <> "\n---------------------------\n" <> show e)
    Right a -> Right a
