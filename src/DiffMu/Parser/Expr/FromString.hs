
module DiffMu.Parser.Expr.FromString where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core

import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Number

import qualified Data.Text as T

-- carry line number information as user state
type LnParser = Parsec String Int

pTLet = do
         (vars, assignment) <- with ":(=)" ((,) <$> (with ":tuple" (many pAsgmt)) <*､> pExpr)
         tail <- pTail (Tup (Var <$> vars))
         return $ (TLet vars assignment tail)

pSLet = do
         (var, assignment) <- with ":(=)" ((,) <$> pAsgmt <*､> pExpr)
         tail <- pTail (Var var)
         return $ (SLet var assignment tail)


with :: String -> LnParser a -> LnParser a
with name content = between (wskip '(') (wskip ')') (((string name) >> sep) >> content)

skippable = (many (oneOf " \n"))
wskip c = between skippable skippable (char c)

sep :: LnParser Char
sep = wskip ','


pLineNumber :: LnParser ()
pLineNumber =
   let p = (char ':') >> (between (string "(#= ") (string " =#)") ((string "none:") >> nat))
   in do
      ln <- p
      putState ln
      return ()



pSng :: LnParser ParseDMTerm
pSng = do
  n <- decFloat False
  case n of
    Left a -> do
      let ident = "Integer"
      return $ Sng (fromIntegral a) (JuliaType ident)
    Right a -> do
      let ident = "Real"
      return $ Sng a (JuliaType ident)


pIdentifier :: LnParser String
pIdentifier = many1 (noneOf "(),[]\"")

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
pCall pcallee pargs = let p = do
                               name <- pcallee
                               sep
                               args <- (many pargs)
                               return (name, args)
        in (":call" `with` p)

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

pApply :: LnParser ParseDMTerm
pApply = let pmut = do
                         (name, args) <- pCall (string ":!" *> pIdentifier) pExpr
                         let callee = Var (((UserTeVar . Symbol . T.pack) ("!" <> name)) :- JTAny)
                         tail <- pTail (Extra (SERight  MutRet))
                         return (Extra (SERight (MutLet (Apply callee args) tail)))
             papp = do
                         (callee, args) <- pCall pExpr pExpr
                         return (Apply callee args) -- TODO error properly upon non-empty tail
         in try pmut <|> try papp

infixl 2 <*､>
(<*､>) :: LnParser (a -> b) -> LnParser a -> LnParser b
(<*､>) f a = (f <* sep) <*> a

pExpr :: LnParser ParseDMTerm
pExpr =
             try (pLineNumber >> sep >> pExpr) -- put line number into user state, continue
         <|> try (":block"       `with` pExpr) -- discard :block
         <|> try pApply
         <|> try pSLet
         <|> try pTLet
         <|> try pFLet
         <|> try pSng
         <|> try pVar








parseExprFromString :: String -> Either DMException ParseDMTerm
parseExprFromString input =
  let res = runParser pExpr 0 "jl-hs-communication" input
  in case res of
    Left e  -> Left (InternalError $ "Communication Error: Could not parse ParseDMTerm from string\n\n----------------------\n" <> input <> "\n---------------------------\n" <> show e)
    Right a -> Right a
