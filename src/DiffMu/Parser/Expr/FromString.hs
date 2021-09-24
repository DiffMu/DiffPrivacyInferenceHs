
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

pAss ctor varParser = do
         (var, assignment) <- with ":(=)" ((,) <$> varParser <*､> pExpr)
         parserTrace ("assignment: " <> show var <> "\n")
         tail <- (sep >> pExpr)
         parserTrace ("tail: " <> show tail <> "\n")
         return $ (ctor var assignment tail)



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

pCall :: LnParser (TeVar, [Asgmt JuliaType])
pCall = let p = do
                   name <- pTeVar
                   sep
                   args <- (many pAsgmt)
                   return (name, args)
        in (":call" `with` p)

pCallStar :: LnParser (TeVar, [Asgmt (JuliaType, Relevance)])
pCallStar = let p = do
                   name <- pTeVar
                   sep
                   args <- (many pAsgmtRel)
                   return (name, args)
        in (":call" `with` p)


pFunc = do
            (name, args) <- pCall
            parserTrace (show name)
            sep
            body <- pExpr
            return (name, (Lam args body))

pFuncStar = let pStar = do
                       sign <- pCallStar
                       parserTrace (show sign)
                       sep
                       string ":Priv"
                       return sign
        in do
            (name, args) <- (":(::)" `with` pStar)
            sep
            body <- pExpr
            return (name, (LamStar args body))

pFLet = do
          (name, lam) <- (":function" `with` (try pFuncStar <|> try pFunc))
          sep
          parserTrace (show lam)
          tail <- pExpr
          return (FLet name lam tail)



infixl 2 <*､>
(<*､>) :: LnParser (a -> b) -> LnParser a -> LnParser b
(<*､>) f a = (f <* sep) <*> a

pExpr :: LnParser ParseDMTerm
pExpr =
             try (pLineNumber >> sep >> pExpr) -- put line number into user state, continue
         <|> try (":block"       `with` pExpr) -- discard :block
         <|> try (pAss SLet pAsgmt)
         <|> try (pAss TLet (with ":tuple" (many pAsgmt)))
         <|> try (pAss (\s t u -> (Extra (SELeft (OLFAss s t u)))) pCall) -- one-line function assignments
         <|> try pSng -- TODO why does this not work on begin 1 end?
         <|> try pVar
         <|> try pFLet








parseExprFromString :: String -> Either DMException ParseDMTerm
parseExprFromString input =
  let res = runParser pExpr 0 "jl-hs-communication" input
  in case res of
    Left e  -> Left (InternalError $ "Communication Error: Could not parse ParseDMTerm from string" <> show input <> ":\n" <> show e)
    Right a -> Right a
