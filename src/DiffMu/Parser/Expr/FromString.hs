
module DiffMu.Parser.Expr.FromString where

import DiffMu.Prelude
--import DiffMu.Abstract
import DiffMu.Core

import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Debug
import Text.Megaparsec.Char.Lexer

import qualified Data.Text as T
import Debug.Trace(trace)

data JExpr =
     JECall JExpr [JExpr]
   | JEBlock [JExpr]
   | JELineNumber String Int
   | JESymbol Symbol
   | JETypeAnnotation JExpr JuliaType
   | JEInteger Int
   | JEReal Float
   | JEIter JExpr JExpr JExpr
   | JELoop Symbol JExpr JExpr
   | JELam [(JExpr, JuliaType)] JExpr
   | JELamStar [(JExpr, (JuliaType, Relevance))] JExpr
   | JEFunction Symbol JExpr
   | JEReturn JExpr
   | JEAssignment JExpr JExpr
   | JETupAssignemnt [JExpr] JExpr
   deriving Show


type Parser = Parsec Void String

infixl 2 <*､>
(<*､>) :: Parser (a -> b) -> Parser a -> Parser b
(<*､>) f a = (f <* sep) <*> a

with :: String -> Parser a -> Parser a
with name content = between (wskip '(') (wskip ')') (((string name) >> sep) >> content)

skippable :: Parser String
skippable = (many (oneOf @[] " \n"))

wskip c = between skippable skippable (char c)

sep :: Parser Char
sep = wskip ','

pIdentifier :: Parser String
pIdentifier = some (noneOf @[] "(),[]=#:\"")

pJuliaType :: Parser JuliaType
pJuliaType = do
  ident <- pIdentifier
  return (JuliaType ident)


pSymbol :: Parser Symbol
pSymbol = (Symbol . T.pack) <$> (try (char ':' *> pIdentifier)
                                 <|> try (string "Symbol" *> between (string "(\"") (string "\")") pIdentifier))

pTypeAnnotation :: Parser JExpr
pTypeAnnotation = (uncurry JETypeAnnotation) <$> (pMaybeAnn pJExpr pJuliaType JTAny)

pLineNumber :: Parser JExpr
pLineNumber = let pLocation = do
                                filename <-string "none"
                                char ':'
                                n <- decimal
                                return (filename, n)
              in do
                   (filename, n) <- (char ':') >> (between (string "(#= ") (string " =#)") pLocation)
                   return (JELineNumber filename n)

pCall :: Parser s -> Parser t -> Parser (s, [t])
pCall pcallee pargs = (":call" `with` ((,) <$> pcallee <*､> (pargs `sepBy` sep)))

pCallSign :: String -> Parser t -> Parser t
pCallSign name psign = (":call" `with` ((string name) >> sep >> psign))


pMaybeAnn pAssignee pAnnotation noAnn = let pAnn = do
                                              name <- trace "parsing name" pAssignee
                                              sep
                                              typ <- trace "parsing annotation" pAnnotation
                                              return (name, typ)
                                            pNoAnn = do
                                                       name <- pAssignee
                                                       return (name, noAnn)
                      in     try (":(::)" `with` pAnn)
                         <|> try pNoAnn


pAsgmt :: Parser (JExpr, JuliaType)
--pAsgmt = pMaybeAnn pJExpr pJuliaType JTAny
pAsgmt = pMaybeAnn (JESymbol <$> pSymbol) pJuliaType JTAny

pRelevance :: Parser (JuliaType, Relevance)
pRelevance = let tupl τ = pure (τ, IsRelevant)
                 tupln τ = pure (τ, NotRelevant)
          in
             try (":call" `with` (((string ":NoData") >> sep >> pJuliaType >>= tupln)))
             <|> try ((string ":NoData") >> (return (JTAny, NotRelevant)))
             <|> (pJuliaType >>= tupl)

pAsgmtRel :: Parser (JExpr, (JuliaType, Relevance))
pAsgmtRel = pMaybeAnn pJExpr pRelevance (JTAny, IsRelevant)

pTLet = do
         (vars, assignment) <- with ":(=)" ((,) <$> (with ":tuple" (pJExpr `sepBy` sep)) <*､> pJExpr)
         return $ (JETupAssignemnt vars assignment)

pSLet = do
         (var, assignment) <- with ":(=)" ((,) <$> pJExpr <*､> pJExpr)
         return $ (JEAssignment var assignment)

pLam :: Parser JExpr
pLam = let pargs = try (":tuple" `with` (pAsgmt `sepBy` sep)) <|> ((\x->[x]) <$> pAsgmt)
       in do
         (args, body) <- (":->" `with` ((,) <$> pargs <*､> pJExpr))
         return (JELam args body)

pFLet :: Parser JExpr
pFLet = let pFunc = do
                        (name, args) <- pCall pSymbol pAsgmt
                        sep
                        body <- pJExpr
                        return (name, (JELam args body))
            pFuncStar = let pStar = do
                                       sign <- pCall pSymbol pAsgmtRel
                                       sep
                                       string ":Priv"
                                       return sign
                        in do
                              (name, args) <- (":(::)" `with` pStar)
                              sep
                              body <- pJExpr
                              return (name, (JELamStar args body))
        in do
          (name, lam) <- try (":function" `with` (try pFuncStar <|> try pFunc))
                         <|> try (":(=)" `with` (try pFuncStar <|> try pFunc))
          return (JEFunction name lam)






pIter :: Parser JExpr
pIter = let psign2 = do
                       (start, end) <- pCallSign ":(:)" ((,) <$> pJExpr <*､> pJExpr)
                       return (start, JEInteger 1, end)
            psign3 = pCallSign ":(:)" ((,,) <$> pJExpr <*､> pJExpr <*､> pJExpr)
        in do 
             (start, step, end) <- (try psign2 <|> psign3)
             return (JEIter start step end)


pLoop = let pit = ":(=)" `with` ((,) <$> pSymbol <*､> pJExpr)
        in do
              ((ivar, iter), body) <- ":for" `with` ((,) <$> pit <*､> pJExpr)
              return (JELoop ivar iter body)


pJExpr :: Parser JExpr
pJExpr = dbg "parseing expr" (try pLineNumber
                          <|> try (":block" `with` (JEBlock <$> (pJExpr `sepBy` sep)))
                        --  <|> try (":return" `with` (JEReturn <$> pJExpr))
                          <|> try ((uncurry JECall) <$> (pCall (JESymbol <$> pSymbol) pJExpr))
                         -- <|> try ((uncurry JECall) <$> (pCall pJExpr pJExpr))
                          <|> try (JESymbol <$> pSymbol)
                        --  <|> try (JEInteger <$> decimal) -- these two cannot be switched which is weird
                        --  <|> try (JEReal <$> float)
                        --  <|> try pLoop
                        --  <|> try pIter
                        --  <|> try pFLet
                          <|> try pLam
                          <|> try pTypeAnnotation)





parseJExprFromString :: String -> Either DMException JExpr
parseJExprFromString input =
  let res = runParser pJExpr "jl-hs-communication" input
  in case res of
    Left e  -> Left (InternalError $ "Communication Error: Could not parse JExpr from string\n\n----------------------\n" <> input <> "\n---------------------------\n" <> errorBundlePretty e)
    Right a -> Right a
