
module DiffMu.Parser.Expr.FromString where

import DiffMu.Prelude
import DiffMu.Core

import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Debug
import Text.Megaparsec.Char.Lexer

import qualified Data.Text as T
import Debug.Trace(trace)

data JExpr =
     JEInteger Float
   | JEReal Float
   | JESymbol Symbol
   | JELineNumber String Int
   | JEUnsupported String
   | JECall JExpr [JExpr]
   | JEBlock [JExpr]
   | JETypeAnnotation JExpr JuliaType
   | JEIter JExpr JExpr JExpr
   | JELoop JExpr JExpr JExpr
   | JELam [JExpr] JExpr
   | JELamStar [JExpr] JExpr
   | JEFunction JExpr JExpr
   | JEReturn JExpr
   | JEAssignment JExpr JExpr
   | JETup [JExpr]
   | JETupAssignemnt [JExpr] JExpr
   | JEIfElse JExpr JExpr JExpr
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
  ident <- char ':' *> pIdentifier
  return (JuliaType ident)


pSymbol :: Parser Symbol
pSymbol = (Symbol . T.pack) <$> (try (char ':' *> pIdentifier)
                                 <|> try (string "Symbol" *> between (string "(\"") (string "\")") pIdentifier))

pTypeAnnotation :: Parser JExpr
pTypeAnnotation = ":(::)" `with` (JETypeAnnotation <$> pJExpr <*､> pJuliaType)

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

pTLet = do
         (vars, assignment) <- with ":(=)" ((,) <$> (with ":tuple" (pJExpr `sepBy` sep)) <*､> pJExpr)
         return $ (JETupAssignemnt vars assignment)

pSLet = do
         (var, assignment) <- with ":(=)" ((,) <$> pJExpr <*､> pJExpr)
         return $ (JEAssignment var assignment)

pLam :: Parser JExpr
pLam = let pargs = try (":tuple" `with` (pJExpr `sepBy` sep)) <|> ((\x->[x]) <$> pJExpr)
       in do
         (args, body) <- (":->" `with` ((,) <$> pargs <*､> pJExpr))
         return (JELam args body)

pFLet :: Parser JExpr
pFLet = let pFunc = do
                        (name, args) <- pCall pJExpr pJExpr
                        sep
                        body <- pJExpr
                        return (name, (JELam args body))
            pFuncStar = let pStar = do
                                       sign <- pCall pJExpr pJExpr
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


pLoop = let pit = ":(=)" `with` ((,) <$> pJExpr <*､> pJExpr)
        in do
              ((ivar, iter), body) <- ":for" `with` ((,) <$> pit <*､> pJExpr)
              return (JELoop ivar iter body)

pIf = ":if" `with` (JEIfElse <$> pJExpr <*､> pJExpr <*､> pJExpr)
pEIf = ":elseif" `with` (JEIfElse <$> pJExpr <*､> pJExpr <*､> pJExpr)

pUnsupported = let someExpr = (((char ':' >> pIdentifier) <* sep) <* pJExpr `sepBy` sep)
               in JEUnsupported <$> (between (wskip '(') (wskip ')') someExpr)



pJExpr :: Parser JExpr
pJExpr =       try pLineNumber
           <|> try (":block" `with` (JEBlock <$> (pJExpr `sepBy` sep)))
           <|> try (":return" `with` (JEReturn <$> pJExpr))
           <|> try (":tuple" `with` (JETup <$> (pJExpr `sepBy` sep)))
           <|> try (JESymbol <$> pSymbol)
           <|> try ((JEInteger . fromIntegral) <$> decimal) -- these two cannot be switched which is weird
           <|> try (JEReal <$> float)
           <|> try pLam
           <|> try pLoop
           <|> try pIter
           <|> try pFLet
           <|> try pSLet
           <|> try pIf
           <|> try pEIf
           <|> try pTypeAnnotation
           <|> try ((uncurry JECall) <$> (pCall pJExpr pJExpr))
           <|> pUnsupported






parseJExprFromString :: String -> Either DMException JExpr
parseJExprFromString input =
  let res = runParser pJExpr "jl-hs-communication" (trace ("Parsing input:\n------------\n" <> input <> "\n---------------") input)
  in case res of
    Left e  -> Left (InternalError $ "Communication Error: Could not parse JExpr from string\n\n----------------------\n" <> input <> "\n---------------------------\n" <> errorBundlePretty e)
    Right a -> Right a
