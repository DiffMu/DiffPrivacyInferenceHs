
module DiffMu.Parser.Expr.FromString where

import DiffMu.Prelude
import DiffMu.Core

import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Debug
import Text.Megaparsec.Char.Lexer

import Data.Either

import qualified Data.Text as T
import Debug.Trace(trace)

data JExpr =
     JEInteger Float
   | JEReal Float
   | JESymbol Symbol
   | JEColon
   | JELineNumber String Int
   | JEUnsupported String
   | JECall JExpr [JExpr]
   | JEBlock [JExpr]
   | JEBlackBox JExpr [JExpr]
   | JETypeAnnotation JExpr (Either String JuliaType)
   | JENotRelevant JExpr (Either String JuliaType)
   | JEIter JExpr JExpr JExpr
   | JELoop JExpr JExpr JExpr
   | JELam [JExpr] JExpr
   | JELamStar [JExpr] JExpr
   | JEFunction JExpr JExpr
   | JEAssignment JExpr JExpr
   | JETup [JExpr]
   | JETupAssignment [JExpr] JExpr
   | JEIfElse JExpr JExpr JExpr
   | JERef JExpr [JExpr]
   deriving Show


type Parser = Parsec Void String


infixl 2 <*､>
(<*､>) :: Parser (a -> b) -> Parser a -> Parser b
(<*､>) f a = (f <* sep) <*> a

with :: String -> Parser a -> Parser a
with name content = between (wskipc '(') (wskipc ')') (((string name) >> sep) >> content)

skippable :: Parser String
skippable = (many (oneOf @[] " \n"))

wskip c = between skippable skippable c
wskipc c = wskip (char c)

sep :: Parser Char
sep = wskipc ','

pIdentifier :: Parser String
pIdentifier = skippable *> some (noneOf @[] "(),[]=#:\" \n") <* skippable

pAnything = let someExpr = do
                              r <- pAnything `sepBy` sep
                              return (intercalate ", " r)
            in try pIdentifier <|> (between (wskipc '(') (wskipc ')') someExpr)
            
pJuliaType :: Parser (Either String JuliaType)
pJuliaType = let
    pNoP = let single =
                 string "Any" *> return (Right JTAny)
                 <|> string "Integer" *> return (Right JTInt)
                 <|> string "Real" *> return (Right JTReal)
                 <|> string "Function" *> return (Right JTFunction)
                 <|> string "Vector" *> return (Right (JTVector JTAny))
                 <|> string "Matrix" *> return (Right (JTMatrix JTAny))
                 <|> string "DMModel" *> return (Right JTModel)
                 <|> string "DMGrads" *> return (Right JTGrads)
                 <|> Left <$> pAnything
                 <|> Left <$> pIdentifier
           in try (char ':') *> single
    pP = -- parametrized types
           let pJTup = do
                       ps <- ":curly" `with` ((string ":Tuple" >> sep) *> (pJuliaType `sepBy` sep))
                       case partitionEithers ps of
                          ([], ts) -> return (Right (JTTuple ts))
                          (es, _) -> return (Left (intercalate ", " es))
               pJMat = do
                       p <- ":curly" `with` ((string ":Matrix" >> sep) *> pJuliaType)
                       case p of
                           Right t -> return (Right (JTMatrix t))
                           Left s -> return (Left s)
               pJVec = do
                       p <- ":curly" `with` ((string ":Vector" >> sep) *> pJuliaType)
                       case p of
                           Right t -> return (Right (JTVector t))
                           Left s -> return (Left s)

           in pJTup <|> pJMat <|> pJVec
 in (try pP <|> try pNoP)


pSymbol :: Parser Symbol
pSymbol = (Symbol . T.pack) <$> (try (char ':' *> pIdentifier)
                                 <|> try (string "Symbol" *> between (string "(\"") (string "\")") pIdentifier))

pAnnotation :: Parser JExpr
pAnnotation = let pNoData :: Parser (Either String JuliaType)
                  pNoData = try (":call" `with` ((string ":NoData") >> sep >> pJuliaType))
                            <|> try ((":call" `with` (string ":NoData")) >> (return (Right JTAny)))
                            <|> ((string ":NoData") >> (return (Right JTAny)))
                  pTyp :: Parser JExpr
                  pTyp = (JETypeAnnotation <$> pJExpr <*､> pJuliaType)
              in ":(::)" `with` (try (JENotRelevant <$> pJExpr <*､> pNoData) <|> pTyp) -- careful order is important


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
pCall pcallee pargs = try (":call" `with` ((,) <$> pcallee <*､> (pargs `sepBy` sep)))
                      <|> ((\x -> (x, [])) <$> (":call" `with` pcallee))

pCallSign :: String -> Parser t -> Parser t
pCallSign name psign = (":call" `with` ((string name) >> sep >> psign))

pTLet = do
         (vars, assignment) <- with ":(=)" ((,) <$> (with ":tuple" (pJExpr `sepBy` sep)) <*､> pJExpr)
         return $ (JETupAssignment vars assignment)

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
            pStar = try (string ":Priv") <|> (pCall (string ":Priv") (pJExpr `sepBy` sep) >> return "")
            pFuncStar = do
                        (name, args) <- (":(::)" `with` ((pCall pJExpr pJExpr) <* sep <* pStar))
                        sep
                        body <- pJExpr
                        return (name, (JELamStar args body))
            pToFLet = do
                      (name, lam) <- try (":function" `with` (try pFuncStar <|> try pFunc))
                                     <|> try (":(=)" `with` (try pFuncStar <|> try pFunc))
                      return (JEFunction name lam)
            pBox = try (string ":BlackBox") <|> (pCall (string ":BlackBox") (pJExpr `sepBy` sep) >> return "")
            pBlackBox = do
                        (name, args) <- (":(::)" `with` ((pCall pJExpr pJExpr) <* sep <* pBox))
                        sep
                        pJExpr
                        return (name, args)
            pToBlackBox = do
                          (name, args) <- try (":function" `with` pBlackBox)
                                          <|> try (":(=)" `with` pBlackBox)
                          return (JEBlackBox name args)
        in do
             try pToBlackBox <|> pToFLet



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

pRef = do
       (name, refs) <- ":ref" `with` ((,) <$> pJExpr <*､> (pJExpr `sepBy` sep))
       return (JERef name refs)

pUnsupported = let someExpr = (((char ':' >> pIdentifier) <* sep) <* pJExpr `sepBy` sep)
               in JEUnsupported <$> (between (wskipc '(') (wskipc ')') someExpr)


pJExpr :: Parser JExpr
pJExpr =       try pLineNumber
           <|> try (":block" `with` (JEBlock <$> (pJExpr `sepBy` sep)))
           <|> try (":tuple" `with` (JETup <$> (pJExpr `sepBy` sep)))
           <|> try ((string ":(:)") >> return JEColon)
           <|> try (JESymbol <$> pSymbol)
           <|> try (JEReal <$> (wskip float))
           <|> try ((JEInteger . fromIntegral) <$> (wskip decimal))
           <|> try pRef
           <|> try pLam
           <|> try pLoop
           <|> try pIter
           <|> try pFLet
           <|> try pTLet
           <|> try pSLet
           <|> try pIf
           <|> try pEIf
           <|> try pAnnotation
           <|> try ((uncurry JECall) <$> (pCall pJExpr pJExpr))
           <|> pUnsupported






parseJExprFromString :: String -> Either DMException JExpr
parseJExprFromString input =
  let res = runParser pJExpr "jl-hs-communication" (trace ("Parsing input:\n------------\n" <> input <> "\n---------------") input)
  in case res of
    Left e  -> Left (InternalError $ "Communication Error: Could not parse JExpr from string\n\n----------------------\n" <> input <> "\n---------------------------\n" <> errorBundlePretty e)
    Right a -> Right a


