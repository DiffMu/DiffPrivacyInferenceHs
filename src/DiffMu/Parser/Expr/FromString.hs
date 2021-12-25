
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

--------------------------------------------------------------------------------
-- a straightforward representation of julia Expr.
-- this parser takes a string and mostly seperates the expression head into a constructor.
-- it also parses numbers properly.

data JTree =
     JLineNumber String Int
   | JHole
   | JSym String
   | JInteger Float
   | JReal Float
   | JColon
   | JCall [JTree]
   | JCurly [JTree]
   | JArrow [JTree]
   | JFunction [JTree]
   | JAssign [JTree]
   | JTypeAssign [JTree]
   | JRef [JTree]
   | JIfElse [JTree]
   | JLoop [JTree]
   | JBlock [JTree]
   | JTup [JTree]
   | JUnsupported String
   deriving Show

type Parser = Parsec Void String


pTLineNumber :: Parser JTree
pTLineNumber = let pLocation = do
                                filename <- some (noneOf @[] " :")
                                char ':'
                                n <- decimal
                                return (filename, n)
              in do
                   (filename, n) <- (char ':') >> (between (string "(#= ") (string " =#)") pLocation)
                   return (JLineNumber filename n)

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

pSymbolString :: Parser String
pSymbolString =    (try (char ':' *> pIdentifier)
                <|> try (string "Symbol" *> between (string "(\"") (string "\")") pIdentifier))

-- any string that is well-paranthesised
pAny :: Parser String
pAny = let noParen = (some (noneOf @[] "()"))
       in (join <$> some (noParen <|> between (wskipc '(') (wskipc ')') pAny))

pWithCtor :: String -> ([JTree] -> JTree) -> Parser JTree
pWithCtor name ctor = name `with` (ctor <$> (pTree `sepBy` sep))

pTree :: Parser JTree
pTree =     try pTLineNumber
        <|> try (string ":_" >> return JHole)
        <|> try (string ":(==)" >> return (JSym "=="))
        <|> try (JSym <$> pSymbolString)
        <|> try (JReal <$> (wskip float))
        <|> try ((JInteger . fromIntegral) <$> (wskip decimal))
        <|> try (":call"     `pWithCtor` JCall)
        <|> try (":curly"    `pWithCtor` JCurly)
        <|> try (":->"       `pWithCtor` JArrow)
        <|> try (":function" `pWithCtor` JFunction)
        <|> try (":(=)"      `pWithCtor` JAssign)
        <|> try (":(::)"     `pWithCtor` JTypeAssign)
        <|> try (string ":(:)" >> return JColon)
        <|> try (":ref"      `pWithCtor` JRef)
        <|> try (":if"       `pWithCtor` JIfElse)
        <|> try (":for"      `pWithCtor` JLoop)
        <|> try (":block"    `pWithCtor` JBlock)
        <|> try (":tuple"    `pWithCtor` JTup)
        <|> JUnsupported <$> pAny

parseJTreeFromString :: String -> Either DMException JTree
parseJTreeFromString input =
  -- let res = runParser pTree "jl-hs-communication" (trace ("Parsing input:\n------------\n" <> input <> "\n---------------") input)
  let res = runParser pTree "jl-hs-communication" input
  in case res of
    Left e  -> Left (InternalError $ "Communication Error: Could not parse JExpr from string\n\n----------------------\n" <> input <> "\n---------------------------\n" <> errorBundlePretty e)
    Right a -> Right a


--------------------------------------------------------------------------------------------
-- parse a JTree (which has the same structure as julia Expr) and
--  - distinguish slet, tlet and bind
--  - distinguish black boxes, sensitivity and privacy lambdas
--  - tidy up loops
--  - catch a few invalid cases
--  - parse symbols in places where types are expected into JuliaTypes
-- the result gets put into a JExpr so it can be used for proper assignment nesting.


-- parse state is (filename, line number, are we inside a function)
-- it's also used for the next step, we don't need th
type JEParseState = (StateT (String,Int) (Except DMException))

jParseError :: String -> JEParseState a
jParseError message = do
                       (file,line) <- get
                       throwOriginalError (ParseError message file line)

data JExpr =
     JEInteger Float
   | JEReal Float
   | JESymbol Symbol
   | JEHole
   | JEColon
   | JELineNumber String Int
   | JEUnsupported String
   | JECall JExpr [JExpr]
   | JEBlock [JExpr]
   | JEBlackBox JExpr [JExpr]
   | JETypeAnnotation JExpr JuliaType
   | JENotRelevant JExpr JuliaType
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
   | JEBind JExpr JExpr
   deriving Show



pJuliaType :: JTree -> JEParseState JuliaType
pJuliaType (JSym name) = case name of
    "Any"      -> pure JTAny
    "Integer"  -> pure JTInt
    "Real"     -> pure JTReal
    "Function" -> pure JTFunction
    "Vector"   -> pure (JTVector JTAny)
    "Matrix"   -> pure (JTMatrix JTAny)
    "DMModel"  -> pure JTModel
    "DMGrads"  -> pure JTGrads
    _          -> jParseError ("Unsupported julia type " <> show name)
pJuliaType (JCurly (name : args)) = case name of
    JSym "Tuple"  -> (JTTuple <$> (mapM pJuliaType args))
    JSym "Matrix" -> case args of
        []  -> pure(JTMatrix JTAny)
        [a] -> (JTMatrix <$> (pJuliaType a))
        _   -> jParseError ("Too many type parameters for matrix type in Matrix{" <> show name <> "}")
    JSym "Vector" -> case args of
        []  -> pure(JTVector JTAny)
        [a] -> (JTVector <$> (pJuliaType a))
        _   -> jParseError ("Too many type parameters for vector type in Vector{" <> show name <> "}")
    _             -> jParseError ("Unsupported parametrised julia type" <> show name)
pJuliaType t = jParseError ("Expected a julia type, got " <> show t)



pSymbol :: Parser Symbol
pSymbol = (Symbol . T.pack) <$> (try (char ':' *> pIdentifier)
                                 <|> try (string "Symbol" *> between (string "(\"") (string "\")") pIdentifier))

pArgs :: [JTree] -> JEParseState [JExpr]
pArgs args = let pArg arg = case arg of
                     JSym _ -> pTreeToJExpr arg
                     JTypeAssign [s, JCall [JSym "NoData"]] -> JENotRelevant <$> pTreeToJExpr s <*> pure JTAny
                     JTypeAssign [s, JCall [JSym "NoData", t]] -> JENotRelevant <$> pTreeToJExpr s <*> pJuliaType t
                     JTypeAssign [s, t] -> JETypeAnnotation <$> pTreeToJExpr s <*> pJuliaType t
                     _ -> jParseError ("Invalid function argument " <> show arg)
             in mapM pArg args

pFLet :: JTree -> JTree -> JEParseState JExpr
pFLet call body = case call of
    JCall (JSym name : args) -> JEFunction <$> pTreeToJExpr (JSym name) <*> (JELam <$> pArgs args <*> pTreeToJExpr body)
    JTypeAssign [JCall (JSym name : args), JCall [ann]] -> case ann of
        JSym "BlackBox" -> JEBlackBox <$> pTreeToJExpr (JSym name) <*> pArgs args
        JSym "Priv"     -> JEFunction <$> pTreeToJExpr (JSym name) <*> (JELamStar <$> pArgs args <*> pTreeToJExpr body)
        _ -> jParseError ("Function return type annotation not yet supported in " <> show call)
    JTypeAssign [JCall _, ann] -> jParseError ("Function return type annotation not yet supported in " <> show call)
    _ -> error ("invalid shape of function definition " <> show call)

pAss :: JTree -> JTree -> JEParseState JExpr
pAss asg asm = case asg of
    JSym _ -> (JEAssignment <$> pTreeToJExpr asg <*> pTreeToJExpr asm)
    JCall _ -> pFLet asg asm
    JTup ts -> (JETupAssignment <$> mapM pTreeToJExpr ts <*> pTreeToJExpr asm)
    JTypeAssign [(JSym s), (JCall [JSym "Robust"])] -> (JEBind <$> pTreeToJExpr (JSym s) <*> pTreeToJExpr asm)
    JTypeAssign [(JCall _), (JCall [JSym "BlackBox"])] -> pFLet asg asm
    JTypeAssign _ -> jParseError ("Type annotations on variable assignments not yet supported in assignment of " <> show asg)
    _ -> jParseError ("Unsupported assignment " <> show asg)


pIter :: [JTree] -> JEParseState JExpr
pIter as = case as of
    [start, end] -> JEIter <$> pTreeToJExpr start <*> (pure $ JEInteger 1) <*> pTreeToJExpr end
    [start, step, end] -> JEIter <$> pTreeToJExpr start <*> pTreeToJExpr step <*> pTreeToJExpr end
    _ -> jParseError ("Unsupported iteration statement " <> show (JCall (JColon : as)))


pTreeToJExpr :: JTree -> JEParseState JExpr
pTreeToJExpr tree = case tree of
     JLineNumber f l -> do -- put line number in the state for exquisit error messages
                                 put (f, l)
                                 return (JELineNumber f l)
     JSym s          -> pure (JESymbol ((Symbol . T.pack) s))
     JInteger i      -> pure $ JEInteger i
     JReal r         -> pure (JEReal r)
     JBlock as       -> JEBlock <$> (mapM pTreeToJExpr as)
     JTup ts         -> JETup <$> (mapM pTreeToJExpr ts)
     JUnsupported s  -> pure $ JEUnsupported s
     JCall as        -> case as of
         (callee : args) -> JECall <$> pTreeToJExpr callee <*> mapM pTreeToJExpr args
         []              -> error "empty call"
     JArrow as       -> case as of
         [JTup args, body] -> JELam <$> pArgs args <*> pTreeToJExpr body
         [s, body]         -> JELam <$> pArgs [s] <*> pTreeToJExpr body
         _                 -> error ("invalid shape or number of args in lam " <> show tree)
     JIfElse as      -> case as of
         [cond, tr, fs] -> JEIfElse <$> pTreeToJExpr cond <*> pTreeToJExpr tr <*> pTreeToJExpr fs
         _              -> error ("wrong number of arguments in ifelse expression " <> show tree <> ", the sanitizer should have prevented this")
     JFunction as    -> case as of
         [call, body] -> pFLet call body
         _            -> error ("invalid shape of function definition in " <> show tree)
     JAssign as -> case as of
         [asg, asm] -> pAss asg asm
         _ -> error ("invalid shape of assignment in " <> show tree)
     JRef as         -> case as of
         (name:refs) -> JERef <$> pTreeToJExpr name <*> mapM pTreeToJExpr refs
         _ -> error ("unsupported reference " <> show tree)
     JHole           -> pure JEHole
     JColon          -> pure JEColon
     JLoop as        -> case as of
         [(JAssign [ivar, JCall (JColon: iter)]), body] -> JELoop <$> pTreeToJExpr ivar <*> pIter iter <*> pTreeToJExpr body
         [(JAssign [_, iter]), _] -> jParseError ("Iterator has to be a range! Not like " <> show iter)
         _ -> jParseError ("unsupported loop statement " <> show tree)
     JCurly _        -> jParseError ("Did not expect a julia type but got " <> show tree)
     JTypeAssign _   -> jParseError ("Type annotations are not supported here: " <> show tree)



parseJExprFromJTree :: JTree -> Either DMException JExpr
parseJExprFromJTree tree =
  let x = runStateT (pTreeToJExpr tree) ("unknown", 0)
      y = case runExcept x of
        Left err -> Left err
        Right (term, _) -> Right term
  in y
