
module DiffMu.Parser.DMTerm.FromString where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core

import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer
-- import Text.Megaparsec.Number
-- import Text.Parsec.String.Char (anyChar)
-- import Text.Parsec.String.Char
-- import Text.Parsec.String.Combinator (many1)
import qualified Data.Text as T

import Data.HashMap.Strict as H

import           Foreign.C.String

-- newtype JuliaType' = JuliaType' String

type Parser = Parsec () String
type ParserIO = ParsecT String () IO


specialChar :: [Char]
specialChar = "(){}, []\""


pIdentifier :: Parser String
pIdentifier = some (noneOf specialChar)

pSymbol :: Parser Symbol
pSymbol = (Symbol . T.pack) <$> (try (char ':' *> pIdentifier)
                                 <|> try (string "Symbol" *> between (string "(\"") (string "\")") pIdentifier))

pTeVar :: Parser TeVar
pTeVar = UserTeVar <$> pSymbol

-- TODO: Add more types.
pJuliaType :: Parser JuliaType
pJuliaType = do
  ident <- pIdentifier
  -- cident <- liftIO (newCString ident)
  return (JuliaType ident)
  --     try (string "Any" *> pure JTAny)
  -- <|> try (string "Integer" *> pure (JTNum JTNumInt))
  -- <|> try (string "Real" *> pure (JTNum JTNumReal))


-- pJuliaNumType :: Parser JuliaNumType
-- pJuliaNumType = undefined

-- pSng :: Parser (PreDMTerm MutabilityExtension)
-- pSng = do
--   n <- (Left <$> float) <|> (Right <$> decimal)
--   case n of
--     Left a -> do
--       let ident = "Integer"
--       -- cident <- liftIO (newCString ident)
--       return $ Sng (fromIntegral a) (JuliaType ident)
--     Right a -> do
--       let ident = "Real"
--       -- cident <- liftIO (newCString ident)
--       return $ Sng a (JuliaType ident)

pSng :: Parser (MutDMTerm )
pSng = let pInt = do
                    n <- decimal
                    let ident = "Integer"
                    return $ Sng (fromIntegral n) (JuliaType ident)
           pReal = do
                    n <- float
                    let ident = "Real"
                    return $ Sng n (JuliaType ident)
       in try pInt <|> pReal


infixl 2 <*､>
(<*､>) :: Parser (a -> b) -> Parser a -> Parser b
(<*､>) f a = (f <* string ", ") <*> a

pAsgmt :: (TeVar -> JuliaType -> c) -> Parser c
pAsgmt f = between (char '(') (char ')') (f <$> pTeVar <*､> pJuliaType)

pRelevance :: Parser Relevance
pRelevance = (try (string "1" *> pure IsRelevant))
             <|> (try (string "0" *> pure NotRelevant))

--pAsgmtWithRel :: Parser (Asgmt (JuliaType, Relevance))
--pAsgmtWithRel = between (char '(') (char ')') ((,) <$> pAsgmt <*､> pRelevance)

pArray :: String -> Parser a -> Parser [a]
pArray prefix p = string prefix *> between (char '[') (char ']') (p `sepBy` (string ", "))

pTuple2 :: Parser a -> Parser b -> Parser (a,b)
pTuple2 a b = between (char '(') (char ')') ((,) <$> a <*､> b)

pTuple3 :: Parser a -> Parser b -> Parser c -> Parser (a,b,c)
pTuple3 a b c = between (char '(') (char ')') ((,,) <$> a <*､> b <*､> c)


pDMTypeOp :: Parser DMTypeOp_Some
pDMTypeOp =
      try (string ":+" >> pure (IsBinary DMOpAdd))
  <|> try (string ":*" >> pure (IsBinary DMOpMul))
  <|> try (string ":-" >> pure (IsBinary DMOpSub))
  <|> try (string ":/" >> pure (IsBinary DMOpDiv))
  <|> try (string ":%" >> pure (IsBinary DMOpMod))
  <|> try (string ":(==)" >> pure (IsBinary DMOpEq))
  <|> try (string ":ceil" >> pure (IsUnary DMOpCeil))

with :: String -> Parser a -> Parser a
with name content = string name >> between (char '(') (char ')') content


-- pSingleChoiceHash :: Parser (HashMap [JuliaType] DMTerm)
-- pSingleChoiceHash = f <$> pTuple2 (pArray "DataType" pJuliaType) pDMTerm
pSingleChoiceHash :: Parser (HashMap [JuliaType] (PreDMTerm MutabilityExtension))
pSingleChoiceHash = f <$> pTuple2 (pArray "Type" pJuliaType) pDMTerm
  where f (sig, term) = H.fromList [(sig,term)]

pGauss = f <$> pTuple3 pDMTerm pDMTerm pDMTerm <*､> pDMTerm
  where f (a,b,c) d = Gauss a b c d

pMat = f <$> pDMTerm <*､> pDMTerm <*､> pTuple2 pTeVar pTeVar <*､> pDMTerm
  where f a b (c,d) e = MCreate a b (c, d) e

pLoop = f <$> pDMTerm <*､> pDMTerm <*､> undefined <*､> pTuple2 pTeVar pTeVar <*､> pDMTerm
  where f _ a b c d = Loop a b c d

-- pDMTerm :: Parser DMTerm
withNothing1 a = f <$> a
  where f a = (a , Nothing)

withNothing2 a = f <$> a
  where f (a , b) = (a , b , Nothing)

pDMTerm :: Parser (PreDMTerm MutabilityExtension )
pDMTerm =
      try ("ret"       `with` (Ret     <$> pDMTerm))
  <|> try ("sng"       `with` (pSng))
  <|> try ("var"       `with` (Var     <$> (pAsgmt (:-))))
  <|> try ("rnd"       `with` (Rnd     <$> pJuliaType))
  -- <|> try ("arg"       `with` (Arg     <$> pSymbol <*､> pJuliaType))
  <|> try ("op"        `with` (Op      <$> pDMTypeOp <*､> pArray "DMTerm" pDMTerm))
  <|> try ("phi"       `with` (Phi     <$> pDMTerm <*､> pDMTerm <*､> pDMTerm))
  <|> try ("lam"       `with` (Lam     <$> pArray "Tuple{Symbol, DataType}" (pAsgmt (:-)) <*､> pDMTerm ))
--  <|> try ("lam_star"  `with` (LamStar <$> pArray "Tuple{Symbol, Tuple{DataType, Bool}" pAsgmtWithRel <*､> pDMTerm ))
  <|> try ("apply"     `with` (Apply   <$> pDMTerm <*､> pArray "DMTerm" pDMTerm))
  <|> try ("iter"      `with` (Iter    <$> pDMTerm <*､> pDMTerm <*､> pDMTerm)) -- NOTE: iter should be deprecated
  <|> try ("flet"      `with` (FLet    <$> pTeVar <*､> pDMTerm <*､> pDMTerm))
  -- no choice
  <|> try ("slet"      `with` (SLet    <$> (pAsgmt (:-)) <*､> pDMTerm <*､> pDMTerm))
  <|> try ("tup"       `with` (Tup     <$> pArray "DMTerm" pDMTerm))
  <|> try ("tlet"      `with` (TLet    <$> pArray "Tuple{Symbol, DataType}" (pAsgmt (:-)) <*､> pDMTerm <*､> pDMTerm))
  <|> try ("loop"      `with` (pLoop))
  <|> try ("gauss"     `with` (pGauss))
  <|> try ("mcreate"   `with` (pMat))
  <|> try ("dmtranspose" `with` (Transpose <$> pDMTerm))
  <|> try ("index"     `with` (Index    <$> pDMTerm <*､> pDMTerm <*､> pDMTerm))
  <|> try ("chce"      `with` (Choice   <$> pSingleChoiceHash))
  -- NN builtins
  <|> try ("dmsubgrad" `with` (SubGrad  <$> pDMTerm <*､> pDMTerm))

  -- mutable terms
  <|> try ("mut_slet"      `with` ((((.).(.)) Extra MutLet)  <$> pDMTerm <*､> pDMTerm))


-- flet(:f, DataType[Any, Any], lam(Tuple{Symbol, DataType}[(:a, Any), (:b, Any)], op(:+, DMTerm[var(:a, Any), op(:+, DMTerm[op(:*, DMTerm[var(:b, Any), var(:b, Any)]), var(:a, Any)])])), var(:f, Any))

pDMTermFromString :: String -> (Either DMException (PreDMTerm MutabilityExtension ))
pDMTermFromString s =
  let res = runParser pDMTerm "jl-hs-communication" s
  in case res of
    Left e  -> Left (InternalError $ "Communication Error: Could not parse DMTerm from string:\n" <> show e)
    Right a -> Right a






