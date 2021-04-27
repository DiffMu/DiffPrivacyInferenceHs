
module DiffMu.Parser.DMTerm.FromString where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core

import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Number
-- import Text.Parsec.String.Char (anyChar)
-- import Text.Parsec.String.Char
-- import Text.Parsec.String.Combinator (many1)
import qualified Data.Text as T

import           Foreign.C.String

-- newtype JuliaType' = JuliaType' String

type ParserIO = ParsecT String () IO


specialChar :: [Char]
specialChar = "(){}, []\""


pIdentifier :: ParserIO String
pIdentifier = many1 (noneOf specialChar)

pSymbol :: ParserIO Symbol
pSymbol = (Symbol . T.pack) <$> (try (char ':' *> pIdentifier)
                                 <|> try (string "Symbol" *> between (string "(\"") (string "\")") pIdentifier))

-- TODO: Add more types.
pJuliaType :: ParserIO JuliaType
pJuliaType = do
  ident <- pIdentifier
  -- cident <- liftIO (newCString ident)
  return (JuliaType ident)
  --     try (string "Any" *> pure JTAny)
  -- <|> try (string "Integer" *> pure (JTNum JTNumInt))
  -- <|> try (string "Real" *> pure (JTNum JTNumReal))


-- pJuliaNumType :: ParserIO JuliaNumType
-- pJuliaNumType = undefined

pSng :: ParserIO DMTerm
pSng = do
  n <- decFloat False
  case n of
    Left a -> do
      let ident = "Integer"
      -- cident <- liftIO (newCString ident)
      return $ Sng (fromIntegral a) (JuliaType ident)
    Right a -> do
      let ident = "Real"
      -- cident <- liftIO (newCString ident)
      return $ Sng a (JuliaType ident)


infixl 2 <*､>
(<*､>) :: ParserIO (a -> b) -> ParserIO a -> ParserIO b
(<*､>) f a = (f <* string ", ") <*> a

pAsgmt :: (Symbol -> JuliaType -> c) -> ParserIO c
pAsgmt f = between (char '(') (char ')') (f <$> pSymbol <*､> pJuliaType)

pRelevance :: ParserIO Relevance
pRelevance = (try (string "1" *> pure IsRelevant))
             <|> (try (string "0" *> pure NotRelevant))

pAsgmtWithRel :: ParserIO (Asgmt JuliaType, Relevance)
pAsgmtWithRel = between (char '(') (char ')') ((,) <$> pAsgmt (:-) <*､> pRelevance)

pArray :: String -> ParserIO a -> ParserIO [a]
pArray prefix p = string prefix *> between (char '[') (char ']') (p `sepBy` (string ", "))

pTuple2 :: ParserIO a -> ParserIO b -> ParserIO (a,b)
pTuple2 a b = between (char '(') (char ')') ((,) <$> a <*､> b)

pDMTypeOp :: ParserIO DMTypeOp_Some
pDMTypeOp =
      try (string ":+" >> pure (IsBinary DMOpAdd))
  <|> try (string ":*" >> pure (IsBinary DMOpAdd))

with :: String -> ParserIO a -> ParserIO a
with name content = string name >> between (char '(') (char ')') content

pDMTerm :: ParserIO DMTerm
pDMTerm =
      try ("ret"       `with` (Ret     <$> pDMTerm))
  <|> try ("sng"       `with` (pSng))
  <|> try ("var"       `with` (Var     <$> pSymbol <*､> pJuliaType))
  -- <|> try ("arg"       `with` (Arg     <$> pSymbol <*､> pJuliaType))
  <|> try ("op"        `with` (Op      <$> pDMTypeOp <*､> pArray "DMTerm" pDMTerm))
  <|> try ("phi"       `with` (Phi     <$> pDMTerm <*､> pDMTerm <*､> pDMTerm))
  <|> try ("lam"       `with` (Lam     <$> pArray "Tuple{Symbol, DataType}" (pAsgmt (:-)) <*､> pDMTerm ))
  <|> try ("lam_star"  `with` (LamStar <$> pArray "Tuple{Tuple{Symbol, DataType}, Bool}" pAsgmtWithRel <*､> pDMTerm ))
  <|> try ("apply"     `with` (Apply   <$> pDMTerm <*､> pArray "DMTerm" pDMTerm))
  <|> try ("iter"      `with` (Iter    <$> pDMTerm <*､> pDMTerm <*､> pDMTerm))
  <|> try ("flet"      `with` (FLet    <$> pSymbol <*､> pArray "DataType" pJuliaType <*､> pDMTerm <*､> pDMTerm))
  -- no choice
  <|> try ("slet"      `with` (SLet    <$> (pAsgmt (:-)) <*､> pDMTerm <*､> pDMTerm))
  <|> try ("tup"       `with` (Tup     <$> pArray "DMTerm" pDMTerm))
  <|> try ("tlet"      `with` (TLet    <$> pArray "Tuple{Symbol, DataType}" (pAsgmt (:-)) <*､> pDMTerm <*､> pDMTerm))
  <|> try ("loop"      `with` (Loop    <$> pDMTerm <*､> pDMTerm <*､> pTuple2 pSymbol pSymbol <*､> pDMTerm))


-- flet(:f, DataType[Any, Any], lam(Tuple{Symbol, DataType}[(:a, Any), (:b, Any)], op(:+, DMTerm[var(:a, Any), op(:+, DMTerm[op(:*, DMTerm[var(:b, Any), var(:b, Any)]), var(:a, Any)])])), var(:f, Any))

pDMTermFromString :: String -> IO (Either DMException DMTerm)
pDMTermFromString s = do
  res <- runParserT pDMTerm () "jl-hs-communication" s
  case res of
    Left e  -> return $ Left (InternalError $ "Communication Error: Could not parse DMTerm from string:\n" <> show e)
    Right a -> return $ Right a






