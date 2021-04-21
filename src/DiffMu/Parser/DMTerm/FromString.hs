
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

newtype JuliaType' = JuliaType' String

specialChar :: [Char]
specialChar = "(){}, "


pIdentifier :: Parser String
pIdentifier = many1 (noneOf specialChar)

pSymbol :: Parser Symbol
pSymbol = (Symbol . T.pack) <$> (char ':' *> pIdentifier)

-- TODO: Add more types.
pJuliaType :: Parser JuliaType
pJuliaType = try (string "Any" *> pure JTAny)

pJuliaNumType :: Parser JuliaNumType
pJuliaNumType = undefined

pSng :: Parser DMTerm
pSng = do
  n <- decFloat False
  case n of
    Left a -> pure $ Sng (fromIntegral a) JTNumInt
    Right a -> pure $ Sng a JTNumReal


infixl 2 <*､>
(<*､>) :: Parser (a -> b) -> Parser a -> Parser b
(<*､>) f a = (f <* string ", ") <*> a

pAsgmt :: (Symbol -> JuliaType -> c) -> Parser c
pAsgmt f = between (char '(') (char ')') (f <$> pSymbol <*､> pJuliaType)

pArray :: String -> Parser a -> Parser [a]
pArray prefix p = string prefix *> between (char '[') (char ']') (p `sepBy` (string ", "))

pDMTypeOp :: Parser DMTypeOp_Some
pDMTypeOp =
      try (string ":+" >> pure (IsBinary DMOpAdd))
  <|> try (string ":*" >> pure (IsBinary DMOpAdd))

with :: String -> Parser a -> Parser a
with name content = string name >> between (char '(') (char ')') content

pDMTerm :: Parser DMTerm
pDMTerm =
      try ("ret"       `with` (Ret     <$> pDMTerm))
  <|> try ("sng"       `with` (pSng))
  <|> try ("var"       `with` (Var     <$> pSymbol <*､> pJuliaType))
  <|> try ("arg"       `with` (Var     <$> pSymbol <*､> pJuliaType))
  <|> try ("op"        `with` (Op      <$> pDMTypeOp <*､> pArray "DMTerm" pDMTerm))
  <|> try ("phi"       `with` (Phi     <$> pDMTerm <*､> pDMTerm <*､> pDMTerm))
  <|> try ("lam"       `with` (Lam     <$> pArray "Tuple{Symbol, DataType}" (pAsgmt (:-)) <*､> pDMTerm ))
  <|> try ("lam_star"  `with` (LamStar <$> pArray "Tuple{Symbol, DataType}" (pAsgmt (:-)) <*､> pDMTerm ))
  <|> try ("apply"     `with` (Apply   <$> pDMTerm <*､> pArray "DMTerm" pDMTerm))
  <|> try ("iter"      `with` (Iter    <$> pDMTerm <*､> pDMTerm <*､> pDMTerm))
  <|> try ("flet"      `with` (FLet    <$> pSymbol <*､> pArray "DataType" pJuliaType <*､> pDMTerm <*､> pDMTerm))

-- flet(:f, DataType[Any, Any], lam(Tuple{Symbol, DataType}[(:a, Any), (:b, Any)], op(:+, DMTerm[var(:a, Any), op(:+, DMTerm[op(:*, DMTerm[var(:b, Any), var(:b, Any)]), var(:a, Any)])])), var(:f, Any))

pDMTermFromString :: String -> Either DMException DMTerm
pDMTermFromString s = case parse pDMTerm "jl-hs-communication" s of
  Left e  -> Left (InternalError $ "Communication Error: Could not parse DMTerm from string:\n" <> show e)
  Right a -> Right a






