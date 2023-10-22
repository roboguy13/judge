module Judge.Logic.Parser
  where

import Judge.Logic.Logic
import Judge.Logic.Unify

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.Void
import Data.Functor

type Parser = Parsec Void String

parseEither :: Parser a -> String -> Either String a
parseEither p str =
  case parse p "<input>" str of
    Left err -> Left $ errorBundlePretty err
    Right r -> Right r

sc :: Parser ()
sc = L.space
  space1
    (L.skipLineComment "%")
    (L.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

keyword :: String -> Parser String
keyword str = lexeme (string str <* notFollowedBy alphaNumChar)

parseIdent :: Parser String
parseIdent = lexeme $ (:) <$> letterChar <*> many restChar
  where
    restChar = letterChar <|> digitChar <|> char '_'

parseVar :: Parser V
parseVar = lexeme $ fmap V (char '?' *> parseIdent)

parseWildcard :: Parser ()
parseWildcard = lexeme $ void (char '_')

parseTerm :: Parser (LTerm V)
parseTerm = (lexeme (fmap Var parseVar)) <|> parseConst <|> parseApp

parseConst :: Parser (LTerm a)
parseConst = lexeme $ fmap Const parseIdent

parseApp1 :: Parser (LTerm V)
parseApp1 = lexeme $ do
  f <- fmap Const parseIdent
  args <- symbol "(" *> parseArgs <* symbol ")"
  pure $ foldl App f args
  where
    parseArgs = parseTerm `sepBy1` symbol ","

parseApp :: Parser (LTerm V)
parseApp = parseApp1 <|> fmap Const parseIdent

parseFact :: Parser (Rule V)
parseFact = lexeme $ do
  hd <- parseApp
  symbol "."
  pure (hd :- [])

parseRule :: Parser (Rule V)
parseRule = lexeme $ do
  hd <- parseApp
  symbol ":-"
  body <- parseApp `sepBy1` symbol ","
  symbol "."

  pure (hd :- body)

parseDecl :: Parser (Rule V)
parseDecl = parseFact <|> parseRule

parseQuery :: Parser (Query V)
parseQuery = parseApp `sepBy1` symbol ","

