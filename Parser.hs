{-# LANGUAGE OverloadedStrings #-}
module Parser where
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language(emptyDef)
import Text.Parsec.String
import Control.Applicative hiding((<|>),many)
import Syntax

reservedNames :: [String]
reservedNames = ["let","rec","in","and","fun",
                 "if","then","else","true","false",
                 "Fail","Omega"]

language :: P.LanguageDef st
language = emptyDef { P.commentStart = "(*"
                    , P.commentEnd = "*)"
                    , P.nestedComments = True
                    , P.reservedNames = reservedNames
                    , P.reservedOpNames = ["=","->","<>"]
                    , P.caseSensitive = True }

lexer :: P.TokenParser st
lexer = P.makeTokenParser language

reserved :: String -> Parser ()
reserved = P.reserved lexer
identifier :: Parser String
identifier = P.identifier lexer
reservedOp :: String -> Parser ()
reservedOp = P.reservedOp lexer
parens :: Parser a -> Parser a
parens = P.parens lexer
commaSep1 :: Parser a -> Parser [a]
commaSep1 = P.commaSep1 lexer
whiteSpace :: Parser ()
whiteSpace = P.whiteSpace lexer

parse :: FilePath -> IO (Either ParseError Program)
parse path = parseFromFile (whiteSpace *> program) path

program :: Parser Program
program = Program <$> (reserved "let" *> reserved "rec" *> defs )
                  <*> (reserved "in" *> term)

defs :: Parser [Def]
defs = sepBy def (reserved "and")

def :: Parser Def
def = (,) <$> identifier <*> liftA2 lam1 (many1 args) (reservedOp "=" *> term)

args :: Parser [Symbol]
args = parens (commaSep1 identifier)
       <|> (pure <$> identifier)

term :: Parser Term
term = lamE
    <|> branchE
    <|> nonDetE

lam1 :: [[Symbol]] -> Term -> Term
lam1 = flip (foldr Lam)

lamE :: Parser Term
lamE = liftA2 lam1 (reserved "fun" *> many1 args) (reservedOp "->" *> term)

branchE :: Parser Term
branchE = liftA3 If (reserved "if" *> term) 
                    (reserved "then" *> term)
                    (reserved "else" *> term)

nonDetE :: Parser Term
nonDetE = chainl1 appE (reservedOp "<>" *> pure (:+:))

appE :: Parser Term
appE = liftA2 (foldl App) primE (many tuple)

tuple :: Parser [Term]
tuple = parens (commaSep1 term) <|> (pure <$> primE)

primE :: Parser Term
primE = trueE
     <|> falseE
     <|> failE
     <|> omegaE
     <|> varE
     <|> parens term

trueE,falseE,failE,omegaE,varE :: Parser Term
trueE = reserved "true" *> pure (C True) 
falseE = reserved "false" *> pure (C False)
failE = reserved "Fail" *> pure (Fail "")
omegaE = reserved "Omega" *> pure (Omega "")
varE = V <$> identifier
