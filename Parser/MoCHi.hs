{-# LANGUAGE OverloadedStrings #-}
module Parser.MoCHi(parseFile) where
import Text.Parsec hiding(Line)
import qualified Text.Parsec.Token as P
import Text.Parsec.Language(emptyDef)
import Text.Parsec.String
import Control.Applicative hiding((<|>),many)
import Syntax
import Control.Monad(replicateM)
import qualified Data.Map as M
import Prelude hiding(lines)


reservedNames :: [String]
reservedNames = ["let","rec","in","and","fun",
                 "if","then","else","true","false","l1","l2","rand_bool",
                 "Fail","Omega","Main"]

language :: P.LanguageDef st
language = emptyDef { P.commentStart = "(*"
                    , P.commentEnd = "*)"
                    , P.nestedComments = True
                    , P.reservedNames = reservedNames
                    , P.reservedOpNames = ["=","->","_|_","#","/","||","&&","=>","(0)"]
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
braces :: Parser a -> Parser a
braces = P.braces lexer
whiteSpace :: Parser ()
whiteSpace = P.whiteSpace lexer
colon :: Parser String
colon = P.colon lexer
dot :: Parser String
dot = P.dot lexer
natural :: Parser Int
natural = fromInteger <$> P.natural lexer

parseFile :: FilePath -> IO (Either ParseError Program)
parseFile path = parseFromFile (whiteSpace *> program) path

type Line = (Symbol,([Symbol],Term))

program :: Parser Program
program = do
    m <- mainDef
    ds <- lines
    let ds' = map (\(f,(xs,t)) -> (f,foldr Lam t xs)) $ M.assocs $ M.fromListWith (\(a,b) (_,d) -> (a,If TF b d)) ds
    case lookup m ds' of
        Just t -> return $ Program (filter (\(x,_) -> x /= m) ds') t
        Nothing -> unexpected $ "undefined main symbol : " ++ m

mainDef :: Parser Symbol
mainDef = reserved "Main" *> colon *> identifier

lines :: Parser [Line]
lines = many1 line

line :: Parser Line
line = do
    l <- identifier
    as <- many identifier
    reservedOp "->"
    t <- term <* dot
    return (l,(as,t))

term :: Parser Term
term = letE <|> 
       funE <|>
       branchE <|> 
       l0E    <|>
       l1E    <|>
       tupleE <|> 
       projE <|> 
       andE <|>
       orE  <|>
       failE <|>
       appE 

l1E :: Parser Term
l1E = reserved "l1" >> primE

l0E :: Parser Term
l0E = reserved "l0" >> primE

letE :: Parser Term
letE = do
    reserved "let"
    x <- identifier
    reservedOp "="
    tx <- term
    reserved "in"
    t <- term
    return (Let x tx t)

funE :: Parser Term
funE = do
    reserved "fun"
    x <- identifier
    reservedOp "->"
    t <- term
    return (Lam x t)


andE :: Parser Term
andE = try $ do
    t1 <- appE
    reservedOp "&&"
    t2 <- appE
    return $ If t1 t2 (C False)

orE :: Parser Term
orE = try $ do
    t1 <- appE
    reservedOp "||"
    t2 <- appE
    return $ If t1 (C True) t2


{-
lam1 :: [[Symbol]] -> Term -> Term
lam1 = flip (foldr Lam)

lamE :: Parser Term
lamE = liftA2 lam1 (reserved "fun" *> many1 args) (reservedOp "->" *> term)
-}

branchE :: Parser Term
branchE = liftA3 If (reserved "if" *> primE) primE primE

{-
nonDetE :: Parser Term
nonDetE = chainl1 appE (reservedOp "<>" *> pure (:+:))
-}

appE :: Parser Term
appE = liftA2 (foldl App) primE (many primE)

tupleE :: Parser Term
tupleE = do
    n <- try $ parens natural 
    ts <- replicateM n primE
    return $ T ts

projE :: Parser Term
projE = do
    reservedOp "#"
    (n,d) <- parens $ liftA2 (,) natural (reservedOp "/" *> natural)
    t <- primE
    return $ Proj (ProjN n) (ProjD d) t


{-
tuple :: Parser [Term]
tuple = parens (commaSep1 term) <|> (pure <$> primE)
-}

primE :: Parser Term
primE = trueE
     <|> falseE
     <|> omegaE
     <|> varE
     <|> unitE
     <|> randE
     <|> parens term

failE :: Parser Term
failE = braces (reserved "fail") >> reservedOp "=>" >> term >> return (Fail "")

trueE,falseE,omegaE,varE,unitE,randE :: Parser Term
trueE = reserved "true" *> pure (C True) 
falseE = reserved "false" *> pure (C False)
omegaE = reservedOp "_|_" *> pure (Omega "")
unitE = reservedOp "(0)" *> pure (T [])
randE = reserved "rand_bool" *> pure TF
varE = V <$> identifier
