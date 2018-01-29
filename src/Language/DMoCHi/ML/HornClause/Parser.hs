module Language.DMoCHi.ML.HornClause.Parser where
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Expr
import Text.Parsec.Language(emptyDef)
import Text.Parsec.String
import Language.DMoCHi.ML.Syntax.PNormal
import qualified Language.DMoCHi.Common.Id as Id 
import qualified Data.Map as M


type Predicate = (Int, [TId], Atom)
parseSolution :: FilePath -> IO (Either ParseError (Maybe [Predicate]))
parseSolution = parseFromFile mainP


reservedNames :: [String]
reservedNames = ["not", "true","false","int","bool"]

language :: P.LanguageDef st
language = emptyDef { P.reservedNames = reservedNames
                    , P.reservedOpNames = ["=","<",">","/\\","\\/","->","<>","+","-",";;","<=",">="]
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
brackets :: Parser a -> Parser a
brackets = P.brackets lexer
whiteSpace :: Parser ()
whiteSpace = P.whiteSpace lexer
colon :: Parser String
colon = P.colon lexer
semi :: Parser String
semi = P.semi lexer
dot :: Parser String
dot = P.dot lexer
comma :: Parser String
comma = P.comma lexer
natural :: Parser Integer
natural = P.natural lexer
semiSep :: Parser a -> Parser [a]
semiSep = P.semiSep lexer
commaSep :: Parser a -> Parser [a]
commaSep = P.commaSep lexer

mainP :: Parser (Maybe [(Int,[TId],Atom)])
mainP = (string "solution:" >> whiteSpace >> (Just <$> many defP) <* eof) 
    <|> (string "no solution." >> whiteSpace >> pure Nothing <* eof)

predP :: Parser Int
predP = do
    many1 (noneOf "[")
    brackets $ do
        i <- natural
        colon
        natural
        return (fromIntegral i)


defP :: Parser (Int,[TId],Atom)
defP = do
    pname <- predP
    xs <- parens (commaSep $ flip TId <$> (Id.reserved <$> identifier) <*> (colon *> typeP))
    reserved "="
    v <- exprP (M.fromList [ (Id.fromReserved (name x), x) | x <- xs ])
    return $ (pname,xs,v)

typeP :: Parser Type
typeP = (TInt <$ reserved "int") <|> (TBool <$ reserved "bool")
      <|> (TInt <$ identifier)

exprP :: M.Map String TId -> Parser Atom
exprP env = it where
    it = buildExpressionParser opTable termP <?> "value"
    opTable = [ [prefix "-" (mkUni SNeg), prefix "+" id, prefix' "not" (mkUni SNot)]
              , [binary "*" (mkBin SMul) AssocLeft, binary "/" (mkBin SDiv) AssocLeft]
              , [binary "+" (mkBin SAdd) AssocLeft, binary "-" (mkBin SSub) AssocLeft]
              , [binary "=" (mkBin SEq)  AssocNone, 
                 binary "<>" (\a b -> mkUni SNot $ mkBin SEq a b) AssocNone,
                 binary "<" (mkBin SLt) AssocNone,
                 binary "<=" (mkBin SLte) AssocNone,
                 binary ">=" (flip $ mkBin SLte) AssocNone,
                 binary ">" (flip $ mkBin SLt) AssocNone]
              , [binary "/\\" (mkBin SAnd) AssocLeft]
              , [binary "\\/" (mkBin SOr) AssocLeft]
              ]
    binary name fun assoc = Infix (reservedOp name >> pure fun) assoc
    prefix name fun       = Prefix (reservedOp name >> pure fun)
    prefix' name fun      = Prefix (reserved name >> pure fun)
    termP = mkVar <$> (fmap (env M.!) identifier) <* optional (parens (pure ()))
        <|> mkLiteral . CInt <$> natural 
        <|> mkLiteral (CBool True) <$ reserved "true" 
        <|> mkLiteral (CBool False) <$ reserved "false"
        <|> parens it

