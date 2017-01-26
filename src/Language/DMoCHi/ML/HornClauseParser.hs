module Language.DMoCHi.ML.HornClauseParser where
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Expr
import Text.Parsec.Language(emptyDef)
import Text.Parsec.String
import Language.DMoCHi.ML.Syntax.PNormal
import qualified Data.Map as M

parseSolution :: FilePath -> IO (Either ParseError [(Int,[Id],AValue)])
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

mainP :: Parser [(Int,[Id],AValue)]
mainP = string "solution:" >> whiteSpace >> many defP <* eof

predP :: Parser Int
predP = do
    many1 (noneOf "[")
    brackets $ do
        i <- natural
        colon
        natural
        return (fromIntegral i)


defP :: Parser (Int,[Id],AValue)
defP = do
    pname <- predP
    xs <- parens (commaSep $ flip Id <$> identifier <*> (colon *> typeP))
    reserved "="
    v <- exprP (M.fromList [ (name x, getType x) | x <- xs ])
    return $ (pname,xs,v)

typeP :: Parser Type
typeP = (TInt <$ reserved "int") <|> (TBool <$ reserved "bool")
      <|> (TInt <$ identifier)

exprP :: M.Map String Type -> Parser AValue
exprP env = it where
    it = buildExpressionParser opTable termP <?> "value"
    opTable = [ [prefix "-" (after Op neg), prefix "+" id, prefix' "not" (after Op OpNot)]
              , [binary "*" scalar AssocNone]
              , [binary "+" (after2 Op OpAdd) AssocLeft, binary "-" (after2 Op OpSub) AssocLeft]
              , [binary "=" (after2 Op OpEq)  AssocNone, 
                 binary "<>" (\a b -> Op $ OpNot $ Op $ OpEq a b) AssocNone,
                 binary "<" (after2 Op OpLt) AssocNone,
                 binary "<=" (after2 Op OpLte) AssocNone,
                 binary ">=" (after2 Op (flip OpLte)) AssocNone,
                 binary ">" (after2 Op (flip OpLt)) AssocNone]
              , [binary "/\\" (after2 Op OpAnd) AssocLeft]
              , [binary "\\/" (after2 Op OpOr) AssocLeft]
              ]
    neg = OpSub (CInt 0)
    after2 = (.) . (.)
    after = (.)
    binary name fun assoc = Infix (reservedOp name >> pure fun) assoc
    prefix name fun       = Prefix (reservedOp name >> pure fun)
    prefix' name fun      = Prefix (reserved name >> pure fun)
    scalar (CInt c) t = foldl1 (after2 Op OpAdd) [ t | _ <- [1..c]]
    scalar _ _ = error "exprP: scalar: non-linear term is unsupported"
    termP = Var <$> (fmap (\x -> Id (env M.! x) x) identifier) <* optional (parens (pure ()))
        <|> CInt <$> natural 
        <|> CBool True <$ reserved "true" 
        <|> CBool False <$ reserved "false"
        <|> parens it

