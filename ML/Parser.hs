module ML.Parser where
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Expr
import Text.Parsec.Language(emptyDef)
import Text.Parsec.String
import Control.Applicative hiding((<|>),many,optional)
import ML.Syntax.UnTyped

reservedNames :: [String]
reservedNames = ["let","rec","in","and","fun","not",
                 "if","then","else","true","false","assume","fst","snd",
                 "Fail","Main"]

language :: P.LanguageDef st
language = emptyDef { P.commentStart = "(*"
                    , P.commentEnd = "*)"
                    , P.nestedComments = True
                    , P.reservedNames = reservedNames
                    , P.reservedOpNames = ["=","<",">","&&","||","->","<>","+","-",";;","<=",">="]
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

brackets :: Parser a -> Parser a
brackets = P.brackets lexer

parseProgramFromFile :: FilePath -> IO (Either ParseError Program)
parseProgramFromFile = parseFromFile (whiteSpace >> progP)

progP :: Parser Program
progP = Program <$> many defP <*> exprP

defP :: Parser (Id,PType,Exp)
defP = try $ do
    x <- reserved "let" *> identifier
    ty <- colon *> ptypeP
    reservedOp "="
    t <- exprP
    optional (reservedOp ";;")
    return (x,ty,t)

exprP :: Parser Exp
exprP = simpleP `chainl1` (Branch <$ reservedOp "<>") <?> "expr" where
    simpleP = Value <$> (try valueP) <|> letP <|> assumeP <|> lambdaP <|> failP <|> parens exprP
    assumeP = Assume <$> (reserved "assume" *> valueP <* semi) 
                     <*> exprP
    lambdaP = Lambda <$> (reserved "fun" *> identifier <* reservedOp "->") 
                     <*> exprP
    failP   = Fail <$ reserved "Fail"

letP :: Parser Exp
letP = (Let <$> (reserved "let" *> identifier)
           <*> sub
           <*> (reserved "in" *> exprP)) <?> "let"
    where sub = LExp <$> (reservedOp ":" *> ptypeP) <*> (reservedOp "=" *> exprP)
            <|> try (LApp <$> (reservedOp "=" *> identifier) <*> many1 termP)
            <|> LValue <$> (reservedOp "=" *> valueP)

valueP :: Parser Value
valueP = buildExpressionParser opTable termP <?> "value" where
    opTable = [ [fstOrSnd]
              , [prefix "-" (after Op OpNeg), prefix "+" id, prefix' "not" (after Op OpNot)]
              , [binary "+" (after2 Op OpAdd) AssocLeft, binary "-" (after2 Op OpSub) AssocLeft]
              , [binary "=" (after2 Op OpEq)  AssocNone, 
                 binary "<" (after2 Op OpLt) AssocNone,
                 binary "<=" (after2 Op OpLte) AssocNone,
                 binary ">=" (after2 Op OpGte) AssocNone,
                 binary ">" (after2 Op OpGt) AssocNone]
              , [binary "&&" (after2 Op OpAnd) AssocLeft]
              , [binary "||" (after2 Op OpOr) AssocLeft]
              ]
    after2 = (.) . (.)
    after = (.)
    binary name fun assoc = Infix (reservedOp name >> pure fun) assoc
    prefix name fun       = Prefix (reservedOp name >> pure fun)
    prefix' name fun      = Prefix (reserved name >> pure fun)
    fstOrSnd = Postfix $ dot >> ((reserved "fst" >> pure (Op . OpFst)) <|>
                                 (reserved "snd" >> pure (Op . OpSnd)))

termP :: Parser Value
termP = Var <$> identifier 
    <|> CInt <$> natural 
    <|> CBool True <$ reserved "true" 
    <|> CBool False <$ reserved "false"
    <|> parens (do p1 <- valueP
                   mp2 <- optionMaybe (comma >> valueP)
                   case mp2 of
                        Nothing -> return p1
                        Just p2 -> return $ Pair p1 p2)

ptypeP :: Parser PType
ptypeP = base PInt "int" 
     <|> base PBool "bool" 
     <|> try pair
     <|> func 
     <|> parens ptypeP where
    base cstr ty = cstr <$> (reserved ty *> option [] (brackets $ semiSep predicateP))
    func = g PFun  <$> identifier <*> (reservedOp ":" *> ptypeP) <*> (reservedOp "->" *> ptypeP)
    pair = g PPair <$> identifier <*> (reservedOp ":" *> ptypeP) <*> (reservedOp "*"  *> ptypeP)
    g f x ty1 ty2 = f ty1 (x,ty2)

predicateP :: Parser Predicate
predicateP = (,) <$> identifier <*> (dot *> valueP) where

