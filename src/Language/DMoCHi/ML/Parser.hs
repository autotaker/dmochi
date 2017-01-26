module Language.DMoCHi.ML.Parser where
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Expr
import Text.Parsec.Language(emptyDef)
import Text.Parsec.String
import Language.DMoCHi.ML.Syntax.UnTyped
import Data.Either

reservedNames :: [String]
reservedNames = ["let","rec","in","and","fun","not",
                 "if","then","else","true","false","assume","assert","fst","snd",
                 "type",
                 "Fail","Main"]

language :: P.LanguageDef st
language = emptyDef { P.commentStart = "(*"
                    , P.commentEnd = "*)"
                    , P.nestedComments = True
                    , P.reservedNames = reservedNames
                    , P.reservedOpNames = ["=","<",">","&&","||","->","<>","+","-",";;","<=",">=","*"]
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
commaSep :: Parser a -> Parser [a]
commaSep = P.commaSep lexer
commaSep1 :: Parser a -> Parser [a]
commaSep1 = P.commaSep1 lexer
natural :: Parser Integer
natural = P.natural lexer
semiSep :: Parser a -> Parser [a]
semiSep = P.semiSep lexer

brackets :: Parser a -> Parser a
brackets = P.brackets lexer

typVar :: Parser Id
typVar = char '\'' *> identifier

parseProgramFromFile :: FilePath -> IO (Either ParseError Program)
parseProgramFromFile = parseFromFile (whiteSpace >> progP)

progP :: Parser Program
progP = uncurry Program . partitionEithers <$> many defP <*> exprP

defP :: Parser (Either (Id,Type,Exp) SynonymDef)
defP = Right <$> synDefP <|> Left <$> funDefP 

funDefP :: Parser (Id,Type,Exp)
funDefP = try $ do
    x <- reserved "let" *> identifier
    ty <- colon *> typeP
    reservedOp "="
    t <- exprP
    optional (reservedOp ";;")
    return (x,ty,t)

synDefP :: Parser SynonymDef
synDefP = do
    reserved "type"
    tvs <- (\x -> [x]) <$> typVar 
       <|> parens (commaSep1 typVar) 
       <|> pure ([])
    syn <- identifier
    reservedOp "="
    ty <- typeP
    optional (reservedOp ";;")
    return $ SynonymDef syn tvs ty

exprP :: Parser Exp
exprP = simpleP `chainl1` (Branch <$ reservedOp "<>") <?> "expr" where
    simpleP = Value <$> (try valueP) <|> letP <|> assumeP <|> assertP <|> lambdaP <|> ifP <|> failP <|> parens exprP
    assumeP = Assume <$> (reserved "assume" *> valueP <* semi) 
                     <*> exprP
    assertP = do
        reserved "assert" 
        v <- termP
        return $ Branch (Assume v (Value (CInt 0))) (Assume (Op (OpNot v)) Fail)
    ifP = do
        reserved "if"
        pred <- valueP
        reserved "then"
        eThen <- exprP
        reserved "else"
        eElse <- exprP
        return $ Branch (Assume pred eThen) (Assume (Op (OpNot pred)) eElse)
    lambdaP = Lambda <$> (reserved "fun" *> argsP <* reservedOp "->") 
                     <*> exprP
    argsP = parens (pure []) <|> many1 identifier
    failP   = Fail <$ reserved "Fail"

letP :: Parser Exp
letP = (Let <$> (reserved "let" *> identifier)
           <*> sub
           <*> (reserved "in" *> exprP)) <?> "let"
    where sub = LExp <$> (reservedOp ":" *> typeP) <*> (reservedOp "=" *> exprP)
            <|> (reservedOp "=" *> (LValue <$> valueP <|> LRand <$ reservedOp "*"))

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
termP = varOrApp
    <|> CInt <$> natural 
    <|> CBool True <$ reserved "true" 
    <|> CBool False <$ reserved "false"
    <|> parens (do p1 <- valueP
                   mp2 <- optionMaybe (comma >> valueP)
                   case mp2 of
                        Nothing -> return p1
                        Just p2 -> return $ Pair p1 p2)
argP :: Parser Value
argP = Var <$> identifier
    <|> CInt <$> natural 
    <|> CBool True <$ reserved "true" 
    <|> CBool False <$ reserved "false"
    <|> parens (do p1 <- valueP
                   mp2 <- optionMaybe (comma >> valueP)
                   case mp2 of
                        Nothing -> return p1
                        Just p2 -> return $ Pair p1 p2)

varOrApp :: Parser Value
varOrApp = do
    f <- identifier
    let l2m [] = Nothing
        l2m vs = Just vs
    l <- try (parens (pure (Just []))) <|> l2m <$> many argP
    case l of
        Nothing -> return $ Var f
        Just vs -> return $ App f vs

typeP :: Parser Type
typeP = prim <|> func 
    where
    base = TInt <$ reserved "int"
       <|> TBool <$ reserved "bool"
       <|> TVar <$> typVar
       <|> TSyn [] <$> identifier
       -- <|> parens typeP
    syms = do
        tys <- parens (commaSep1 typeP) <|> (\x -> [x]) <$> base
        case tys of
            [ty] -> do
                ss <- many identifier
                return $ foldl (\acc syn -> TSyn [acc] syn) ty ss
            tys -> do
                s:ss <- many1 identifier
                return $ foldl (\acc syn -> TSyn [acc] syn) (TSyn tys s) ss
    prim = chainr1 syms (TPair <$ reservedOp "*" )
    func = TFun <$> brackets arglist <*> (reservedOp "->" *> typeP)
    arglist = commaSep prim

