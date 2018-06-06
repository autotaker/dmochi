module Language.DMoCHi.ML.Parser where
import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as P
import Text.Parsec.Expr
import Language.DMoCHi.ML.Syntax.UnTyped 
import Data.Either
import Control.Monad.Identity

reservedNames :: [String]
reservedNames = ["let","rec","in","and","fun","not",
                 "if","then","else","true","false","assume","assert","fst","snd",
                 "type",
                 "Fail","Main"]

language :: Monad m => P.GenLanguageDef String u m
language = P.LanguageDef { P.commentStart = "(*"
                         , P.commentEnd = "*)"
                         , P.commentLine = ""
                         , P.nestedComments = True
                         , P.identStart = letter <|> char '_'
                         , P.identLetter = alphaNum <|> oneOf "_'"
                         , P.opStart = P.opLetter language
                         , P.opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
                         , P.reservedNames = reservedNames
                         , P.reservedOpNames = ["=","<",">","&&","||","->","<>","+","-",";;","<=",">=","*"]
                         , P.caseSensitive = True }


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

typVar :: Parser String
typVar = char '\'' *> identifier

parseProgramFromFile :: FilePath -> IO (Either ParseError Program)
parseProgramFromFile f = parseFromFile progP f

progP :: Parser Program
progP = do
    (funDefs, synDefs) <- partitionEithers <$> many defP
    e <- exprP
    return $ Program { functions = funDefs
                     , synonyms = synDefs
                     , specs = []
                     , mainTerm = e }

defP :: Parser (Either (AnnotVar String (Maybe Type),TypeScheme,Exp) SynonymDef)
defP = Right <$> synDefP <|> Left <$> funDefP 

funDefP :: Parser (AnnotVar String (Maybe Type),TypeScheme,Exp)
funDefP = try $ do
    x <- reserved "let" *> identifier
    ty <- colon *> typeP
    reservedOp "="
    t <- exprP
    optional (reservedOp ";;")
    return (V x Nothing,toTypeScheme ty,t)

synDefP :: Parser SynonymDef
synDefP = do
    reserved "type"
    tvs <- (\x -> [x]) <$> typVar 
       <|> parens (commaSep1 typVar) 
       <|> pure []
    syn <- identifier
    reservedOp "="
    ty <- typeP
    optional (reservedOp ";;")
    return $ SynonymDef syn tvs ty

exprP :: Parser Exp
exprP = simpleP `chainl1` (reservedOp "<>" >> mkBranch' ) <?> "expr" where
    simpleP = try valueP <|> letP <|> assumeP <|> assertP <|> lambdaP <|> ifP <|> failP <|> omegaP <|> parens exprP
    assumeP = do cond <- (reserved "assume" *> valueP <* semi) 
                 e <- exprP
                 pure $ mkAssume cond e
    mkBranch' = pure mkBranch
    assertP = do
        reserved "assert" 
        v <- termP
        let e2 = mkLiteral CUnit
        let e3 = mkFail
        pure $ mkIf v e2 e3
    ifP = do
        reserved "if"
        pred <- valueP
        reserved "then"
        eThen <- exprP
        reserved "else"
        eElse <- exprP
        pure $ mkIf pred eThen eElse
    lambdaP = do xs <- reserved "fun" *> argsP <* reservedOp "->" 
                 e <- exprP
                 pure $ mkLambda xs e
    argsP = many1 argP 
    argP = (identifier >>= \x -> pure (V x Nothing)) <|> parens (do
                x <- identifier
                reservedOp ":"
                ty <- typeP
                pure (V x (Just ty)))
    failP   = mkFail <$ reserved "Fail"
    omegaP   = mkOmega <$ reserved "Omega"

letP :: Parser Exp
letP = (do reserved "let" 
           cnstr <- (do reserved "rec"
                        mkLetRec <$> sepBy1 bindFunc (reserved "and")) <|> 
                    (uncurry mkLet <$> (try bind <|> bindFunc)) 
           e <- reserved "in" *> exprP
           pure (cnstr e)) <?> "let"
    where 
        bindFunc = do
            f <- identifier
            xs <- many1 identifier
            e  <- reservedOp "=" *> exprP
            let v = mkLambda (map (\x -> V x Nothing) xs) e
            return (V f Nothing, v)
        bind = do 
            x <- identifier
            mty <- optionMaybe $ reservedOp ":" *> typeP
            e <- reservedOp "=" *> (exprP <|> 
                (reservedOp "*" >> return mkRand))
            return (V x mty, e)

valueP :: Parser Exp
valueP = buildExpressionParser opTable termP <?> "value" where
    opTable = [ [fstOrSnd]
              , [prefix "-" SNeg, prefix' "not" SNot]
              , [binary "+" SAdd AssocLeft, binary "-" SSub AssocLeft]
              , [binary "=" SEq AssocNone, 
                 binary "<" SLt AssocNone,
                 binary "<=" SLte AssocNone,
                 binary ">=" SGte AssocNone,
                 binary ">" SGt AssocNone]
              , [binary "&&" SAnd AssocLeft]
              , [binary "||" SOr AssocLeft]
              ]
    binary :: Supported op (BinOps Exp) => String -> SBinOp op -> Assoc -> Operator String () Identity Exp
    binary name op assoc = Infix (mkBinary op <$ reservedOp name) assoc
    prefix, prefix' :: Supported op (UniOps Exp) => String -> SUniOp op  -> Operator String () Identity Exp
    prefix name op       = Prefix (mkUnary op <$ reservedOp name)
    prefix' name op      = Prefix (mkUnary op <$ reserved name)
    fstOrSnd = Postfix $ dot >> ((mkUnary SFst <$ reserved "fst") <|>
                                 (mkUnary SSnd <$ reserved "snd"))

termP :: Parser Exp
termP = varOrApp
    <|> (mkLiteral . CInt <$> natural)
    <|> (mkLiteral (CBool True) <$ reserved "true")
    <|> (mkLiteral (CBool False) <$ reserved "false")
    <|> parens (do p1 <- valueP
                   mp2 <- optionMaybe (comma >> valueP)
                   case mp2 of
                        Nothing -> return p1
                        Just p2 -> pure $ mkPair p1 p2)

argP :: Parser Exp
argP = (mkVar . (\x -> V x Nothing) <$> identifier)
    <|> (mkLiteral . CInt <$> natural)
    <|> (mkLiteral (CBool True) <$ reserved "true")
    <|> (mkLiteral (CBool False) <$ reserved "false")
    <|> parens (do p1 <- valueP
                   mp2 <- optionMaybe (comma >> valueP)
                   case mp2 of
                        Nothing -> return p1
                        Just p2 -> pure $ mkPair p1 p2)

varOrApp :: Parser Exp
varOrApp = do
    f <- identifier
    let l2m [] = Nothing
        l2m vs = Just vs
    l <- try (parens (pure (Just []))) <|> l2m <$> many argP
    case l of
        Nothing -> pure $ mkVar (V f Nothing)
        Just vs -> pure $ mkApp (mkVar (V f Nothing)) vs

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
            [ty] -> foldl (\acc syn -> TSyn [acc] syn) ty <$> many identifier
            tys -> do
                s:ss <- many1 identifier
                return $ foldl (\acc syn -> TSyn [acc] syn) (TSyn tys s) ss
    prim = chainr1 syms (TPair <$ reservedOp "*" )
    func = TFun <$> brackets arglist <*> (reservedOp "->" *> typeP)
    arglist = commaSep prim

