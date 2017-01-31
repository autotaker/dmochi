{-# LANGUAGE BangPatterns #-}
module Language.DMoCHi.ML.Parser where
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Expr
import Language.DMoCHi.ML.Syntax.UnTyped 
import Language.DMoCHi.Common.Id(FreshT,UniqueKey, runFresh)
import Data.Either
import Data.Functor.Identity

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


type Parser a = ParsecT String [(UniqueKey,Type)] (FreshT Identity) a

type UserState = [(UniqueKey, Type)]
type UserMonad = [(UniqueKey, Type)]

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
parseProgramFromFile f = do
    input <- readFile f
    return $ runFresh (runParserT progP [] f input)

progP :: Parser Program
progP = do
    (funDefs, synDefs) <- partitionEithers <$> many defP
    e <- exprP
    annots <- getState
    return $ Program { functions = funDefs
                     , synonyms = synDefs
                     , typeAnn = annots
                     , mainTerm = e }

defP :: Parser (Either (String,Type,Exp) SynonymDef)
defP = Right <$> synDefP <|> Left <$> funDefP 

funDefP :: Parser (String,Type,Exp)
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
exprP = simpleP `chainl1` (reservedOp "<>" >> mkBranch' ) <?> "expr" where
    simpleP = try valueP <|> letP <|> assumeP <|> assertP <|> lambdaP <|> ifP <|> failP <|> omegaP <|> parens exprP
    assumeP = do cond <- (reserved "assume" *> valueP <* semi) 
                 e <- exprP
                 mkAssume cond e
    assertP = do
        reserved "assert" 
        v <- termP
        e2 <- mkLiteral (CInt 0)
        e3 <- mkFail
        mkIf v e2 e3
    ifP = do
        reserved "if"
        pred <- valueP
        reserved "then"
        eThen <- exprP
        reserved "else"
        eElse <- exprP
        mkIf pred eThen eElse
    lambdaP = do xs <- reserved "fun" *> argsP <* reservedOp "->" 
                 e <- exprP
                 mkLambda xs e
    argsP = parens (pure []) <|> many1 identifier
    failP   = reserved "Fail" >> mkFail
    omegaP   = reserved "Omega" >> mkOmega

letP :: Parser Exp
letP = (do x <- reserved "let" *> identifier
           e1 <- sub
           e2 <- reserved "in" *> exprP
           mkLet x e1 e2) <?> "let"
    where sub = (do ty <- reservedOp ":" *> typeP 
                    e1 <- reservedOp "=" *> exprP
                    let !key = getKey e1
                    modifyState ((key, ty):)
                    return e1) <|> 
                (reservedOp "=" *> (valueP <|> (reservedOp "*" >> mkRand)))

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
    binary :: Supported op (BinOps Exp) => String -> SBinOp op -> Assoc -> Operator String [(UniqueKey,Type)] (FreshT Identity) Exp
    binary name op assoc = Infix (reservedOp name >> mkBinary' op) assoc
    prefix, prefix' :: Supported op (UniOps Exp) => String -> SUniOp op  -> Operator String [(UniqueKey,Type)] (FreshT Identity) Exp
    prefix name op       = Prefix (reservedOp name >> mkUnary' op)
    prefix' name op      = Prefix (reserved name >> mkUnary' op)
    fstOrSnd = Postfix $ dot >> ((reserved "fst" >> mkUnary' SFst) <|>
                                 (reserved "snd" >> mkUnary' SSnd))

termP :: Parser Exp
termP = varOrApp
    <|> (natural >>= mkLiteral . CInt)
    <|> (reserved "true" >> mkLiteral (CBool True))
    <|> (reserved "false" >> mkLiteral (CBool False))
    <|> parens (do p1 <- valueP
                   mp2 <- optionMaybe (comma >> valueP)
                   case mp2 of
                        Nothing -> return p1
                        Just p2 -> mkPair p1 p2)

argP :: Parser Exp
argP = (identifier >>= mkVar)
    <|> (natural >>= mkLiteral . CInt)
    <|> (reserved "true" >> mkLiteral (CBool True))
    <|> (reserved "false" >> mkLiteral (CBool False))
    <|> parens (do p1 <- valueP
                   mp2 <- optionMaybe (comma >> valueP)
                   case mp2 of
                        Nothing -> return p1
                        Just p2 -> mkPair p1 p2)

varOrApp :: Parser Exp
varOrApp = do
    f <- identifier
    let l2m [] = Nothing
        l2m vs = Just vs
    l <- try (parens (pure (Just []))) <|> l2m <$> many argP
    case l of
        Nothing -> mkVar f
        Just vs -> mkApp f vs

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

