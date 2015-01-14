module ML.Parser where
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Expr
import Text.Parsec.Language(emptyDef)
import Text.Parsec.String
import Control.Applicative hiding((<|>),many)
import ML.Syntax

reservedNames :: [String]
reservedNames = ["let","rec","in","and","fun","not",
                 "if","then","else","true","false","assume",
                 "Fail","Main"]

language :: P.LanguageDef st
language = emptyDef { P.commentStart = "(*"
                    , P.commentEnd = "*)"
                    , P.nestedComments = True
                    , P.reservedNames = reservedNames
                    , P.reservedOpNames = ["=","<","&&","||","->","<>","+","-"]
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
natural :: Parser Integer
natural = P.natural lexer
semiSep :: Parser a -> Parser [a]
semiSep = P.semiSep lexer
brackets :: Parser a -> Parser a
brackets = P.brackets lexer

exprP :: Parser Exp
exprP = simpleP `chainl1` (Branch <$ reservedOp "<>") where
    simpleP = Value <$> valueP <|> letP <|> assumeP <|> lambdaP <|> failP <|> parens exprP
    assumeP = Assume <$> (reserved "assume" *> valueP <* semi) 
                     <*> exprP
    lambdaP = Lambda <$> (reserved "fun" *> identifier <* reservedOp "->") 
                     <*> exprP
    failP   = Fail <$ reserved "Fail"

letP :: Parser Exp
letP = Let <$> (reserved "let" *> identifier)
           <*> sub
           <*> (reserved "in" *> exprP)
    where sub = LExp <$> (reservedOp ":" *> ptypeP) <*> (reservedOp "=" *> exprP)
            <|> try (LApp <$> (reservedOp "=" *> identifier) <*> many1 termP)
            <|> LValue <$> (reservedOp "=" *> valueP)

valueP :: Parser Value
valueP = buildExpressionParser opTable termP where
    opTable = [ [prefix "-" (after Op OpNeg), prefix "+" id, prefix' "not" (after Op OpNot)]
              , [binary "+" (after2 Op OpAdd) AssocLeft, binary "-" (after2 Op OpSub) AssocLeft]
              , [binary "=" (after2 Op OpEq)  AssocNone, 
                 binary "<" (after2 Op OpLt) AssocNone,
                 binary ">" (after2 Op OpGt) AssocNone]
              , [binary "&&" (after2 Op OpAnd) AssocLeft]
              , [binary "||" (after2 Op OpOr) AssocLeft]
              ]
    after2 = (.) . (.)
    after = (.)
    binary name fun assoc = Infix (reservedOp name >> pure fun) assoc
    prefix name fun       = Prefix (reservedOp name >> pure fun)
    prefix' name fun      = Prefix (reserved name >> pure fun)


termP :: Parser Value
termP = Var <$> identifier 
    <|> CInt <$> natural 
    <|> CBool True <$ reserved "true" 
    <|> CBool False <$ reserved "false"
    <|> parens valueP

ptypeP :: Parser PType
ptypeP = base PInt "int" <|> base PBool "bool" <|> func where
    base cstr ty = cstr <$> (reserved ty *> option [] (brackets $ semiSep predicateP))
    func = f <$> identifier <*> (reservedOp ":" *> ptypeP) <*> (reservedOp "->" *> ptypeP)
    f x ty1 ty2 = PFun ty1 (g x ty2)
    g :: Id -> PType -> (Value -> PType)
    g x (PInt ps)      v = PInt (map (substV x v.) ps)
    g x (PBool ps)     v = PBool (map (substV x v.) ps)
    g x (PFun ty ty_f) v = PFun (g x ty v) (\w -> g x (ty_f w) v)

predicateP :: Parser Predicate
predicateP = f <$> identifier <*> (dot *> valueP) where
    f :: Id -> Value -> Predicate
    f x (Var y) | x == y = id
    f x (Op op)          = \v -> Op $ fmap (($v).f x) op
    f _ v                = const v

