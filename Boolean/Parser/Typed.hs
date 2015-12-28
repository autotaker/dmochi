
module Boolean.Parser.Typed where
import Text.Parsec 
import qualified Text.Parsec.Token as P
import Control.Applicative hiding((<|>),many)
import Boolean.Syntax.Typed
import Control.Monad.Fix
import Control.Monad.Reader
import qualified Data.Map as M
import Prelude hiding(lines)

reservedNames :: [String]
reservedNames = 
    ["let","in","fun", "true","false", "fail","assume","not","Bool","X"]

language :: P.GenLanguageDef String () (Reader (M.Map String Symbol))
language    = P.LanguageDef
               { P.commentStart   = "(*"
               , P.commentEnd     = "*)"
               , P.commentLine    = ""
               , P.nestedComments = True
               , P.identStart     = letter <|> char '_'
               , P.identLetter    = alphaNum <|> oneOf "_'"
               , P.opStart        = P.opLetter language
               , P.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
               , P.reservedOpNames = ["=","->","||","&&","/","<>","<+>",";;"]
               , P.reservedNames  = reservedNames
               , P.caseSensitive  = True
               }

lexer :: P.GenTokenParser String () (Reader (M.Map String Symbol))
lexer = P.makeTokenParser language

reserved :: String -> Parser ()
reserved = P.reserved lexer
identifier :: Parser String
identifier = P.identifier lexer
reservedOp :: String -> Parser ()
reservedOp = P.reservedOp lexer
parens :: Parser a -> Parser a
parens = P.parens lexer
brackets :: Parser a -> Parser a
brackets = P.brackets lexer
whiteSpace :: Parser ()
whiteSpace = P.whiteSpace lexer
colon :: Parser String
colon = P.colon lexer
comma :: Parser String
comma = P.comma lexer
dot :: Parser String
dot = P.dot lexer
semi :: Parser String
semi = P.semi lexer
natural :: Parser Int
natural = fromInteger <$> P.natural lexer

type Parser a = ParsecT String () (Reader (M.Map String Symbol)) a

parseFile :: FilePath -> IO (Either ParseError Program)
parseFile path = do
    input <- readFile path
    let m = runParserT (whiteSpace *> program) () path input
    return $ fix $ \x -> 
        let env = case x of
                    Left _ -> undefined
                    Right p -> M.fromList [(name d,d) | (d,_) <- definitions p] in
        runReader m env

program :: Parser Program
program = Program <$> many (try functionDef) <*> mainDef

list :: Parser a -> Parser [a]
list p = brackets $ p `sepBy` comma

sortP :: Parser Sort
sortP = foldr1 (:->) <$> sepBy1 atom (reservedOp "->") where
    atom = X <$ reserved "X" <|>
           Bool <$ reserved "Bool" <|>
           Tuple <$> list sortP <|>
           parens sortP <?> "sort"
        
termP :: Parser Term 
termP = expr where
    lamP = do
        x <- (reserved "fun" *> parens symbolP <* reservedOp "->")
        t <- local (M.insert (name x) x) expr
        return $ Lam x t
    letP = do
        x <- reserved "let" *> symbolP <* reservedOp "="
        tx <- expr <* reserved "in"
        t <- local (M.insert (name x) x) expr
        return $ f_let x tx t
    assumeP = f_assume <$> (reserved "assume" *> expr <* semi)
                       <*> expr
    branchP = do
        x <- expr1
        xs <- many ((,) <$> (f_branch <$ reservedOp "<>" <|> f_branch_label <$ reservedOp "<+>")
                        <*> expr1)
        return $ foldl (\acc (f,v) -> f acc v) x xs
    trueP = C True <$ reserved "true"
    falseP = C False <$ reserved "false"
    varP  = do
        x <- identifier
        env <- ask
        return $ V $ env M.! x
    failP = (\t -> Fail (Symbol t "")) <$> (reserved "fail" *> parens sortP)
    projP = dot *> parens (f_proj <$> natural <*> (reservedOp "/" *> natural))
    tupleP = T <$> do
        n <- natural 
        replicateM n expr4
    expr = lamP <|> letP <|> assumeP <|> branchP  <?> "expr"
    expr1 = (foldl1 f_or <$> expr2 `sepBy1` reservedOp "||") <?> "or"
    expr2 = (foldl1 f_and <$> expr3 `sepBy1` reservedOp "&&") <?> "and"
    expr3 = f_not <$> (reserved "not" *> expr4) <|> 
            foldl1 f_app <$> many1 expr4 
            <?> "app"
    expr4 = (foldl (flip ($)) <$> atom <*> many projP) <?> "proj"
    atom = trueP <|> falseP <|> failP <|> varP <|>
           parens (tupleP <|> expr) <?> "atom"

symbolP :: Parser Symbol
symbolP = flip Symbol <$> identifier <* colon <*> sortP

functionDef :: Parser (Symbol,Term)
functionDef = 
    liftA2 (,) (reserved "let" *> symbolP <* reservedOp "=")
               (termP <* reservedOp ";;")

mainDef :: Parser Term
mainDef = termP

