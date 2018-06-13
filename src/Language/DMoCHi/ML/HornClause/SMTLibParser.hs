module Language.DMoCHi.ML.HornClause.SMTLibParser where

import Text.Parsec

import qualified Language.DMoCHi.Common.Id as Id
import Language.DMoCHi.Common.Util
import qualified Text.Parsec.Token as P
import qualified Data.Map as M
--import Text.Parsec.String
import Language.DMoCHi.ML.Syntax.Atom
import Control.Monad.Trans(lift)
import Control.Monad
import qualified Z3.Monad as Z3
import qualified Language.DMoCHi.ML.SMT as SMT
import qualified Text.PrettyPrint.HughesPJClass as PP
import Control.Monad.IO.Class

type Parser a = ParsecT String () (SMT.SMT (LoggingT IO)) a
instance Z3.MonadZ3 m => Z3.MonadZ3 (ParsecT s u m) where
  getContext = lift Z3.getContext
  getSolver  = lift Z3.getSolver

instance Z3.MonadZ3 m => Z3.MonadZ3 (LoggingT m) where
  getContext = lift Z3.getContext
  getSolver  = lift Z3.getSolver

instance MonadLogger m => MonadLogger (ParsecT s u m)
instance MonadLoggerIO m => MonadLoggerIO (ParsecT s u m)


parseSolution :: FilePath -> LoggingT IO (Either ParseError (Maybe [(Int, [TId], Atom)]))
parseSolution path = do
  content <- liftIO $ readFile path
  SMT.runSMT $ runParserT mainP () path content

language :: P.GenLanguageDef String () (SMT.SMT (LoggingT IO))
language = P.LanguageDef {
    P.reservedNames = ["sat", "unsat", "model", "define-fun" 
                      , "exists", "forall"
                      ,"Int", "Bool", "and", "or", "not"]
  , P.reservedOpNames = ["=","<",">","->","<>","+","-","<=",">="]
  , P.caseSensitive = True
  , P.commentStart = ""
  , P.commentEnd = ""
  , P.commentLine = ""
  , P.nestedComments = False
  , P.identStart = oneOf $ ['a'..'z'] ++ ['A'..'Z'] ++ "'_"
  , P.identLetter = P.identStart language <|> oneOf (['0'..'9'] ++ "!")
  , P.opStart = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , P.opLetter = P.opStart language
}

lexer = P.makeTokenParser language
reserved = P.reserved lexer
parens = P.parens lexer
reservedOp = P.reservedOp lexer

identifier :: Parser String
identifier = P.identifier lexer <|>
  char '|' *> many1 (noneOf "|") <* char '|' <* P.whiteSpace lexer

natural :: Parser Integer
natural = P.natural  lexer

mainP :: Parser (Maybe [(Int, [TId], Atom)])
mainP = 
  (Just <$ reserved "sat") <*> parens (reserved "model" *>
    let defs penv = (do
          (pName, xs, body, ast) <- defP penv
          ((parsePred pName, xs, body) :) <$> defs (M.insert pName ast penv)) <|> pure []
    in defs M.empty)
  <|> (Nothing <$ reserved "unsat" )

parsePred :: String -> Int
parsePred str =
  case dropWhile (/='[') str of
    '[': str -> read (takeWhile (/=':') str)
    _ -> error $ "parsePred: " ++ str


defP :: M.Map String Z3.AST -> Parser (String, [TId], Atom, Z3.AST)
defP pEnv = parens $ do
  reserved "define-fun"
  pred <- identifier
  args <- argsP
  reserved "Bool"
  body <- termP pEnv args >>= Z3.simplify
  xs <- forM args $ \(name, sort) -> do
    ty <- fromSort sort
    return $ TId ty (Id.reserved name)
  atom <- fromAST (M.fromList (zip [0..] xs)) body
  return (pred, xs, atom, body)

fromSort :: Z3.MonadZ3 m => Z3.Sort -> m Type
fromSort sort = Z3.getSortKind sort >>= \case
  Z3.Z3_BOOL_SORT -> return TBool
  Z3.Z3_INT_SORT -> return TInt
  _ -> error $ "non-supported sort" ++ show sort

argsP :: Parser [(String, Z3.Sort)]
argsP = parens $ many argP

argP :: Parser (String, Z3.Sort)
argP = parens $ (,) <$> identifier <*> typeP

var :: [(String, Z3.Sort)] -> String -> Parser Z3.AST
var = go 0 where
  go i ((x, s):env) y 
    | x == y = Z3.mkBound i s
    | otherwise = go (i+1) env y
  go _ [] y = parserFail $ "undefined variable:" ++ y

fromAST :: Z3.MonadZ3 m => M.Map Int TId -> Z3.AST -> m Atom
fromAST env ast = 
  Z3.getAstKind ast >>= \case
    Z3.Z3_NUMERAL_AST -> 
      mkLiteral . CInt . read <$> Z3.getNumeralString ast
    Z3.Z3_APP_AST -> do
      app <- Z3.toApp ast
      fname <- Z3.getAppDecl app >>= Z3.getDeclName >>= Z3.getSymbolString
      args <- Z3.getAppArgs app >>= mapM (fromAST env)
      case (fname, args) of
        ("+", vs) -> return $ foldl1 (mkBin SAdd) vs
        ("-", [v]) -> return $ mkUni SNeg v
        ("*", vs) -> return $ foldl1 (mkBin SMul) vs
        ("div", [v1, v2]) -> return $ mkBin SDiv v1 v2
        ("true", []) -> return $ mkLiteral $ CBool True
        ("false", []) -> return $ mkLiteral $ CBool False
        ("=", [v1,v2]) -> return $ mkBin SEq v1 v2
        ("<=", [v1, v2]) -> return $ mkBin SLte v1 v2
        (">=", [v1, v2]) -> return $ mkBin SGte v1 v2
        ("<", [v1, v2]) -> return $ mkBin SLt v1 v2
        (">", [v1, v2]) -> return $ mkBin SGt v1 v2
        ("not", [v1]) -> return $ mkUni SNot v1
        ("and", vs) -> return $ foldl1 (mkBin SAnd) vs
        ("or", vs)  -> return $ foldl1 (mkBin SOr)  vs
        _ -> error $ "non-supported ast:" ++ show app
    Z3.Z3_VAR_AST -> do 
      i <- Z3.getIndexValue ast
      return $ mkVar $ env M.! i
    Z3.Z3_QUANTIFIER_AST -> undefined
    _ -> undefined

qe :: (Z3.MonadZ3 m, MonadLogger m) => Z3.AST -> m Z3.AST
qe ast = do
  tactic <- Z3.mkQuantifierEliminationTactic
  goal <- Z3.mkGoal False False False
  Z3.goalAssert goal ast
  appRes <- Z3.applyTactic tactic goal
  [goal] <- Z3.getApplyResultSubgoals appRes
  formulas <- Z3.getGoalFormulas goal
  --l <- mapM Z3.astToString formulas 
  ast' <- Z3.mkAnd formulas
  ast_str <- Z3.astToString ast
  ast'_str <- Z3.astToString ast'
  let doc = PP.braces $ 
              PP.text "input:" PP.<+> PP.text ast_str PP.$+$
              PP.text "result:" PP.<+> PP.text ast'_str
  logPretty "SMTLibParser" LevelDebug "QE" (PPrinted doc)
  return ast'


termP :: M.Map String Z3.AST -> [(String, Z3.Sort)] -> Parser Z3.AST
termP penv env = 
        (natural >>= Z3.mkInteger)
    <|> (reserved "true" *> Z3.mkTrue) 
    <|> (reserved "false" *> Z3.mkFalse)
    <|> (identifier >>= var env)
    <|> parens (parseOp opList <|> predApp <|> exists <|> forall)
    where
    opList = [(reserved "and",  Z3.mkAnd)
             ,(reserved "or",   Z3.mkOr)
             ,(reserved "not",  unary Z3.mkNot)
             ,(reservedOp "=",  binary Z3.mkEq)
             ,(reservedOp "<=", binary Z3.mkLe)
             ,(reservedOp "<",  binary Z3.mkLt)
             ,(reservedOp ">=", binary Z3.mkGe)
             ,(reservedOp ">",  binary Z3.mkGt)
             ,(reservedOp "+",  Z3.mkAdd)
             ,(reservedOp "-",  unaryOrMany Z3.mkUnaryMinus Z3.mkSub)
             ,(reservedOp "*",  Z3.mkMul)
             ,(reservedOp "div",  binary Z3.mkDiv)
             ]
    binary f [a,b] = f a b
    binary _ _ = parserFail "expect binary"
    unary f [a] = f a
    unary _ _ = parserFail "expect unary"
    unaryOrMany uni _ [a] = uni a
    unaryOrMany _ bin l = bin l
    parseOp [] = parserFail "unexpected op"
    parseOp ((opP, action):opList) =
      (opP >> many (termP penv env) >>= action) <|> parseOp opList
    predApp = do
      f <- identifier
      args <- many (termP penv env)
      case M.lookup f penv of
        Just body -> Z3.substituteVars body args >>= Z3.simplify
        Nothing -> parserFail $ "predApp: undefined predicate: " ++ f
    exists = do
      xs <- reserved "exists" *> argsP 
      let env' = reverse xs ++ env
      let (names, sorts) = unzip xs
      symbols <- mapM Z3.mkStringSymbol names
      body <- termP penv env'
      term <- Z3.mkExists [] symbols sorts body
      qe term
    forall = do
      xs <- reserved "forall" *> argsP 
      let env' = reverse xs ++ env
      let (names, sorts) = unzip xs
      symbols <- mapM Z3.mkStringSymbol names
      body <- termP penv env'
      term <- Z3.mkForall [] symbols sorts body
      qe term
      


typeP :: Parser Z3.Sort
typeP = (reserved "Int" *> lift Z3.mkIntSort) 
    <|> (reserved "Bool" *> lift Z3.mkBoolSort)


