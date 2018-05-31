module Language.DMoCHi.ML.HornClause.SMTLibParser where

import Text.Parsec

import qualified Language.DMoCHi.Common.Id as Id
import qualified Text.Parsec.Token as P
import qualified Data.Map as M
import Text.Parsec.String
import Text.Parsec.Language(emptyDef)
import Language.DMoCHi.ML.Syntax.Atom

parseSolution :: FilePath -> IO (Either ParseError (Maybe [(Int, [TId], Atom)]))
parseSolution = parseFromFile mainP

reservedNames :: [String]
reservedNames = ["sat", "unsat", "model", "define-fun"
                ,"Int", "Bool", "and", "or", "not"]
language :: P.LanguageDef st
language = emptyDef { P.reservedNames = reservedNames
                    , P.reservedOpNames = ["=","<",">","->","<>","+","-","<=",">="]
                    , P.caseSensitive = True }
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
          (pName, xs, body) <- defP penv
          ((parsePred pName, xs, body) :) <$> defs (M.insert pName (xs, body) penv)) <|> pure []
    in defs M.empty)
  <|> (Nothing <$ reserved "unsat" )

parsePred :: String -> Int
parsePred str =
  case dropWhile (/='[') str of
    '[': str -> read (takeWhile (/=':') str)
    _ -> error $ "parsePred: " ++ str


defP :: M.Map String ([TId], Atom) -> Parser (String, [TId], Atom)
defP pEnv = parens $ do
  reserved "define-fun"
  pred <- identifier
  args <- argsP
  reserved "Bool"
  let env = M.fromList [ (Id.getName (name x), mkVar x)| x <- args ]
  body <- termP pEnv env
  return (pred, args, body)

argsP :: Parser [TId]
argsP = parens $ many argP

argP :: Parser TId
argP = parens $ mkTId <$> identifier <*> typeP
  where
  mkTId str ty = TId ty (Id.reserved str)

termP :: M.Map String ([TId], Atom) -> M.Map String Atom -> Parser Atom
termP penv env =
        mkLiteral . CInt <$> natural
    <|> mkLiteral . CBool <$> (True <$ reserved "true"  <|> False <$ reserved "false")
    <|> (env M.!) <$> identifier
    <|> parens (parseOp opList <|> predApp)
    where
    opList = [(reserved "and",  leftAssoc (mkBin SAnd))
             ,(reserved "or",   leftAssoc (mkBin SOr))
             ,(reserved "not",  unary (mkUni SNot))
             ,(reservedOp "=",  binary (mkBin SEq))
             ,(reservedOp "<=", binary (mkBin SLte))
             ,(reservedOp "<",  binary (mkBin SLt))
             ,(reservedOp ">=", binary (mkBin SGte))
             ,(reservedOp ">",  binary (mkBin SGt))
             ,(reservedOp "+",  leftAssoc (mkBin SAdd))
             ,(reservedOp "-",  unaryOrBinary (mkUni SNeg) (mkBin SSub))
             ,(reservedOp "*",  binary (mkBin SMul))
             ,(reservedOp "/",  binary (mkBin SDiv))
             ]
    binary f [a,b] = pure $ f a b
    binary _ _ = parserFail "expect binary"
    leftAssoc f [] = parserFail "empty"
    leftAssoc f l = pure $ foldl1 f l
    unary f [a] = pure $ f a
    unary _ _ = parserFail "expect unary"
    unaryOrBinary uni _ [a] = pure $ uni a
    unaryOrBinary _ bin [a,b] = pure $ bin a b
    unaryOrBinary _ _ _ = parserFail "expect unary or binary"
    parseOp [] = parserFail "unexpected op"
    parseOp ((opP, action):opList) =
      (opP >> many (termP penv env) >>= action) <|> parseOp opList
    predApp = do
      f <- identifier
      args <- many (termP penv env)
      case M.lookup f penv of
        Just (xs, body) -> pure $ substAFormula (M.fromList $ zip xs args) body
        Nothing -> parserFail $ "predApp: undefined predicate: " ++ f


typeP :: Parser Type
typeP = TInt <$ reserved "Int" <|> TBool <$ reserved "Bool"


