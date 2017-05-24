{
module Language.DMoCHi.ML.MLLexer (
  Token(..), Alex, runAlex, scanToken, tokenError
) where
import Control.Monad(when)

}

%wrapper "monadUserState"

$digit = 0-9
$lower = [a-z\_]
$upper = [A-Z]
$symstart = [a-z\_]
$symchar = [a-zA-Z0-9\'\_]
$eol = [\n]

@ident = $symstart $symchar*

tokens :-
  $eol    ;
  $white+ ;
  let     { lexeme $ \s -> TokenLet}
  rec     { lexeme $ \s -> TokenRec }
  and     { lexeme $ \s -> TokenAnd }
  type    { lexeme $ \s -> TokenType}
  fun     { lexeme $ \s -> TokenFun }
  "->"    { lexeme $ \s -> TokenArr }
  ";;"    { lexeme $ \s -> TokenEOL }
  ";"     { lexeme $ \s -> TokenSemi}
  ","     { lexeme $ \s -> TokenComma}
  ":"     { lexeme $ \s -> TokenColon}
  if      { lexeme $ \s -> TokenIf  }
  then    { lexeme $ \s -> TokenThen}
  else    { lexeme $ \s -> TokenElse}
  "||"    { lexeme $ \s -> TokenOr  }
  "&&"    { lexeme $ \s -> TokenLAnd}
  \=      { lexeme $ \s -> TokenEq  }
  "<>"    { lexeme $ \s -> TokenNEq }
  "<"     { lexeme $ \s -> TokenLt  }
  ">"     { lexeme $ \s -> TokenGt  }
  "<="    { lexeme $ \s -> TokenLe  }
  ">="    { lexeme $ \s -> TokenGe  }
  "+"     { lexeme $ \s -> TokenAdd }
  "-"     { lexeme $ \s -> TokenSub }
  "/"     { lexeme $ \s -> TokenDiv }
  \(      { lexeme $ \s -> TokenLPar}
  \)      { lexeme $ \s -> TokenRPar}
  "*"     { lexeme $ \s -> TokenMul }
<0,commentSC>  "(*" { beginComment } 
<commentSC>    "*)" { endComment   }
<commentSC>    [.\n] ;
  true    { lexeme $ \s -> TokenTrue }
  false   { lexeme $ \s -> TokenTrue }
  @ident  { lexeme $ \s -> TokenVar s }
  \'@ident{ lexeme $ \s -> TokenTVar s }
  $digit+ { lexeme $ \s -> TokenNum (read $s) }
{
data Token
 = TokenLet
 | TokenRec
 | TokenIn
 | TokenTrue
 | TokenFalse
 | TokenVar String
 | TokenTVar String
 | TokenNum Integer
 | TokenAnd
 | TokenType
 | TokenInt
 | TokenBool
 | TokenUnit
 | TokenFun
 | TokenArr
 | TokenSemi
 | TokenColon
 | TokenComma
 | TokenLPar
 | TokenRPar
 | TokenIf
 | TokenThen
 | TokenElse
 | TokenOr
 | TokenLAnd
 | TokenEq
 | TokenNEq
 | TokenLt
 | TokenLe
 | TokenGt
 | TokenGe
 | TokenAdd
 | TokenSub
 | TokenDiv
 | TokenMul
 | TokenEOL
 | TokenEOF
 deriving(Show,Eq)

lexeme :: (String -> Token) -> AlexAction Token
lexeme p inp@(pos,_,_,s) l = do
    ust <- alexGetUserState
    alexSetUserState (ust { lexerLastPos = pos 
                          , lexerLastLexeme = (take l s)})
    return (p (take l s))

data AlexUserState
 = AlexUserState {
      lexerLastPos :: AlexPosn
     ,lexerLastLexeme :: String
     ,lexerCommentDepth :: !Int
 }

alexEOF :: Alex Token
alexEOF = return TokenEOF

beginComment :: AlexAction Token
beginComment _ _ = do
    s <- alexGetUserState
    alexSetUserState s{ lexerCommentDepth = lexerCommentDepth s + 1 }
    alexSetStartCode commentSC
    alexMonadScan

endComment :: AlexAction Token
endComment _ _ = do
    s <- alexGetUserState
    let d = lexerCommentDepth s - 1
    alexSetUserState s{ lexerCommentDepth = d }
    when (d == 0) $ alexSetStartCode commentSC
    alexMonadScan
        
alexInitUserState = AlexUserState undefined undefined 0

scanToken :: Alex Token
scanToken = alexMonadScan

tokenError :: Token -> Alex a
tokenError token = do
    ust <- alexGetUserState
    let AlexPn _ line col = lexerLastPos ust
    alexError $ "ParseError: unexpected token " ++ show (lexerLastLexeme ust) 
                ++ " at line " ++ (show line) 
                ++ ", column " ++ (show col)

}
-- vim:ft=alex
