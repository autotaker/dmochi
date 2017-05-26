{
{-# OPTIONS_GHC -fno-warn-unused-matches  -fno-warn-unused-imports #-}
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
<0>            $eol    ;
<0>            $white+ ;
<0,commentSC>  "(*"    { beginComment } 
<commentSC>    "*)"    { endComment   }
<commentSC>    [.\n]   ;
<0>            let     { lexeme $ \_ -> TokenLet}
<0>            in      { lexeme $ \_ -> TokenIn}
<0>            rec     { lexeme $ \_ -> TokenRec }
<0>            and     { lexeme $ \_ -> TokenAnd }
<0>            type    { lexeme $ \_ -> TokenType}
<0>            fun     { lexeme $ \_ -> TokenFun }
<0>            "->"    { lexeme $ \_ -> TokenArr }
<0>            ";;"    { lexeme $ \_ -> TokenEOL }
<0>            ";"     { lexeme $ \_ -> TokenSemi}
<0>            ","     { lexeme $ \_ -> TokenComma}
<0>            ":"     { lexeme $ \_ -> TokenColon}
<0>            if      { lexeme $ \_ -> TokenIf  }
<0>            then    { lexeme $ \_ -> TokenThen}
<0>            else    { lexeme $ \_ -> TokenElse}
<0>            "||"    { lexeme $ \_ -> TokenOr  }
<0>            "&&"    { lexeme $ \_ -> TokenLAnd}
<0>            \=      { lexeme $ \_ -> TokenEq  }
<0>            "<>"    { lexeme $ \_ -> TokenNEq }
<0>            "<"     { lexeme $ \_ -> TokenLt  }
<0>            ">"     { lexeme $ \_ -> TokenGt  }
<0>            "<="    { lexeme $ \_ -> TokenLe  }
<0>            ">="    { lexeme $ \_ -> TokenGe  }
<0>            "+"     { lexeme $ \_ -> TokenAdd }
<0>            "-"     { lexeme $ \_ -> TokenSub }
<0>            "/"     { lexeme $ \_ -> TokenDiv }
<0>            \(      { lexeme $ \_ -> TokenLPar}
<0>            \)      { lexeme $ \_ -> TokenRPar}
<0>            "*"     { lexeme $ \_ -> TokenMul }
<0>            true    { lexeme $ \_ -> TokenTrue }
<0>            false   { lexeme $ \_ -> TokenTrue }
<0>            assert  { lexeme $ \_ -> TokenAssert }
<0>            @ident  { lexeme $ \s -> if s == "_" then TokenHole else TokenVar s }
<0>            \'@ident{ lexeme $ \s -> TokenTVar s }
<0>            $digit+ { lexeme $ \s -> TokenNum (read $s) }
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
 | TokenAssert
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
 | TokenHole
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
lexeme p (pos,_,_,s) l = do
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
    when (d == 0) $ alexSetStartCode 0 
    alexMonadScan
        
alexInitUserState = AlexUserState undefined undefined 0

scanToken :: Alex Token
scanToken = alexMonadScan

tokenError :: Token -> Alex a
tokenError _ = do
    ust <- alexGetUserState
    let AlexPn _ line col = lexerLastPos ust
    alexError $ "ParseError: unexpected token " ++ show (lexerLastLexeme ust) 
                ++ " at line " ++ (show line) 
                ++ ", column " ++ (show col)

}
-- vim:ft=alex
