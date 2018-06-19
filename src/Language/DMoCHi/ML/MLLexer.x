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
@module = ($upper$symchar*\.)*

tokens :-
<0,specSC>     $eol    ;
<0,specSC>     $white+ ;
<0>            "(*{SPEC}"  { beginSpec }
<specSC>       "{SPEC}*)"  { endSpec   }
<0,commentSC>  "(*"    { beginComment }
<commentSC>    "*)"    { endComment   }
<commentSC>    [.\n]   ;
<0>            let     { lexeme $ \_ -> TokenLet}
<0>            in      { lexeme $ \_ -> TokenIn}
<0>            rec     { lexeme $ \_ -> TokenRec }
<0>            and     { lexeme $ \_ -> TokenAnd }
<0>            type    { lexeme $ \_ -> TokenType}
<0>            fun     { lexeme $ \_ -> TokenFun }
<0>            begin   { lexeme $ \_ -> TokenBegin}
<0>            end     { lexeme $ \_ -> TokenEnd }
<0,specSC>     int     { lexeme $ \_ -> TokenInt }
<0,specSC>     bool    { lexeme $ \_ -> TokenBool }
<0,specSC>     unit    { lexeme $ \_ -> TokenUnit }
<0,specSC>     "->"    { lexeme $ \_ -> TokenArr }
<0,specSC>     ";;"    { lexeme $ \_ -> TokenEOL }
<0,specSC>     ";"     { lexeme $ \_ -> TokenSemi}
<0>            ","     { lexeme $ \_ -> TokenComma}
<0,specSC>     ":"     { lexeme $ \_ -> TokenColon}
<0>            if      { lexeme $ \_ -> TokenIf  }
<0>            then    { lexeme $ \_ -> TokenThen}
<0>            else    { lexeme $ \_ -> TokenElse}
<0,specSC>     "||"    { lexeme $ \_ -> TokenOr  }
<0,specSC>     "&&"    { lexeme $ \_ -> TokenLAnd}
<0,specSC>     \=      { lexeme $ \_ -> TokenEq  }
<0,specSC>     "<>"    { lexeme $ \_ -> TokenNEq }
<0,specSC>     "<"     { lexeme $ \_ -> TokenLt  }
<0,specSC>     ">"     { lexeme $ \_ -> TokenGt  }
<0,specSC>     "<="    { lexeme $ \_ -> TokenLe  }
<0,specSC>     ">="    { lexeme $ \_ -> TokenGe  }
<0,specSC>     "+"     { lexeme $ \_ -> TokenAdd }
<0,specSC>     "-"     { lexeme $ \_ -> TokenSub }
<0,specSC>     "/"     { lexeme $ \_ -> TokenDiv }
<0,specSC>     \(      { lexeme $ \_ -> TokenLPar}
<0,specSC>     \)      { lexeme $ \_ -> TokenRPar}
<specSC>       \[       { lexeme $ \_ -> TokenLBra }
<specSC>       \]       { lexeme $ \_ -> TokenRBra }
<0,specSC>     "*"     { lexeme $ \_ -> TokenMul }
<0,specSC>     true    { lexeme $ \_ -> TokenTrue }
<0,specSC>     false   { lexeme $ \_ -> TokenFalse }
<specSC>       valcegar { lexeme $ \_ -> TokenValCEGAR }
<specSC>       not { lexeme $ \_ -> TokenNot }
<0>            assert  { lexeme $ \_ -> TokenAssert }
<0>            @module@ident  { lexeme $ \s -> if s == "_" then TokenHole else TokenVar s }
<specSC>       @ident  { lexeme $ \s -> TokenVar s }
<0>            \'@ident{ lexeme $ \s -> TokenTVar s }
<0,specSC>     $digit+ { lexeme $ \s -> TokenNum (read s) }
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
 | TokenBegin
 | TokenEnd
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
 | TokenNot
 | TokenEOL
 | TokenEOF
 | TokenValCEGAR
 | TokenLBra
 | TokenRBra
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

beginSpec :: AlexAction Token
beginSpec _ _ = do
    alexSetStartCode specSC
    alexMonadScan

endSpec :: AlexAction Token
endSpec _ _ = do
    alexSetStartCode 0
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
