{
{-# OPTIONS_GHC -fno-warn-unsed-matches #-}
module Language.DMoCHi.ML.MLParser(parseProg, parseProgramFromFile)  where

import Language.DMoCHi.ML.Syntax.UnTyped
import Language.DMoCHi.ML.MLLexer
}

%tokentype { Token }
%token
  let    { TokenLet  }
  rec    { TokenRec  }
  in     { TokenIn   }
  VAR    { TokenVar $$ }
  TVAR   { TokenTVar $$}
  NUM    { TokenNum $$ }
  true   { TokenTrue }
  false  { TokenFalse }
  type   { TokenType }
  int    { TokenInt }
  bool   { TokenBool }
  unit   { TokenUnit }
  and    { TokenAnd  }
  fun    { TokenFun  }
  begin  { TokenBegin }
  end    { TokenEnd }
  '->'   { TokenArr  }
  ';'    { TokenSemi }
  ':'    { TokenColon}
  ','    { TokenComma}
  if     { TokenIf   }
  then   { TokenThen }
  else   { TokenElse }
  assert { TokenAssert }
  '||'   { TokenOr   }
  '&&'   { TokenLAnd }
  '='    { TokenEq   }
  '_'    { TokenHole }
  '<>'   { TokenNEq  }
  '<'    { TokenLt   }
  '<='   { TokenLe   }
  '>'    { TokenGt   }
  '>='   { TokenGe   }
  '+'    { TokenAdd  }
  '-'    { TokenSub  }
  '/'    { TokenDiv  }
  '*'    { TokenMul  }
  '('    { TokenLPar }
  ')'    { TokenRPar }
  '['    { TokenLBra }
  ']'    { TokenRBra }
  not    { TokenNot }
  valcegar { TokenValCEGAR }
  ';;'   { TokenEOL  }


%monad { Alex } { (>>=) } { return }
%error { tokenError }
%lexer { lexer }{ TokenEOF }

%name prog Prog

%left ';;'
%right in
%right '->'
%right ';'
%right  then else
%nonassoc ','
%left  '||'
%left  '&&'
%nonassoc '=' '<>' '<' '>' '<=' '>='
%left '+' '-'
%left '/' '*'
%nonassoc NEG
%nonassoc not
%nonassoc APP
%%

Prog : Defs { $1 }

Defs : let LetDef Defs        { $2 : $3 }
     | let LetDef ';;' Defs   { $2 : $4 }
     | type TypDef Defs       { $2 : $3 }
     | type TypDef ';;' Defs  { $2 : $4 }
     | valcegar SpecDef Defs  { $2 : $3  }
     | valcegar SpecDef ';;' Defs  { $2 : $4  }
     | Expr Defs              { DLet unusedVar $1 : $2 }
     | Expr ';;' Defs         { DLet unusedVar $1 : $3 }
     |                        { [] }



LetDef 
 : Arg ':' Type  '=' Expr { DLet $1 (annot $5 $3) }
 | Arg '=' Expr           { DLet $1 $3 }
 | FunDef                 { let (f,e) = $1 in DLet f e }
 | rec RecDef             { DRec $2 }

TypDef : SynLHS '=' Type       { let (s,tvars) = $1 in DSyn (SynonymDef s tvars $3) }

SpecDef : VAR ':' AType    { DSpec $1 $3 }

AType : ABase                  { $1 }
      | AType '->' AType       { AFun $1 $3 }

ABase : '(' AType ')'          { $2 }
      | VAR ':' TPrimNP '[' FormulaList ']'  { ABase $1 $3 $5 }
      | VAR ':' TPrimNP  { ABase $1 $3 [] }

FormulaList : Formula          { [$1] }
            | Formula ';' FormulaList { $1 : $3 }

SynLHS : TVAR VAR              { ($2, [$1])} 
       | '(' TVarTuple ')' VAR { ($4, $2) }
       | VAR                   { ($1, []) }

TVarTuple : TVAR               { [$1] }
          | TVAR ',' TVarTuple { $1 : $3 }

Type  : TPrim          { $1 }
      | Type '*' Type  { TPair $1 $3 }
      | Type '->' Type { TFun [$1] $3 }


TPrim : TPrimNP      { $1 }
      | '(' Type ')' { $2 }

TPrimNP : int                            { TInt  }
        | bool                           { TBool }
        | unit                           { TUnit }
        | TVAR                           { TVar $1 }
        | VAR                            { TSyn [] $1 }
        | TPrimNP VAR                    { TSyn [$1] $2 }
        | '(' Type ')' VAR               { TSyn [$2] $4 }
        | '(' Type ',' TypeTuple ')' VAR { TSyn ($2 : $4) $6 }

TypeTuple : Type               { [$1] }
          | Type ',' TypeTuple { $1 : $3 }

FunDef : Arg Args '=' Expr          { ($1, mkLambda $2 $4) }
       | Arg Args ':' Type '=' Expr { ($1, mkLambda $2 (annot $6 $4)) }

RecDef : FunDef             { [$1] }
       | FunDef and RecDef  { $1 : $3 }

Arg : VAR                   { V $1 Nothing }
    | '_'                   { unusedVar    }
    | '(' VAR ':' Type ')'  { V $2 (Just $4) }
    | '(' '_' ':' Type ')'  { annotVar unusedVar $4 }
    | '(' ')'               { annotVar unusedVar TUnit }
    | '(' '(' ')' ':' unit ')' { annotVar unusedVar TUnit }
    | '(' Arg ')'           { $2 }

Args : Arg Args { $1 : $2 }
     | Arg      { [$1] }

Formula : VAR                            { mkVar (V $1 Nothing) }
        | NUM                            { mkLiteral (CInt $1)  }
        | true                           { mkLiteral (CBool True)  }
        | false                          { mkLiteral (CBool False) }
        | Formula '+' Formula            { mkBinary SAdd $1 $3 }
        | Formula '-' Formula            { mkBinary SSub $1 $3 }
        | Formula '*' Formula            { mkBinary SMul $1 $3 }
        | Formula '/' Formula            { mkBinary SDiv $1 $3 }
        | Formula '&&' Formula            { mkBinary SAnd $1 $3 }
        | Formula '||' Formula            { mkBinary SOr $1 $3 }
        | Formula '<' Formula            { mkBinary SLt $1 $3 }
        | Formula '>' Formula            { mkBinary SGt $1 $3 }
        | Formula '<=' Formula            { mkBinary SLte $1 $3 }
        | Formula '>=' Formula            { mkBinary SGte $1 $3 }
        | Formula '<>' Formula            { mkBinary SNEq $1 $3 }
        | Formula '=' Formula            { mkBinary SEq $1 $3 }
        | '-' Formula %prec NEG          { mkUnary SNeg $2 }
        | not Formula                    { mkUnary SNot $2 }
        | '(' Formula ')'                { $2 }

Expr : let Arg ':' Type '=' Expr in Expr { mkLet $2 (annot $6 $4) $8 }
     | let Arg '=' Expr in Expr          { mkLet $2 $4 $6 }
     | let FunDef in Expr                { let (f,e) = $2 in mkLet f e $4 }
     | let rec RecDef in Expr            { mkLetRec $3 $5 }
     | fun Args '->' Expr                { mkLambda $2 $4 }
     | Expr ';' Expr                     { mkLet unusedVar $1 $3 }
     | if Expr then Expr else Expr       { mkIf $2 $4 $6 }
     | if Expr then Expr                 { mkIf $2 $4 (mkLiteral CUnit) }
     | assert Atom                       { mkAssert $2 }
     | Expr ',' Expr                     { mkPair $1 $3 }
     | Expr '&&' Expr                    { mkBinary SAnd $1 $3 }
     | Expr '||' Expr                    { mkBinary SOr  $1 $3 }
     | Expr '<' Expr                     { mkBinary SLt  $1 $3 }
     | Expr '>' Expr                     { mkBinary SGt  $1 $3 }
     | Expr '=' Expr                     { mkBinary SEq  $1 $3 }
     | Expr '<>' Expr                    { mkBinary SNEq $1 $3 }
     | Expr '<=' Expr                    { mkBinary SLte $1 $3 }
     | Expr '>=' Expr                    { mkBinary SGte $1 $3 }
     | Expr '+' Expr                     { mkBinary SAdd $1 $3 }
     | Expr '-' Expr                     { mkBinary SSub $1 $3 }
     | Expr '*' Expr                     { mkBinary SMul $1 $3 } 
     | Expr '/' Expr                     { mkBinary SDiv $1 $3 }
     | '-' Expr %prec NEG                { mkUnary SNeg $2 }
     | Fact                              { $1 }
  
Fact : Atom AtomList { mkApp $1 $2}
     | Atom          { $1 }

AtomList : Atom           { [$1] }
         | Atom AtomList { $1 : $2 }

Atom : VAR                    { mkVar (V $1 Nothing) }
     | NUM                    { mkLiteral (CInt $1) }
     | true                   { mkLiteral (CBool True) }
     | false                  { mkLiteral (CBool False) }
     | '(' ')'                { mkLiteral CUnit }
     | '(' Expr ')'           { $2 }
     | begin Expr end         { $2 }
     | '(' Expr ':' Type ')'  { annot $2 $4 }

{
data Def = DLet (AnnotVar String (Maybe Type)) Exp
         | DSyn SynonymDef
         | DSpec String AType
         | DRec [(AnnotVar String (Maybe Type), Exp)]


primFuncs :: [(AnnotVar String (Maybe Type), TypeScheme, Exp)]
primFuncs = 
    [ build "read_int" (TFun [TUnit] TInt) readIntDef
    , build "Random.bool" (TFun [TUnit] TBool) randomBoolDef
    , build "Random.int" (TFun [TInt] TInt) randomIntDef
    , build "assume"   (TFun [TBool] TUnit) assumeDef
    , build "fst"      (TFun [TPair ta tb] (TVar "a")) fstDef
    , build "snd"      (TFun [TPair ta tb] (TVar "b")) sndDef
    , build "not"      (TFun [TBool] TBool) notDef
    ]
    where
    ta = TVar "a"
    tb = TVar "b"
    build fname ty def = (V fname Nothing, toTypeScheme ty, def)
    readIntDef = 
        mkLambda [unusedVar] $ 
        mkLet x mkRand $
        mkMark x (mkVar x)
    randomIntDef =
        mkLambda [x] $
        mkLet y mkRand $
        let e_0_lte_y_lt_x = 
                mkBinary SAnd (mkBinary SLte c0 vy)
                              (mkBinary SLt  vy vx) 
            vx = mkVar x
            vy = mkVar y 
            c0 = mkLiteral (CInt 0) in
        mkAssume (mkBinary SOr (mkBinary SEq vx c0) e_0_lte_y_lt_x) $
        mkMark y (mkVar y) 
    randomBoolDef = 
        mkLambda [unusedVar] $
        mkLet x (mkBranch (mkLiteral (CBool True)) 
                          (mkLiteral (CBool False))) $
        mkMark x (mkVar x)
    assumeDef  = mkLambda [x] (mkAssume (mkVar x) (mkLiteral CUnit))
    x = V "x" Nothing
    y = V "y" Nothing
    fstDef = mkLambda [x] (mkUnary SFst (mkVar x))
    sndDef = mkLambda [x] (mkUnary SSnd (mkVar x))
    notDef = mkLambda [x] (mkUnary SNot (mkVar x))

toProg :: [Def] -> Program
toProg defs = foldr f (Program primFuncs [] [] e0) defs
    where
    isDef (DLet _ _) = True
    isDef _ = False
    e0 = case last (filter isDef defs) of
        DLet x e | arity e > 0 -> 
            let xs = [ V ("x_" ++ show i) Nothing | i <- [1..arity e]]
                e_app = mkApp (mkVar x) [ mkVar x_i | x_i <- xs] in
            foldr (\x_i acc -> mkLet x_i mkRand $ mkMark x_i acc) e_app xs
        _ -> mkLiteral CUnit
    f (DLet x e) prog = prog{ mainTerm = mkLet x e (mainTerm prog) }
    f (DSyn syn) prog = prog{ synonyms = syn:synonyms prog }
    f (DSpec x ty) prog = prog{ specs  = (x, ty) : specs prog }
    f (DRec funs) prog = prog{ mainTerm = mkLetRec funs (mainTerm prog) }

mkAssert :: Exp -> Exp
mkAssert e = mkIf e (mkLiteral CUnit) mkFail

parseProg :: String -> Either String Program
parseProg input = toProg <$> runAlex input prog

parseProgramFromFile :: FilePath -> IO (Either String Program)
parseProgramFromFile f = parseProg <$> readFile f

lexer :: (Token -> Alex a) -> Alex a
lexer cont = scanToken >>= cont

-- vim:ft=happy
}
