%{
  open Fpat
  open Util
  open Combinator
  open Formula
  open PredVar
  open HornClause
  open HCCS
  open NumAtom

  (** HCCS parser *)

%}

%token <int> INT
%token <float> FLOAT
%token <string> VAR
%token <Fpat.Idnt.t> PVAR
%token PLUS FPLUS MINUS FMINUS
%token TIMES FTIMES DIV FDIV
%token EQ NOTEQ NOT GT LT GEQ LEQ COMMA
%token AND OR IFF
%token LPAREN RPAREN LBRA RBRA
%token DECLARE QUERY
%token BOT TOP
%token DOT CL EOF

%nonassoc IFF
%left OR
%left AND
%left NOT
%nonassoc EQ NOTEQ GT LT GEQ LEQ
%left PLUS FPLUS MINUS FMINUS
%left TIMES FTIMES DIV FDIV
%left COMMA

%start parser_main
%type <Fpat.HCCS.t> parser_main

%% 
parser_main:
 | hcs EOF { $1 }
 | hc EOF { [$1] }
 | error {
       Printer.print_parser_error_information ();
       raise (Global.Syntax_error "Parse error")
     }

hcs:
 | hc DOT hcs { $1 :: $3 }
 | hc DOT { [$1] }
 | DOT { [] }

hc:
 | head DECLARE body { HornClause.of_formulas (List.concat_map Formula.fvs ($1 :: $3)) $1 $3 }
 | QUERY body { HornClause.of_formulas (List.concat_map Formula.fvs $2) Formula.mk_false $2 }

head:
 | BOT
   { Formula.mk_false }
 | PVAR
   { Pva.make $1 [] |> Pva.to_formula }
 | PVAR LPAREN terms RPAREN
   { Pva.make $1 $3 |> Pva.to_formula }

body:
 | atom COMMA body { $1 :: $3 }
 | atom { [$1] }
 | { [] }

atom:
 | PVAR { Pva.make $1 [] |> Pva.to_formula }
 | PVAR LPAREN terms RPAREN { Pva.make $1 $3 |> Pva.to_formula }
 | term { Formula.of_term $1 }

term:
 | INT { IntTerm.make $1 }
 | VAR { Term.mk_var (Idnt.make $1) }
 | term PLUS term { IntTerm.add $1 $3 }
 | term TIMES term { IntTerm.mul $1 $3 }
 | term MINUS term { IntTerm.sub $1 $3 }
 | term DIV term { IntTerm.div $1 $3 }
 | term EQ term
        { Formula.term_of (Formula.eq (Type.mk_unknown) $1 $3) }
 | term NOTEQ term
        { Formula.term_of (Formula.neq (Type.mk_unknown) $1 $3) }
 | term GT term { Formula.term_of (IntFormula.gt $1 $3) }
 | term LT term { Formula.term_of (IntFormula.lt $1 $3) }
 | term LEQ term { Formula.term_of (IntFormula.leq $1 $3) }
 | term GEQ term { Formula.term_of (IntFormula.geq $1 $3) }
 | NOT term { Formula.term_of (Formula.bnot (Formula.of_term $2)) }
 | term AND term { Formula.term_of (Formula.mk_and (Formula.of_term $1) (Formula.of_term $3)) }
 | term OR  term { Formula.term_of (Formula.mk_or  (Formula.of_term $1) (Formula.of_term $3)) }
 | term IFF term { let a, b = Formula.of_term $1, Formula.of_term $3 in
                   Formula.term_of (Formula.mk_and (Formula.imply a b) (Formula.imply b a)) }
 | BOT { BoolTerm.mk_false }
 | TOP { BoolTerm.mk_true }
 | LPAREN term RPAREN { $2 }

terms:
 | term COMMA terms { ($1, Type.mk_unknown) :: $3 }
 | term { [$1, Type.mk_unknown] }
