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
%start atom
%type <Fpat.Formula.t> atom
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
 | term EQ term
        { Formula.eq
            (Type.meet (snd $1) (snd $3))
            (fst $1) (fst $3) }
 | term NOTEQ term
        { Formula.neq
            (Type.meet (snd $1) (snd $3))
            (fst $1) (fst $3) }
 | term GT term { IntFormula.gt (fst $1) (fst $3) }
 | term LT term { IntFormula.lt (fst $1) (fst $3) }
 | term LEQ term { IntFormula.leq (fst $1) (fst $3) }
 | term GEQ term { IntFormula.geq (fst $1) (fst $3) }
 | NOT atom { Formula.bnot $2 }
 | atom AND atom { Formula.mk_and $1 $3 }
 | atom OR  atom { Formula.mk_or  $1 $3 }
 | atom IFF atom { Formula.mk_and (Formula.imply $1 $3) (Formula.imply $3 $1) }
 | LPAREN atom RPAREN { $2 }
 | BOT { Formula.mk_false }
 | TOP { Formula.mk_true }

term:
    /*
 | PVAR LPAREN terms RPAREN
        { let ts, tys = List.split $3 in
          let ty = Type.mk_fun_args_ret tys Type.mk_top in
          Term.mk_app
            (Term.mk_const (Const.Con(ty, Idnt.make $1)))
            ts,
          Type.mk_top }
 | PVAR { Term.mk_const (Const.Con(Type.mk_top, Idnt.make $1)),
          Type.mk_top }
        */
 | INT { IntTerm.make $1, Type.mk_int }
 | VAR { Term.mk_var (Idnt.make $1), Type.mk_int }
 | term PLUS term { IntTerm.add (fst $1) (fst $3), Type.mk_int }
 | term TIMES term { IntTerm.mul (fst $1) (fst $3), Type.mk_int }
 | term MINUS term { IntTerm.sub (fst $1) (fst $3), Type.mk_int }
 | term DIV term { IntTerm.div (fst $1) (fst $3), Type.mk_int }
 | LPAREN term RPAREN { $2 }

terms:
 | term COMMA terms { $1 :: $3 }
 | term { [$1] }
