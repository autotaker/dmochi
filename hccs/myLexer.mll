{
  open Fpat
  open MyParser

  (** HCCS lexer *)
}
rule token = parse
| [' ' '\t' '\r'] { token lexbuf }
| '\n' {
      Lexing.new_line lexbuf;
      token lexbuf
    }
| ['0'-'9']+ as lxm { INT(int_of_string lxm) }
| ['0'-'9']+ '.' ['0'-'9']+ as lxm { FLOAT(float_of_string lxm) }
| ":-" { DECLARE }
| "?-" { QUERY }

| '=' { EQ }
| "\\=" { NOTEQ }
| '!' { NOT }
| '>' { GT }
| '<' { LT }
| ">=" { GEQ }
| "<=" { LEQ }
| "<=>" { IFF }
| "/\\" { AND }
| "\\/" { OR }
| '.' { DOT }
| ',' { COMMA }
| "bot" { BOT }
| "top" { TOP }
| "false" { BOT }
| "true" { TOP }

| '+' { PLUS }
| "+." { FPLUS }
| '-' { MINUS }
| "-." { FMINUS }
| '*' { TIMES }
| "*." { FTIMES }
| '/' { DIV }
| "/." { FDIV }

| '(' { LPAREN }
| ')' { RPAREN }
| '[' { LBRA }
| ']' { RBRA }

| ['a'-'z']+ ['A'-'Z' 'a'-'z' '0'-'9' '_' '$']* as str { VAR(str) }
| ("P{" ['A'-'Z' 'a'-'z' '0'-'9' '.' '_']* '}' as ident) (['0'-'9']+ as label) {
    PVAR(Idnt.T(Idnt.make ident, int_of_string label, 0)) }
| ['A'-'Z']+ ['A'-'Z' 'a'-'z' '0'-'9' '_' '$']* as str { PVAR(Idnt.make str) }
| eof { EOF }

| _ {
      Printer.print_lexer_error_information lexbuf;
      raise (Global.Syntax_error "Lexical error")
    }
