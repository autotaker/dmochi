open Fpat
open Util
open Combinator

let parse_hccs filename =
  let lexbuf =
    filename
    |> open_in  
    |> Lexing.from_channel
  in
  lexbuf.Lexing.lex_curr_p <-
    { Lexing.pos_fname = filename;
      Lexing.pos_lnum = 1;
      Lexing.pos_bol = 0;
      Lexing.pos_cnum = 0 };
  lexbuf |> HCCSParser.parser_main HCCSLexer.token

let parse_sexp filename =
  let lexbuf =
    filename
    |> open_in  
    |> Lexing.from_channel
  in
  lexbuf.Lexing.lex_curr_p <-
    { Lexing.pos_fname = filename;
      Lexing.pos_lnum = 1;
      Lexing.pos_bol = 0;
      Lexing.pos_cnum = 0 };
  lexbuf
  |> SexpParser.parser_main SexpLexer.token
  |> HCCS.of_smtlib1

let infer_constructor hcs =
  let cs = HCCS.kons hcs in
  let ty = Type.mk_adt (Idnt.make "atom") (List.map fst cs) in
  List.map
    (fun (id, i) -> (id, Type.mk_fun_args_ret (List.gen i (fun _ -> Type.new_var ())) ty))
    cs

let () =
    begin
      FPATConfig.set_default ();
      InterpProver.ext_interpolate := InterpProver.interpolate_csisat_dyn;
      Format.printf "@[<v>";
      begin
        try
          Arg.parse
            (Arg.align FPATConfig.arg_spec)
            (fun filename ->
             Global.target_filename := filename;
             SMTProver.open_ ();
             begin
               try
                 begin
                   try
                     parse_hccs filename
                   with Global.Syntax_error(msg) ->
                     try
                       parse_sexp filename
                     with Global.Syntax_error(_) ->
                       failwith msg
                 end
                 |> (fun hcs -> Format.printf "HCCS:@,  %a@," HCCS.pr_verbose hcs; hcs)
                 |> (fun hcs -> infer_constructor hcs, hcs)
                 |> (fun (tenv, hcs) -> SimTypInfer.infer_hccs tenv hcs (* type inference *))
                 |> (fun (env, hcs) ->
                     Unwinding.ctenv0 := env;
                     Format.printf
                       "types:@,  %a@,typed HCCS:@,  %a@,"
                       TypEnv.pr env
                       HCCS.pr_verbose hcs;
                     hcs)
                 |> HCCSSolver.solve_dyn
                 |> PredSubst.normalize
                 |> (fun ans -> Format.printf "solution:@,  %a@," PredSubst.pr ans;ans)
                 |> (fun ans -> 
                        let channel = open_out (filename ^ ".ans") in
                        let f = Format.formatter_of_out_channel channel in
                        Format.fprintf f "solution.@\n%a@\n%!" PredSubst.pr ans)
               with
               | HCCSSolver.NoSolution ->
                  Format.printf "no solution.@,";
                  let channel = open_out (filename ^ ".ans") in
                  let f = Format.formatter_of_out_channel channel in
                  Format.fprintf f "no solution.@\n!";
                  close_out channel
               | HCCSSolver.Unknown ->
                  Format.printf "unknown.@,";
                  let channel = open_out (filename ^ ".ans") in
                  let f = Format.formatter_of_out_channel channel in
                  Format.fprintf f "unknown.@\n!";
                  close_out channel
             end;
             SMTProver.close ())
            FPATConfig.usage
        with
        | Not_found -> Arg.usage (Arg.align FPATConfig.arg_spec) FPATConfig.usage
      end;
      Format.printf "@]@."
    end
