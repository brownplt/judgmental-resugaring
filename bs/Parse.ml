open Lexing;;
open Parsing;;
open Term;;
open Lexer;;
open Parser;;

exception Exit of unit;;

let show_pos lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "  File: %s\n  Line: %d\n  Column: %d\n"
         pos.pos_fname
         pos.pos_lnum
         (pos.pos_cnum - pos.pos_bol + 1);;

type 'a t_parser = (Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a;;

let parse ((p, filename, buf) : 'a t_parser * string * Lexing.lexbuf): 'a =
  let pos = buf.lex_curr_p in
  buf.lex_curr_p <- { pos with pos_fname = filename };
  try p Lexer.token buf with
  | SyntaxError msg ->
     Printf.fprintf stderr "\n%s:\n%s" msg (show_pos buf);
     raise(Exit())
  | Parsing.Parse_error ->
     Printf.fprintf stderr "\nSyntax error:\n%s" (show_pos buf);
     raise(Exit());;

let parse_s ((p, filename, s): 'a t_parser * string * string): 'a =
  parse(p, filename, Lexing.from_string s);;

let parse_term f buf = parse(Parser.term, f, buf);;
let parse_term_s1 f s = parse_s(Parser.term, f, s);;
let parse_grammar f buf = parse(Parser.grammar, f, buf);;
let parse_grammar_s f s = parse_s(Parser.grammar, f, s);;
let parse_ds_rules f buf = parse(Parser.ds_rules, f, buf);;
let parse_ds_rules_s f s = parse_s(Parser.ds_rules, f, s);;
let parse_inference_rules f buf = parse(Parser.inference_rules, f, buf);;
let parse_inference_rules_s f s = parse_s(Parser.inference_rules, f, s);;

(* Bucklescript bug! *)
let parse_term_s a b = a + b;;
