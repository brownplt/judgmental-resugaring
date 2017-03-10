open Term;;
open Parser;;

let parse_term (buf: Lexing.lexbuf): Term.term =
  Parser.term Lexer.token buf;;

let parse_term_s (s: string): Term.term =
  parse_term (Lexing.from_string s);;

let parse_grammar (buf: Lexing.lexbuf): Grammar.grammar =
  Parser.grammar Lexer.token buf;;

let parse_grammar_s (s: string): Grammar.grammar =
  parse_grammar (Lexing.from_string s)
