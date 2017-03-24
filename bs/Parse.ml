open Term;;
open Parser;;

let parse_term (buf: Lexing.lexbuf): Term.term =
  Parser.term Lexer.token buf;;

let parse_term_s (s: string): Term.term =
  parse_term (Lexing.from_string s);;

let parse_grammar (buf: Lexing.lexbuf): Grammar.grammar =
  Parser.grammar Lexer.token buf;;

let parse_grammar_s (s: string): Grammar.grammar =
  parse_grammar (Lexing.from_string s);;

let parse_ds_rules (buf: Lexing.lexbuf): Desugar.rule list =
  Parser.ds_rules Lexer.token buf;;

let parse_ds_rules_s (s: string): Desugar.rule list =
  parse_ds_rules (Lexing.from_string s);;

let parse_judgments (buf: Lexing.lexbuf): Judgment.judgment list =
  Parser.judgments Lexer.token buf;;

let parse_judgments_s (s: string): Judgment.judgment list =
  parse_judgments (Lexing.from_string s);;
