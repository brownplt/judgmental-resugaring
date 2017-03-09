
let parse_term (buf: Lexing.lexbuf): Term.term =
  Parser.term Lexer.token buf;;

let parse_term_s (s: string): Term.term =
  parse_term (Lexing.from_string s);;
