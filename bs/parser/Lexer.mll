
{
    open Parser        (* The type token is defined in parser.mli *)
}
rule token = parse
    [' ' '\t' '\n' '\r']     { token lexbuf } (* whitespace *)
  | '\'' [^ '\'']* '\'' as lxm  { LITERAL(lxm) }  (* TODO: string escapes *)
  | ['a' - 'z' 'A' - 'Z' '_']+ as lxm { IDENTIFIER(lxm) }
  | '('                      { LPAREN }
  | ')'                      { RPAREN }
  | '{'                      { LBRACE }
  | '}'                      { RBRACE }
  | "grammar"                { GRAMMAR }
  | eof                      { EOF }
