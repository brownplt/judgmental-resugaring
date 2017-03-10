
{
    open Parser        (* The type token is defined in parser.mli *)
}
rule token = parse
    [' ' '\t' '\n' '\r']     { token lexbuf } (* whitespace *)
  | '('                      { LPAREN }
  | ')'                      { RPAREN }
  | '{'                      { LBRACE }
  | '}'                      { RBRACE }
  | ';'                      { SEMICOLON }
  | "grammar"                { LIT_GRAMMAR }
  | "VALUE"                  { LIT_VALUE }
  | "VARIABLE"               { LIT_VARIABLE }
  | "="                      { EQUAL }
  | "|"                      { PIPE }
  | eof                      { EOF }
  | '\'' [^ '\'']* '\'' as lxm  { LITERAL(lxm) }  (* TODO: string escapes *)
  | ['a' - 'z']['a' - 'z' 'A' - 'Z' '_']* as lxm { LID(lxm) }
  | ['A' - 'Z']['a' - 'z' 'A' - 'Z' '_']* as lxm { UID(lxm) }
