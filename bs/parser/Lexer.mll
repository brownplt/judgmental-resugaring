
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
  | "=>"                     { ARROW }
  | "="                      { EQUAL }
  | "|"                      { PIPE }
  | ","                      { COMMA }
  | eof                      { EOF }
  | "grammar"                { LIT_GRAMMAR }
  | "rule"                   { LIT_RULE }
  | "judgment"               { LIT_JUDGMENT }
  | "VALUE"                  { LIT_VALUE }
  | "VARIABLE"               { LIT_VARIABLE }
  | '\'' [^ '\'']* '\'' as lxm  { LITERAL(lxm) }  (* TODO: string escapes *)
  | ['a' - 'z']['a' - 'z' 'A' - 'Z' '_']* as lxm { LID(lxm) }
  | ['A' - 'Z']['a' - 'z' 'A' - 'Z' '_']* as lxm { UID(lxm) }
