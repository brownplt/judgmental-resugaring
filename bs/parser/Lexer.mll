
{
    open Lexing
    open Parser        (* The type token is defined in parser.mli *)

    exception SyntaxError of string

    let next_line lexbuf =
      let pos = lexbuf.lex_curr_p in
      lexbuf.lex_curr_p <-
        { pos with pos_bol = lexbuf.lex_curr_pos;
          pos_lnum = pos.pos_lnum + 1
        };;
}
rule token = parse
  | [' ' '\t' '\r']          { token lexbuf }
  | ['\n']                   { next_line lexbuf; token lexbuf }
  | '('                      { LPAREN }
  | ')'                      { RPAREN }
  | '{'                      { LBRACE }
  | '}'                      { RBRACE }
  | ';'                      { SEMICOLON }
  | "=>"                     { ARROW }
  | "="                      { EQUAL }
  | "|-"                     { TURNSTILE }
  | ":"                      { COLON }
  | "|"                      { PIPE }
  | ","                      { COMMA }
  | eof                      { EOF }

  | "grammar"                { LIT_GRAMMAR }
  | "rule"                   { LIT_RULE }
  | "judgment"               { LIT_JUDGMENT }
  | "empty"                  { LIT_EMPTY }

  | "VALUE"                  { LIT_VALUE }
  | "VARIABLE"               { LIT_VARIABLE }

  | '\'' [^ '\'']* '\'' as lxm  { LITERAL(lxm) }  (* TODO: string escapes *)
  | ['a' - 'z']['a' - 'z' 'A' - 'Z' '_']* as lxm { LID(lxm) }
  | ['A' - 'Z']['a' - 'z' 'A' - 'Z' '_']* as lxm { UID(lxm) }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
