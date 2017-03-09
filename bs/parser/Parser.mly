%{
  open Term
%}

%token <string> LITERAL
%token <string> IDENTIFIER
%token LPAREN RPAREN
%token LBRACE RBRACE
%token GRAMMAR
%token EOF

%start term
%type <Term.term> term
%%

term:
  | LITERAL                 {
    let s = $1 in
    Term.Val(String.sub s 1 (String.length(s) - 2))
  }
  | IDENTIFIER              { Term.Var($1) }
  | LPAREN IDENTIFIER terms RPAREN { Term.Stx($2, $3) }
;
terms:
  |                         { [] }
  | term terms              { $1 :: $2 }
;
