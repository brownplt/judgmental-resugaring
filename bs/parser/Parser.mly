%{
%}

%token <string> LITERAL
%token <string> LID
%token <string> UID
%token LPAREN RPAREN
%token LBRACE RBRACE
%token SEMICOLON
%token LIT_GRAMMAR
%token LIT_VALUE
%token LIT_VARIABLE
%token LIT_RULE
%token ARROW
%token EQUAL
%token PIPE
%token EOF

%start term
%type <Term.term> term
%start grammar
%type <Grammar.grammar> grammar
%start rules
%type <Desugar.rule list> rules
%type <Desugar.rule> rule
%type <Term.context> context
%type <Grammar.grammar> grammar_rules
%type <string * Grammar.production list> grammar_rule
%type <Grammar.production list> grammar_rule_alts
%type <Grammar.production list> grammar_rule_alt_seq
%type <string list> grammar_nts
%type <string> grammar_nt
%%

rules:
  | { [] }
  | rule rules { $1 :: $2 }
;
rule:
  | LIT_RULE context ARROW context {
    Desugar.Rule ($2, $4)
  }
;
grammar:
  | grammar_rules { $1 }
;
grammar_rules:
  | { Hashtbl.create 10 }
  | grammar_rule grammar_rules {
    let (nt, alts) = $1 in
    Hashtbl.add $2 nt alts;
    $2
  }
;
grammar_rule:
  | UID EQUAL grammar_rule_alts SEMICOLON {
    ($1, $3)
  }
;
grammar_rule_alts:
  | { [] }
  | grammar_production grammar_rule_alt_seq { $1 :: $2 }
;
grammar_rule_alt_seq:
  | { [] }
  | PIPE grammar_production grammar_rule_alt_seq { $2 :: $3 }
;
grammar_production:
  | LIT_VALUE    { Grammar.PVal }
  | LIT_VARIABLE { Grammar.PVar }
  | LPAREN UID grammar_nts RPAREN {
    Grammar.PStx($2, $3)
  }
;
grammar_nts:
  | { [] }
  | grammar_nt grammar_nts { $1 :: $2 }
;
grammar_nt:
  | UID { $1 }
;
term:
  | LITERAL {
    let s = $1 in
    Term.Val(String.sub s 1 (String.length(s) - 2))
  }
  | LID {
    Term.Var($1)
  }
  | LPAREN UID terms RPAREN {
    Term.Stx($2, $3)
  }
;
terms:
  |             { [] }
  | term terms  { $1 :: $2 }
;
context:
  | LITERAL {
    let s = $1 in
    Term.CVal(String.sub s 1 (String.length(s) - 2))
  }
  | LID {
    Term.CVar($1)
  }
  | UID {
    Term.CHole($1)
  }
  | LPAREN UID contexts RPAREN {
    Term.CStx($2, $3)
  }
;
contexts:
  |                  { [] }
  | context contexts { $1 :: $2 }
;
