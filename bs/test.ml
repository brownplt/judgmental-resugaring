open Util;;
open Term;;
open Grammar;;
open TestRunner;;
open Grammar;;
open Desugar;;
open Parse;;

let gram =
  parse_grammar_s
    "Lit = VALUE;
     Decl = VARIABLE;
     Expr = VARIABLE | (Num Lit) | (Let Binds Expr) | (Lambda Params Expr)
          | (DsLet Binds Expr Params Args);
     Args = (End) | (Arg Expr Args);
     Params = (End) | (Param Decl Params);
     Binds = (End) | (Bind Decl Expr Binds);"

let ds_rules =
  parse_ds_rules_s
    "rule (Let Bs B)
       => (DsLet Bs B (End) (End))
     rule (DsLet (Bind X Defn Bs) Body Params Args)
       => (DsLet Bs Body (Param X Params) (Arg Defn Args))
     rule (DsLet (End) Body Params Args)
       => (Apply (Lambda Params Body) Args)";;

let gram_let =
  parse_grammar_s
    "Lit = VALUE;
     Decl = VARIABLE;
     Expr = VARIABLE
          | (Num Lit)
          | (Let Decl Type Expr Expr)
          | (Lambda Decl Type Expr)
          | (Apply Expr Expr);
     Type = (TNum)
          | (TFun Type Type);";;

let ds_let =
  parse_ds_rules_s
    "rule (Let X A B)
       => (Apply (Lambda X B) A)";;
    
let test_desugar (t: string) (exp: string): bool =
  let t = parse_term_s t in
  let exp = parse_term_s exp in
  desugar ds_rules t = exp

let test_validate_succ (s: nonterminal) (t: string): bool =
  let t = parse_term_s t in
  match validate gram t s with
  | Err _ -> false
  | Ok  _ -> true;;

let test_validate_fail (s: nonterminal) (t: string): bool =
  let t = parse_term_s t in
  match validate gram t s with
  | Err _ -> true
  | Ok  _ -> false;;

let tests =
  TestGroup(
      "All Tests",
      [TestGroup(
           "Validation again a Grammar",
           [TestGroup(
                "Atomic",
                [Test("Valid value",
                      fun() -> test_validate_succ "Expr" "(Num '0')");
                 Test("Valid variable",
                      fun() -> test_validate_succ "Expr" "x");
                 Test("Invalid value",
                      fun() -> test_validate_fail "Expr" "(Str '0')")]);
            TestGroup(
                "Terms",
                [Test("Valid",
                      fun() -> test_validate_succ "Expr" "(Let (Bind x (Num '0') (End)) x)");
                 Test("Invalid1",
                      fun() -> test_validate_fail "Expr" "(Let (Bind (Num '0') (Num '0') (End)) x)");
                 Test("Invalid2",
                      fun() -> test_validate_fail "Expr" "(Let (Bind x (Num '0') (End))
                                                               (Bind x (Num '0') (End)))")])]);
       TestGroup(
           "Desugaring",
           [Test("Valid",
                 fun() -> test_desugar
                            "(Let (Bind x (Num '1') (End)) x)"
                            "(Apply (Lambda (Param x (End)) x) (Arg (Num '1') (End)))")])]);;
  
run_tests tests;;
