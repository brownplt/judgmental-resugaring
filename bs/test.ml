open Util;;
open Term;;
open Grammar;;
open TestRunner;;
open Grammar;;
open Parse;;

let gram =
  parse_grammar_s
    "Lit = VALUE;
     Decl = VARIABLE;
     Expr = VARIABLE | (Num Lit) | (Let Binds Expr);
     Binds = (End) | (Bind Decl Expr Binds);"

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
                 Test("Invalid",
                      fun() -> test_validate_fail "Expr" "(Let (Bind x (Num '0') (End))
                                                               (Bind x (Num '0') (End)))")])])]);;
  
run_tests tests;;
