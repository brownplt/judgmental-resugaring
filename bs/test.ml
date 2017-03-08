open Util;;
open Term;;
open Grammar;;
open TestRunner;;

module StringNT =
  struct
    include String;;
    let ord x = 1;;
    let show s = s;;
  end;;

type nonterminal =
  | DeclNT
  | ExprNT
  | BindsNT;;

module Nonterminal =
  struct
    type t = nonterminal;;
    let show s =
      match s with
      | DeclNT -> "Decl"
      | ExprNT -> "Expr"
      | BindsNT -> "Binds";;
    let ord s =
      match s with
      | DeclNT -> 0
      | ExprNT -> 1
      | BindsNT -> 2;;
  end

module Grammar = Grammar(StringNT)(Nonterminal);;
open Grammar;;
open Term;;
  
let gram =
  begin
    let g = GrammarMap.create 10 in
    GrammarMap.add
      g
      DeclNT
      [PVar];
    GrammarMap.add
      g
      ExprNT
      [PVar;
       PVal("Num");
       PStx("Let", [BindsNT; ExprNT])];
    GrammarMap.add
      g
      BindsNT
      [PStx("End", []);
       PStx("Bind", [DeclNT; ExprNT; BindsNT])];
    g
  end;;

let test_validate_succ (s: nonterminal) (t: 'v term): bool =
  match validate gram t s with
  | Err _ -> false
  | Ok  _ -> true;;

let test_validate_fail (s: nonterminal) (t: 'v term): bool =
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
                      fun() -> test_validate_succ ExprNT (Val("Num", "0")));
                 Test("Valid variable",
                      fun() -> test_validate_succ ExprNT (Var("x")));
                 Test("Invalid value",
                      fun() -> test_validate_fail ExprNT (Val("Str", "0")))]);
            TestGroup(
                "Terms",
                [Test("Valid",
                      fun() ->
                      test_validate_succ
                        ExprNT
                        (Stx("Let", [Stx("Bind",
                                         [Var("x"); Val("Num", "0"); Stx("End", [])]);
                                     Var("x")])));
                Test("Invalid1",
                     fun() ->
                     test_validate_fail
                       ExprNT
                       (Stx("Let", [Stx("Bind",
                                        [Val("Num", "0"); Val("Num", "0"); Stx("End", [])]);
                                    Var("x")])));
                Test("Invalid2",
                     fun() ->
                     test_validate_fail
                       ExprNT
                       (Stx("Let", [Stx("Bind",
                                        [Var("x"); Val("Num", "0"); Stx("End", [])]);
                                    Stx("Bind",
                                        [Var("x"); Val("Num", "0"); Stx("End", [])])])))])])]);;

run_tests tests;;
