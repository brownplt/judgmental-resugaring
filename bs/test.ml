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
  | ExprNT
  | BindsNT;;

module Nonterminal =
  struct
    type t = nonterminal;;
    let show s =
      match s with
      | ExprNT -> "Expr"
      | BindsNT -> "Binds";;
    let ord s =
      match s with
      | ExprNT -> 0
      | BindsNT -> 1;;
  end

module Grammar = Grammar(StringNT)(Nonterminal);;
open Grammar;;
open Term;;
  
let gram =
  begin
    let g = GrammarMap.create 10 in
    GrammarMap.add
      g
      ExprNT
      [PVar;
       PVal("Num");
       PStx("Let", [BindsNT; ExprNT])];
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
           "Numbers",
           [Test("Number",
                 fun() ->
                 test_validate_succ ExprNT (Val("Num", "0")));
            Test("String",
                 fun() ->
                 test_validate_fail ExprNT (Val("Str", "0")))]);
       Test("Whatever", fun() -> true);
       TestGroup(
           "Repetition",
           [Test("One is one", fun() -> 1 == 1);
            Test("One is two", fun() -> 1 == 2)])]);;

run_tests tests;;
