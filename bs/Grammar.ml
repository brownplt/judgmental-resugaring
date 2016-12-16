module Grammar (Head: Symbol.Symbol) (Nonterminal: Symbol.Symbol) =
struct

open Util;;
open Term;;
module Term = Term(Head);;
open Term;;

module Nonterminal = Symbol.Make(Nonterminal);;
module Head        = Symbol.Make(Head);;
module GrammarMap  = Hashtbl.Make(Nonterminal);;
  
type nonterminal = Nonterminal.t;;
type head = Head.t;;
  
type production =
  | PVal of head
  | PVar
  | PStx of head * nonterminal list;;

type grammar = production list GrammarMap.t;;


let show_production_shallow (p: production): string =
  match p with
  | PVal(head)    -> Printf.sprintf "value of nonterminal %s" (Head.show head)
  | PVar          -> Printf.sprintf "variable"
  | PStx(head, _) -> Printf.sprintf "term of nonterminal %s" (Head.show head);;

let validate (g: grammar) (t: 'v term) (s: nonterminal): (unit, string) result =
  
  let nonterminal_error t s =
    Printf.sprintf "Expected %s but found %s"
                   s
                   (show_term_shallow t) in
  
  let prod_error t p =
    Printf.sprintf
      "Expected %s but found %s"
      (show_production_shallow p)
      (show_term_shallow t) in
  
  let rec validate_nonterminal (t: 'v term) (s: nonterminal): (unit, string) result =
    let ps = GrammarMap.find g s in
    match ps with
    | [p] -> validate_prod t p
    | ps ->
       match or_result (validate_prod t) ps with
       | Err ()  -> Err(nonterminal_error t (Nonterminal.show s))
       | Ok  _   -> Ok ()

  and validate_prod (t: 'v term) (p: production): (unit, string) result =
    match (t, p) with
    | (Val(head_found, _), PVal(head_expected))
         when head_expected == head_found ->
       Ok ()
    | (Var _, PVar) -> Ok ()
    | (Stx(head_found, ts), PStx(head_expected, ss))
         when head_expected == head_found
              && List.length ss == List.length ts ->
       (match and_result2 validate_nonterminal ts ss with
        | Err msg -> Err msg
        | Ok  _   -> Ok ())
    | (_, _) -> Err(prod_error t p) in
  
  validate_nonterminal t s

end
