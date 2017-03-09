module Grammar =
struct

  open Util;;
  open Term;;
  open Term;;

  type nonterminal = string;;
    
  type production =
    | PVal
    | PVar
    | PStx of string * nonterminal list;;

  type grammar = (string, production list) Hashtbl.t;;


  let show_production_shallow (p: production): string =
    match p with
    | PVal          -> Printf.sprintf "value"
    | PVar          -> Printf.sprintf "variable"
    | PStx(head, _) -> Printf.sprintf "term of nonterminal %s" head;;

  let validate (g: grammar) (t: term) (s: nonterminal): (unit, string) result =
    
    let nonterminal_error t s =
      Printf.sprintf "Expected %s but found %s"
                     s
                     (show_term_shallow t) in
    
    let prod_error t p =
      Printf.sprintf
        "Expected %s but found %s"
        (show_production_shallow p)
        (show_term_shallow t) in
    
    let rec validate_nonterminal (t: term) (s: nonterminal): (unit, string) result =
      let ps = Hashtbl.find g s in
      match ps with
      | [p] -> validate_prod t p
      | ps ->
         match or_result (validate_prod t) ps with
         | Err ()  -> Err(nonterminal_error t s)
         | Ok  _   -> Ok ()

    and validate_prod (t: term) (p: production): (unit, string) result =
      match (t, p) with
      | (Val(_), PVal) -> Ok ()
      | (Var _, PVar)  -> Ok ()
      | (Stx(head_found, ts), PStx(head_expected, ss))
           when head_expected == head_found
                && List.length ss == List.length ts ->
         (match and_result2 validate_nonterminal ts ss with
          | Err msg -> Err msg
          | Ok  _   -> Ok ())
      | (_, _) -> Err(prod_error t p) in
    
    validate_nonterminal t s

end
