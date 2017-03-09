open Format;;
  
type var = string;;

type term =
  | Val of string
  | Var of var
  | Stx of string * term list;;

let rec show_term (t: term): string =
  match t with
  | Val(v)        -> Printf.sprintf "\"%s\"" v (* TODO: string escapes *)
  | Var(var)      -> var
  | Stx(head, ts) -> Printf.sprintf "(%s %s)" head (show_terms ts)
and show_terms (ts: term list): string =
  match ts with
  | []    -> ""
  | [t]   -> show_term t
  | t::ts -> Printf.sprintf "%s %s" (show_term t) (show_terms ts);;
  
let show_term_shallow (t: term): string =
  match t with
  | Val(v)       -> Printf.sprintf "value %s" v
  | Var(var)     -> Printf.sprintf "variable %s" var
  | Stx(head, _) -> Printf.sprintf "term %s" head;;
  
let go msg =
  print_endline msg;;

let plus(x, y) = x + y;;
