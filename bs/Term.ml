open Format;;

type var = string;;

type mvar =
  | MVar of string * int;;

type term =
  | Val of string
  | Var of var
  | Stx of string * term list;;

type context =
  | CVal of string
  | CHole of mvar
  | CVar of var
  | CStx of string * context list;;

let new_mvar (name: string): mvar =
  MVar(name, 0);;


(* Freshening *)

let next_fresh_id = ref 0;;

let fresh_id(): int =
  next_fresh_id := !next_fresh_id + 1;
  !next_fresh_id;;

let freshen_mvar (v: mvar): mvar =
  match v with
  | MVar(name, id) -> MVar(name, fresh_id());;

let rec freshen_context (c: context): context =
  match c with
  | CVal(_)        -> c
  | CVar(_)        -> c
  | CHole(v)       -> CHole(freshen_mvar(v))
  | CStx(head, cs) -> CStx(head, List.map freshen_context cs);;


(* Printing *)

let show_mvar (var: mvar): string =
  match var with
  | MVar(name, _) -> name;;

let rec show_term (t: term): string =
  match t with
  | Val(v)        -> Printf.sprintf "'%s'" v (* TODO: string escapes *)
  | Var(var)      -> var
  | Stx(head, []) -> Printf.sprintf "(%s)" head
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

let rec show_context (t: context): string =
  match t with
  | CVal(v)        -> Printf.sprintf "\"%s\"" v (* TODO: string escapes *)
  | CVar(var)      -> var
  | CHole(var)     -> show_mvar var
  | CStx(head, []) -> Printf.sprintf "(%s)" head
  | CStx(head, ts) -> Printf.sprintf "(%s %s)" head (show_contexts ts)
and show_contexts (ts: context list): string =
  match ts with
  | []    -> ""
  | [t]   -> show_context t
  | t::ts -> Printf.sprintf "%s %s" (show_context t) (show_contexts ts);;
