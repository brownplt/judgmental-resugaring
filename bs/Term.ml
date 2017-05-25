open Util;;
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
  | CAtom of var
  | CVar of var
  | CStx of string * context list;;

let new_mvar (name: string): mvar =
  MVar(name, 0);;



(* Checking if Atomic *)

let atomic_context (c: context): bool =
  match c with
  | CAtom(_) -> true
  | _ -> false;;

let rec opacify_context (c: context): context =
  match c with
  | CStx(a, ca) -> CStx(a, List.map opacify_context ca)
  | CHole(MVar(x, _)) -> CAtom(x)
  | _ -> c;;


(* Printing *)

let show_mvar (var: mvar): string =
  match var with
  | MVar(name, id) ->
     if debug_var_on
     then Printf.sprintf "%s_%s" name (string_of_int id)
     else name;;

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
  | CAtom(var)     -> Printf.sprintf "$%s" var (* TODO: make parsing and printing inverses *)
  | CStx(head, []) -> Printf.sprintf "(%s)" head
  | CStx(head, ts) -> Printf.sprintf "(%s %s)" head (show_contexts ts)
and show_contexts (ts: context list): string =
  match ts with
  | []    -> ""
  | [t]   -> show_context t
  | t::ts -> Printf.sprintf "%s %s" (show_context t) (show_contexts ts);;
