open Term;;
open Judgment;;


type mapping =
  | Mapping of (int, context) Hashtbl.t * (int, string) Hashtbl.t * (int, environment) Hashtbl.t;;


(* Basic Helpers [TODO]: make private *)

let environment_mapping (m: mapping): (int, environment) Hashtbl.t =
  match m with
  | Mapping(_, _, m) -> m;;

let var_mapping (m: mapping): (int, string) Hashtbl.t =
  match m with
  | Mapping(_, m, _) -> m;;

let context_mapping (m: mapping): (int, context) Hashtbl.t =
  match m with
  | Mapping(m, _, _) -> m;;

let lookup_in_mapping (v: mvar) (m: (int, 'a) Hashtbl.t): 'a option =
  let MVar(_, id) = v in
  if Hashtbl.mem m id
  then Some (Hashtbl.find m id)
  else None;;

let lookup_environment (m: mapping) (v: mvar): environment option =
  lookup_in_mapping v (environment_mapping m);;

let lookup_var (m: mapping) (v: mvar): var option =
  lookup_in_mapping v (var_mapping m);;

let lookup_context (m: mapping) (v: mvar): context option =
  lookup_in_mapping v (context_mapping m);;


(* Expansion *)

let rec expand_context (m: mapping) (c: context): context =
  match c with
  | CVal(_) -> c
  | CVar(_) -> c
  | CHole(v) ->
     (match lookup_context m v with
      | None -> c
      | Some(c) -> expand_context m c)
  | CStx(head, cs) ->
     CStx(head, List.map (expand_context m) cs);;

let rec expand_environment (m: mapping) (env: environment): environment =
  match env with
  | EnvEmpty() -> env
  | EnvHole(v) ->
     (match lookup_environment m v with
      | None -> env
      | Some(env) -> expand_environment m env)
  | EnvCons(v, t, env) ->
     EnvCons(v, expand_context m t, expand_environment m env);;

(* [TODO] expand_var? *)
