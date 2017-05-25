open Util;;
open Term;;
open Judgment;;
open Fresh;;


type mapping =
  | Mapping of (int, context) Hashtbl.t * (int, environment) Hashtbl.t;;


(* Basic Helpers [TODO]: make private *)

let new_mapping (): mapping =
  Mapping(Hashtbl.create 0, Hashtbl.create 0);;
  
let environment_mapping (m: mapping): (int, environment) Hashtbl.t =
  match m with
  | Mapping(_, m) -> m;;

let context_mapping (m: mapping): (int, context) Hashtbl.t =
  match m with
  | Mapping(m, _) -> m;;

let lookup_in_mapping (m: (int, 'a) Hashtbl.t) (v: mvar): 'a option =
  let MVar(_, id) = v in
  if Hashtbl.mem m id
  then Some (Hashtbl.find m id)
  else None;;

let lookup_environment (m: mapping) (v: mvar): environment option =
  lookup_in_mapping (environment_mapping m) v;;

let lookup_var (m: mapping) (v: mvar): context option =
  lookup_in_mapping (context_mapping m) v;;

let lookup_context (m: mapping) (v: mvar): context option =
  lookup_in_mapping (context_mapping m) v;;

let insert_in_mapping (m: (int, 'a) Hashtbl.t) (v: mvar) (value: 'a) =
  let MVar(name, id) = v in
  if Hashtbl.mem m id
  then internal_error (Printf.sprintf "insert_in_mapping - variable %s_%s already bound" name (string_of_int id))
  else Hashtbl.add m id value;;

let insert_environment (m: mapping) (v: mvar) (env: environment) =
  insert_in_mapping (environment_mapping m) v env;;

let insert_var (m: mapping) (v: mvar) (x: mvar) =
  if v = x
  then ()
  else insert_in_mapping (context_mapping m) v (CHole(x));;

let insert_context (m: mapping) (v: mvar) (c: context) =
  if CHole(v) = c
  then ()
  else
    (*    Printf.printf "bind %s=%s\n" (show_mvar v) (show_context c); *)
    insert_in_mapping (context_mapping m) v c;;


(* Expansion *)

let as_hole (c: context): mvar =
  match c with
  | CHole(v) -> v
  | _ -> internal_error (Printf.sprintf "expand_environment - wrong type %s\n" (show_context c));;
  
let rec expand_context (m: mapping) (c: context): context =
  match c with
  | CVal(_) -> c
  | CVar(_) -> c
  | CAtom(_) -> c
  | CHole(v) ->
     (match lookup_context m v with
      | None -> (* Printf.printf "not found: %s\n" (show_mvar v); *) c
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
     EnvCons(expand_context m v, expand_context m t, expand_environment m env);;

let expand_judgment (m: mapping) (j: judgment): judgment =
  match j with
  | Judgment(env, e, t) ->
     Judgment(expand_environment m env, expand_context m e, expand_context m t);;

let rec expand_derivation (m: mapping) (d: derivation): derivation =
  let Derivation(premises, conclusion) = d in
  Derivation(List.map (expand_derivation m) premises, expand_judgment m conclusion);;

  
(* Unification *)

(* [TODO] Assumption that variables in inference rules are distinct. *)
(* [TODO] Check if environment 'variables' are actually compound expressions. *)

let rec unify_context (m: mapping) (c1: context) (c2: context): bool =
  match (c1, c2) with
  | (CHole(v), c2) ->
     (match lookup_context m v with
      | None -> insert_context m v c2; true
      | Some(c1) -> unify_context m c1 c2)
  | (c1, CHole(v)) -> unify_context m (CHole v) c1
  | (CVal(a), CVal(b)) -> a = b
  | (CVar(a), CVar(b)) -> a = b
  | (CAtom(a), CAtom(b)) -> a = b
  | (CStx(a, ca), CStx(b, cb)) ->
     a = b && List.for_all2 (unify_context m) ca cb
  | (_, _) -> false;;

let rec unify_environment (m: mapping) (env1: environment) (env2: environment): bool =
  match (env1, env2) with
  | (EnvHole(v), env2) ->
     (match lookup_environment m v with
      | None -> insert_environment m v env2; true
      | Some(env1) -> unify_environment m env1 env2)
  | (env1, EnvHole(v)) -> unify_environment m (EnvHole v) env1
  | (EnvEmpty(), EnvEmpty()) -> true
  | (EnvCons(x1, t1, env1), EnvCons(x2, t2, env2)) ->
     (unify_context m x1 x2)
     && (unify_context m t1 t2)
     && (unify_environment m env1 env2)
  | (_, _) -> internal_error "unify_environment - environments do not match";;

let unify_judgment (m: mapping) (j1: judgment) (j2: judgment): bool =
  match (j1, j2) with
  | (Judgment(env1, e1, t1), Judgment(env2, e2, t2)) ->
     (unify_environment m env1 env2)
     && (unify_context m e1 e2)
     && (unify_context m t1 t2);;


(* Expansion Inference Rules *)

let rec add_expansion_rules
          (inf_rules: inference_rule list)
          (ds_rules: Desugar.rule list):
          inference_rule list =
  match ds_rules with
  | [] -> inf_rules
  | (Desugar.Rule(lhs, rhs) :: ds_rules) ->
     let new_rule = InferenceRule([generic_judgment(rhs)], generic_judgment(lhs)) in
     add_expansion_rules (new_rule :: inf_rules) ds_rules;;

  
(* Inference *)

(* Assumes that r has been freshened. *)
let derive_premises (m: mapping) (j: judgment) (r: inference_rule): judgment list option =
  match r with
  | InferenceRule(premises, conclusion) ->
     if unify_judgment m j conclusion
     then Some(List.map (expand_judgment m) premises)
     else None;;

let rec derive_tree (m: mapping) (rules: inference_rule list) (j: judgment): derivation =
  let rec recur (rs: inference_rule list): derivation =
    match rs with
    | [] ->
       error (Printf.sprintf "No derivation found for %s\n" (show_judgment j))
    | (r :: rs) ->
       match derive_premises m j r with
       | None -> recur rs
       | Some(premises) ->
          debug (Printf.sprintf "Applying %s" (show_inference_rule r));
          debug (Printf.sprintf "  to get %s" (show_judgments premises));
          expand_derivation m (Derivation(List.map (derive_tree m rules) premises, j))
  in
  if atomic_judgment j
  then Derivation([], j)
  else recur (List.map freshen_inference_rule rules);;

let infer (rules: inference_rule list) (j: judgment): derivation =
  debug (Printf.sprintf "infer: %s\n" (show_judgment j));
  derive_tree (new_mapping()) rules j;;

let resugar (inf_rules: inference_rule list) (ds_rules: Desugar.rule list): derivation list =
  debug "resugar:";
  let inf_rules = add_expansion_rules inf_rules ds_rules in
  debug (show_inference_rules inf_rules);
  let resugar_rule rule =
    match rule with
    | Desugar.Rule(lhs, _) -> 
       infer inf_rules (generic_judgment (opacify_context lhs))
  in
  let ans = List.map resugar_rule ds_rules in
  ans;;
