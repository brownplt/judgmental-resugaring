open Util;;
open Term;;
open Judgment;;
open Fresh;;


type mapping =
  | Mapping of (int, context) Hashtbl.t * (int, mvar) Hashtbl.t * (int, environment) Hashtbl.t;;

  
(* Basic Helpers [TODO]: make private *)

let new_mapping (): mapping =
  Mapping(Hashtbl.create 0, Hashtbl.create 0, Hashtbl.create 0);;
  
let environment_mapping (m: mapping): (int, environment) Hashtbl.t =
  match m with
  | Mapping(_, _, m) -> m;;

let var_mapping (m: mapping): (int, mvar) Hashtbl.t =
  match m with
  | Mapping(_, m, _) -> m;;

let context_mapping (m: mapping): (int, context) Hashtbl.t =
  match m with
  | Mapping(m, _, _) -> m;;

let lookup_in_mapping (m: (int, 'a) Hashtbl.t) (v: mvar): 'a option =
  let MVar(_, id) = v in
  if Hashtbl.mem m id
  then Some (Hashtbl.find m id)
  else None;;

let lookup_environment (m: mapping) (v: mvar): environment option =
  lookup_in_mapping (environment_mapping m) v;;

let lookup_var (m: mapping) (v: mvar): mvar option =
  lookup_in_mapping (var_mapping m) v;;

let lookup_context (m: mapping) (v: mvar): context option =
  lookup_in_mapping (context_mapping m) v;;

let insert_in_mapping (m: (int, 'a) Hashtbl.t) (v: mvar) (value: 'a) =
  let MVar(name, id) = v in
  if Hashtbl.mem m id
  then internal_error (Printf.sprintf "bind_in_mapping - variable %s_%s already bound" name (string_of_int id))
  else Hashtbl.add m id value;;

let insert_environment (m: mapping) (v: mvar) (env: environment) =
  insert_in_mapping (environment_mapping m) v env;;

let insert_var (m: mapping) (v: mvar) (x: mvar) =
  if v = x
  then ()
  else insert_in_mapping (var_mapping m) v x;;

let insert_context (m: mapping) (v: mvar) (c: context) =
  if CHole(v) = c
  then ()
  else insert_in_mapping (context_mapping m) v c;;


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

let expand_judgment (m: mapping) (j: judgment): judgment =
  match j with
  | Judgment(env, e, t) ->
     Judgment(expand_environment m env, expand_context m e, expand_context m t);;

let rec expand_derivation (m: mapping) (d: derivation): derivation =
  let Derivation(premises, conclusion) = d in
  Derivation(List.map (expand_derivation m) premises, expand_judgment m conclusion);;


(* Matching *)

(* [TODO] Assumption that variables in inference rules are distinct. *)

let rec matches_context (m: mapping) (c1: context) (c2: context): bool =
  match (c1, c2) with
  | (c1, CHole(v)) ->
     (match lookup_context m v with
      | None -> true
      | Some(c2) -> matches_context m c1 c2)
  | (CHole(_), _) -> false
  | (CVal(a), CVal(b)) -> a = b
  | (CStx(a, ca), CStx(b, cb)) ->
     (a = b) && List.for_all2 (matches_context m) ca cb
  | (_, _) -> false;;

let rec matches_environment (m: mapping) (env1: environment) (env2: environment): bool =
  match (env1, env2) with
  | (env1, EnvHole(v)) ->
     (match lookup_environment m v with
      | None -> true
      | Some(env2) -> matches_environment m env1 env2)
  | (EnvHole(_), _) -> false
  | (EnvEmpty(), EnvEmpty()) -> true
  | (EnvCons(_, t1, env1), EnvCons(_, t2, env2)) ->
     matches_context m t1 t2 && matches_environment m env1 env2
  | (_, _) -> false;;

let matches_judgment (m: mapping) (j1: judgment) (j2: judgment): bool =
  match (j1, j2) with
  | (Judgment(env1, e1, t1), Judgment(env2, e2, t2)) ->
     matches_environment m env1 env2
     && matches_context m e1 e2
     && matches_context m t1 t2;;


(* Binding *)

let rec bind_context (m: mapping) (c1: context) (c2: context) =
  match (c1, c2) with
  | (c1, CHole(v)) ->
     (match lookup_context m v with
      | None -> insert_context m v c1
      | Some(c2) -> bind_context m c1 c2)
  | (CVal(_), CVal(_)) -> ()
  | (CStx(_, ca), CStx(_, cb)) -> List.iter2 (bind_context m) ca cb
  | (_, _) -> internal_error "bind_context - contexts do not match";;

let rec bind_environment (m: mapping) (env1: environment) (env2: environment) =
  match (env1, env2) with
  | (env1, EnvHole(v)) ->
     (match lookup_environment m v with
      | None -> insert_environment m v env1
      | Some(env2) -> bind_environment m env1 env2)
  | (EnvEmpty(), EnvEmpty()) -> ()
  | (EnvCons(x1, t1, env1), EnvCons(x2, t2, env2)) ->
     insert_var m x2 x1;
     bind_context m t1 t2;
     bind_environment m env1 env2
  | (_, _) -> internal_error "bind_environment - environments do not match";;

let bind_judgment (m: mapping) (j1: judgment) (j2: judgment) =
  match (j1, j2) with
  | (Judgment(env1, e1, t1), Judgment(env2, e2, t2)) ->
     bind_environment m env1 env2;
     bind_context m e1 e2;
     bind_context m t1 t2;;


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
  | InferenceRule(presmises, conclusion) ->
     if matches_judgment m j conclusion
     then (bind_judgment m j conclusion;
           Some(presmises))
     else None;;

let rec derive_tree (rules: inference_rule list) (m: mapping) (j: judgment): derivation =
  let rec recur (rs: inference_rule list): derivation =
    match rs with
    | [] ->
       error (Printf.sprintf "No derivation found for %s\n" (show_judgment j))
    | (r :: rs) ->
       match derive_premises m j r with
       | None -> recur rs
       | Some(premises) ->
          debug (Printf.sprintf "applying rule %s" (show_inference_rule r));
          Derivation(List.map (derive_tree rules m) premises, j)
  in
  if atomic_judgment j
  then Derivation([], j)
            else recur (List.map freshen_inference_rule rules);;

let infer (rules: inference_rule list) (j: judgment): derivation =
  debug (Printf.sprintf "infer: %s\n" (show_judgment j));
  let m = new_mapping() in
  let d = derive_tree rules m j in
  let ans = expand_derivation m d in
  ans;;

let resugar (inf_rules: inference_rule list) (ds_rules: Desugar.rule list): derivation list =
  debug "resugar:";
  let inf_rules = add_expansion_rules inf_rules ds_rules in
  debug (show_inference_rules inf_rules);
  let resugar_rule rule =
    match rule with
    | Desugar.Rule(lhs, _) -> 
       infer inf_rules (freshen_judgment (generic_judgment lhs))
  in
  let ans = List.map resugar_rule ds_rules in
  ans;;
