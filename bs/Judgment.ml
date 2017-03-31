open Format;;
open Term;;

(* [TODO]: EnvCons where the variable name is a constant *)
type environment =
  | EnvEmpty of unit
  | EnvHole of mvar
  | EnvCons of mvar * context * environment;;

type judgment =
  | Judgment of environment * context * context;;

type inference_rule =
  | InferenceRule of judgment list * judgment;;

type derivation =
  | Derivation of derivation list * judgment;;


(* Freshening *)

let rec freshen_env (env: environment): environment =
  match env with
  | EnvEmpty()         -> EnvEmpty()
  | EnvHole(v)         -> EnvHole(freshen_mvar(v))
  | EnvCons(v, t, env) -> EnvCons(freshen_mvar(v), freshen_context(t), freshen_env(env));;

let freshen_judgment (j: judgment): judgment =
  match j with
  | Judgment(env, e, t) ->
     Judgment(freshen_env(env), freshen_context(e), freshen_context(t));;

let freshen_inference_rule (r: inference_rule): inference_rule =
  match r with
  | InferenceRule(ps, c) ->
     InferenceRule(List.map freshen_judgment ps, freshen_judgment(c));;


(* Checking if Atomic *)

let atomic_judgment (j: judgment): bool =
  let Judgment(_, e, _) = j in
  atomic_context e;;


(* Printing *)

let rec show_environment (env: environment): string =
  match env with
  | EnvEmpty()         -> "empty"
  | EnvHole(v)         -> show_mvar v
  | EnvCons(v, t, env) -> Printf.sprintf "%s: %s, %s"
                          (show_mvar v) (show_context t) (show_environment env);;

let show_judgment (j: judgment): string =
  match j with
  | Judgment(env, e, t) ->
     Printf.sprintf "judgment %s |- %s : %s"
                    (show_environment env)
                    (show_context e)
                    (show_context t);;

let show_inference_rule (r: inference_rule): string =
  let rec show_premises (js: judgment list): string =
    match js with
    | []        -> ""
    | [j]       -> show_judgment j
    | (j :: js) -> Printf.sprintf "%s %s" (show_judgment j) (show_premises js) in

  match r with
  | InferenceRule([], conclusion) ->
     Printf.sprintf "rule %s" (show_judgment conclusion)
  | InferenceRule(premises, conclusion) ->
     Printf.sprintf "rule %s => %s" (show_premises premises) (show_judgment conclusion);;

let show_derivation (d: derivation): string =
  let indent (indentation: int): string =
    String.make (4 * indentation) ' '
  in
  let rec show_tree (d: derivation) (indentation: int): string =
    match d with
    | Derivation([], conclusion) ->
       Printf.sprintf "%s%s"
                      (indent indentation)
                      (show_judgment conclusion)
    | Derivation(premises, conclusion) ->
       Printf.sprintf "%s%s=> %s\n"
                      (show_forest premises (indentation + 1))
                      (indent (indentation + 2))
                      (show_judgment conclusion)
  and show_forest (ds: derivation list) (indentation: int): string =
    match ds with
    | [] -> ""
    | (d :: ds) -> Printf.sprintf "%s\n%s"
                                  (show_tree d indentation)
                                  (show_forest ds indentation)
  in
  show_tree d 0
