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


(* Freshening *)

let rec freshen_env(env: environment): environment =
  match env with
  | EnvEmpty()         -> EnvEmpty()
  | EnvHole(v)         -> EnvHole(freshen_mvar(v))
  | EnvCons(v, t, env) -> EnvCons(freshen_mvar(v), freshen_context(t), freshen_env(env));;

let freshen_judgment (j: judgment): judgment =
  match j with
  | Judgment(env, lhs, rhs) ->
     Judgment(freshen_env(env), freshen_context(lhs), freshen_context(rhs));;

let freshen_inference_rule (r: inference_rule): inference_rule =
  match r with
  | InferenceRule(ps, c) ->
     InferenceRule(List.map freshen_judgment ps, freshen_judgment(c));;


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
