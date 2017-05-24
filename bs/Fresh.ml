open Term;;
open Judgment;;

type fresh = ((string * int), int) Hashtbl.t;;

  
let next_fresh_id = ref 0;;

let fresh_id(): int =
  next_fresh_id := !next_fresh_id + 1;
  !next_fresh_id;;

let f_mvar (f: fresh) (v: mvar): mvar =
  match v with
  | MVar(name, id) ->
     if Hashtbl.mem f (name, id)
     then
       let new_id = Hashtbl.find f (name, id) in
       MVar(name, new_id)
     else 
       let new_id = fresh_id() in
       Hashtbl.add f (name, id) new_id;
       MVar(name, new_id);;

let rec f_context (f: fresh) (c: context): context =
  match c with
  | CVal(_)        -> c
  | CVar(_)        -> c
  | CHole(v)       -> CHole(f_mvar f v)
  | CStx(head, cs) -> CStx(head, List.map (f_context f) cs);;

let rec f_env (f: fresh) (env: environment): environment =
  match env with
  | EnvEmpty()         -> EnvEmpty()
  | EnvHole(v)         -> EnvHole(f_mvar f v)
  | EnvCons(v, t, env) -> EnvCons(f_mvar f v, f_context f t, f_env f env);;

let f_judgment (f: fresh) (j: judgment): judgment =
  match j with
  | Judgment(env, e, t) ->
     Judgment(f_env f env, f_context f e, f_context f t);;

let f_inference_rule (f: fresh) (r: inference_rule): inference_rule =
  match r with
  | InferenceRule(ps, c) ->
     InferenceRule(List.map (f_judgment f) ps, f_judgment f c);;

(* Public *)

let freshen_context (c: context): context =
  f_context (Hashtbl.create 0) c;;

let freshen_judgment (j: judgment): judgment =
  f_judgment (Hashtbl.create 0) j;;

let freshen_inference_rule (r: inference_rule): inference_rule =
  f_inference_rule (Hashtbl.create 0) r;;

let generic_judgment (ctx: context): judgment =
  Judgment(EnvHole(new_mvar("g")), freshen_context ctx, CHole(new_mvar("r")));;
