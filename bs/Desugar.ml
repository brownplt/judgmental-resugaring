open Term;;

type rule =
  | Rule of context * context;;

type environment = (string, term) Hashtbl.t;;

let rewrite (t: term) (rs: rule list): term option =
  
  let rec matches (t: term) (ctx: context): bool =
    match (t, ctx) with
    | (_, CHole(_))                  -> true
    | (Val(a), CVal(b))              -> a == b
    | (Stx(a, terms), CStx(b, ctxs)) ->
       (a == b) && (List.for_all2 matches terms ctxs)
    | (_, _) -> false in
  
  let rec bind (env: environment) (t: term) (ctx: context) =
    match (t, ctx) with
    | (t, CHole(v))                  -> Hashtbl.add env v t
    | (Val(_), CVal(_))              -> ()
    | (Stx(_, terms), CStx(_, ctxs)) -> List.iter2 (bind env) terms ctxs
    | (_, _) -> failwith "Internal error in Desugar/bind" in
  
  (* [TODO]: add check *)
  (* Requires that env contain bindings for all holes in ctx. *)
  let rec substitute (env: environment) (ctx: context): term =
    match ctx with
    | CHole(v)      -> Hashtbl.find env v
    | CVal(l)       -> Val(l)
    | CVar(v)       -> Var(v)
    | CStx(s, ctxs) -> Stx(s, List.map (substitute env) ctxs) in

  let rec recur (rs: rule list): term option =
    match rs with
    | []                     -> None
    | (Rule(lhs, rhs) :: rs) ->
       if matches t lhs
       then let env = Hashtbl.create 0 in
            bind env t lhs;
            Some(substitute env rhs)
       else recur rs in

  recur rs
