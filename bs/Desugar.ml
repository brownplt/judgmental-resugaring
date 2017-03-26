open Term;;

type rule =
  | Rule of context * context;;

type environment = (string, term) Hashtbl.t;;

let desugar (rs: rule list) (t: term): term =
  
  let rec matches (t: term) (ctx: context): bool =
    match (t, ctx) with
    | (_, CHole(_))                  -> true
    | (Val(a), CVal(b))              -> a == b
    | (Stx(a, terms), CStx(b, ctxs)) ->
       (a == b) && (List.for_all2 matches terms ctxs)
    | (_, _) -> false in
  
  let rec bind (env: environment) (t: term) (ctx: context) =
    match (t, ctx) with
    | (t, CHole(MVar(v, _)))         -> Hashtbl.add env v t
    | (Val(_), CVal(_))              -> ()
    | (Stx(_, terms), CStx(_, ctxs)) -> List.iter2 (bind env) terms ctxs
    | (_, _) -> failwith "Internal error in Desugar/bind" in
  
  (* [TODO]: add check *)
  (* Requires that env contain bindings for all holes in ctx. *)
  let rec substitute (env: environment) (ctx: context): term =
    match ctx with
    | CHole(MVar(v, _)) -> Hashtbl.find env v
    | CVal(l)           -> Val(l)
    | CVar(v)           -> Var(v)
    | CStx(s, ctxs)     -> Stx(s, List.map (substitute env) ctxs) in

  let rec rewrite (rs: rule list) (t: term): term option =
    match rs with
    | []                     -> None
    | (Rule(lhs, rhs) :: rs) ->
       if matches t lhs
       then let env = Hashtbl.create 0 in
            bind env t lhs;
            Some(substitute env rhs)
       else rewrite rs t in

  let rec rewrites (t: term): term =
    match rewrite rs t with
    | Some(t) -> rewrites t
    | None ->
       match t with
       | Stx(s, ts) -> Stx(s, List.map rewrites ts)
       | t          -> t in
  
  rewrites t
