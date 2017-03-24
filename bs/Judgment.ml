open Format;;
open Term;;
  
type var = string;;

type judgment =
  | Judgment of context list * context;;

let show_judgment (j: judgment): string =
  let rec show_premises (cs: context list): string =
    match cs with
    | []        -> ""
    | (c :: cs) -> Printf.sprintf "%s, %s" (show_context c) (show_premises cs) in
  
  match j with
  | Judgment([], conclusion) ->
     Printf.sprintf "judgment %s" (show_context conclusion)
  | Judgment(premises, conclusion) ->
     Printf.sprintf "judgment %s => %s" (show_premises premises) (show_context conclusion);;
