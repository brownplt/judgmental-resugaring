let debug_on = false;;

let () = Printexc.record_backtrace true;;

type ('a, 'b) result =
  | Ok of 'a
  | Err of 'b;;

let or_result (f: 'c -> ('a, 'b) result) (xs: 'c list)
    : ('a, unit) result =
  let rec recur (xs: 'c list) =
    match xs with
    | [] -> Err ()
    | x :: xs ->
       match f x with
       | Ok(a)  -> Ok(a)
       | Err(_) -> recur xs in
  recur xs;;
        
let or_result2 (f: 'c -> 'd -> ('a, 'b) result) (xs: 'c list) (ys: 'd list)
    : ('a, unit) result =
  let rec recur (xs: 'c list) (ys: 'd list) =
    match (xs, ys) with
    | ([], []) -> Err ()
    | (x :: xs, y :: ys) ->
       (match f x y with
        | Ok(a)  -> Ok(a)
        | Err(_) -> recur xs ys)
    | (_, _) -> raise(Invalid_argument "or_result2 received lists of different lengths") in
  recur xs ys;;

let and_result (f: 'c -> ('a, 'b) result) (xs: 'c list)
    : ('a list, 'b) result =
  let rec recur (xs: 'c list) (rs: 'a list): ('a list, 'b) result =
    match xs with
    | [] -> Ok rs
    | x :: xs ->
       match f x with
       | Err(b) -> Err(b)
       | Ok(r)  -> recur xs (r :: rs) in
  recur xs [];;

let and_result2 (f: 'c -> 'd -> ('a, 'b) result) (xs: 'c list) (ys: 'd list)
    : ('a list, 'b) result =
  let rec recur (xs: 'c list) (ys: 'd list) (rs: 'a list): ('a list, 'b) result =
    match (xs, ys) with
    | ([], []) -> Ok rs
    | (x :: xs, y :: ys) ->
       (match f x y with
        | Err(b) -> Err(b)
        | Ok(r)  -> recur xs ys (r :: rs))
    | (_, _) -> raise(Invalid_argument "and_result2 received lists of different lengths") in
  recur xs ys [];;

let debug (s: string): unit =
  if debug_on then print_endline s;;
  
let error (s: string): 'a =
  failwith (Printf.sprintf "Error: %s" s);;

let internal_error (s: string): 'a =
  failwith (Printf.sprintf "Internal error: %s" s);;
