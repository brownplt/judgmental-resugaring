module Term (Head: Symbol.Symbol) =
  struct
    
    open Format;;
  
    type var = string;;

    module Head = Symbol.Make(Head);;
    type head = Head.t;;

    type 'v term =
      | Val of head * 'v
      | Var of var
      | Stx of head * 'v term list;;

    let show_term_shallow (t: 'v term): string =
      match t with
      | Val(head, _) -> Printf.sprintf "value %s" (Head.show head)
      | Var(var)     -> Printf.sprintf "variable %s" var
      | Stx(head, _) -> Printf.sprintf "term %s"  (Head.show head);;
      
    let go msg =
      print_endline msg;;  

  end
