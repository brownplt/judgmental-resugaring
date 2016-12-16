type test =
  | Test of string * (unit -> bool)
  | TestGroup of string * test list;;

  
class writer = object(self)
  val mutable ind = 0
                      
  method private indent =
    ind <- ind + 1
                   
  method private dedent =
    ind <- ind - 1

  method write msg =
    for i = 0 to ind - 1 do
      print_string "    "
    done;
    print_endline msg

  method indented: 'a. (unit -> 'a) -> 'a =
    fun f ->
    self#indent;
    let x = f() in
    self#dedent;
    x
end;;
  

class test_runner (w: writer) = object(self)
  val mutable succ = 0
  val mutable fail = 0

  method succ = succ
  method fail = fail

  method private passed (name: string) =
    w#write(Printf.sprintf "Test %s: PASS" name);
    succ <- succ + 1

  method private failed (name: string) =
    w#write(Printf.sprintf "Test %s: FAIL" name);
    fail <- fail + 1

  method private run_test (t: test) =
    match t with
    | Test(name, exec) ->
       if exec()
       then self#passed name
       else self#failed name
    | TestGroup(_, _) ->
       let r = new test_runner w in
       r#run t;
       succ <- succ + r#succ;
       fail <- fail + r#fail

  method run (t: test) =
    match t with
    | Test(_, _) ->
       failwith "test_runner#run: must be called on a test group"
    | TestGroup(name, tests) ->
       w#write(Printf.sprintf "%s:" name);
       w#indented (fun () -> List.iter self#run_test tests);
       w#write(Printf.sprintf "%s (%i/%i)" name succ (succ + fail))
end;;

let run_tests (tests: test) =
  (new test_runner (new writer))#run tests;;
