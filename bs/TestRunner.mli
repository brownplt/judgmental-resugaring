type test =
  | Test of string * (unit -> bool)
  | TestGroup of string * test list
                               
val run_tests: test -> unit
