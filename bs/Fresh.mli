open Term;;
open Judgment;;

val freshen_judgment: judgment -> judgment;;
val freshen_inference_rule: inference_rule -> inference_rule;;
val generic_judgment: context -> judgment;;
