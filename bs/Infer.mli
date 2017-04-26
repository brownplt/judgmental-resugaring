open Term;;
open Judgment;;

val infer : inference_rule list -> judgment -> derivation;;
val resugar : inference_rule list -> Desugar.rule list -> derivation list;;
