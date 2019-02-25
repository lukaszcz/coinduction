(* Proof translation *)

open CPred

val translate_proof :
  (int * copred) list (* copreds  *) -> Evd.evar_map ->
  EConstr.t (* type *) -> EConstr.t (* proof *) ->
  Evd.evar_map * EConstr.t
