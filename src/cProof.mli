(* Proof translation -- implementation *)

open Names

val translate_proof :
  string list (* names of ind types  *) -> Evd.evar_map ->
  EConstr.t (* type *) -> EConstr.t (* proof *) ->
  Evd.evar_map * EConstr.t
