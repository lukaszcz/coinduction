(* Proof translation -- implementation *)

open Names

val translate_proof :
  Id.t list -> Evd.evar_map -> EConstr.t (* type *) -> EConstr.t (* proof *) ->
  Evd.evar_map * EConstr.t
