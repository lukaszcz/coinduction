(* Proof translation *)

open CPred
open CStmt

val translate_proof :
  stmt -> (int * copred) list (* copreds  *) -> EConstr.t list (* cohyps *) ->
  Evd.evar_map -> EConstr.t (* type *) -> EConstr.t (* proof *) ->
  Evd.evar_map * EConstr.t
