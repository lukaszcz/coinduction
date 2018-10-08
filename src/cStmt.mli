(* Statement translation *)

open Names

val translate_statement :
  Evd.evar_map -> EConstr.t ->
  string list (* ind types names *) * Evd.evar_map (* new evd *) * EConstr.t (* translated statement *)
