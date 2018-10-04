(* Statement translation *)

open Names

val translate_statement : Evd.evar_map -> EConstr.t -> Id.t list * Evd.evar_map * EConstr.t
