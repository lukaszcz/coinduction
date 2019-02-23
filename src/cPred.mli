(* Coinductive predicates *)

open Names

type copred = {
  cop_name : string; (* original name of the coinductive type *)
  cop_type : EConstr.t; (* original arity *)
  cop_ex_args : string list; (* which arguments are existential variables? "" if not existential, otherwise the name of the coindutive type *)
  cop_ind_names : string list; (* original names of coinductive types in the same mutual-coinductive block *)
  cop_ind_types : EConstr.t list; (* original arities *)
}

val get_green_name : copred -> string -> string
val get_red_name : copred -> string -> string

val translate_coinductive :
  Evd.evar_map -> inductive -> string list (* ex_args *) -> Evd.evar_map * copred
