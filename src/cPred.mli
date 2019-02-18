(* Coinductive predicates *)

open Names

type copred = {
  name : string; (* original name of the coinductive type *)
  ex_args : bool list; (* which arguments are existential variables? *)
  ind_names : string list; (* original names of coinductive types in the same mutual-coinductive block *)
  ind_types : EConstr.t list; (* original arities *)
}

val get_green_name : copred -> string -> string
val get_red_name : copred -> string -> string

val translate_coinductive : Evd.evar_map -> inductive -> bool list (* ex_args *) -> copred
