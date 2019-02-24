(* Coinductive predicates *)

open Names

type copred = {
  cop_name : string; (* original name of the coinductive type *)
  cop_type : EConstr.t; (* original arity *)
  cop_ex_args : string list; (* which arguments are existential variables? "" if not existential, otherwise the name of the coindutive type *)
  cop_ex_arg_idxs : int list;
  cop_ind_names : string list; (* original names of coinductive types in the same mutual-coinductive block *)
  cop_ind_types : EConstr.t list; (* original arities *)
}

val get_green_name : copred -> string -> string
val get_red_name : copred -> string -> string

val fix_ex_arg_red : int -> Constr.t -> Constr.t
val fix_ex_arg_e_red : Evd.evar_map -> int -> EConstr.t -> EConstr.t
val fix_ex_arg_e_green : Evd.evar_map -> string -> int -> EConstr.t -> EConstr.t

val translate_coinductive :
  Evd.evar_map -> inductive -> string list (* ex_args *) -> int list (* ex_arg_idxs *) ->
  Evd.evar_map * copred
