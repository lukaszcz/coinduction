(* Utilities *)

open Names

(* numbers from m up to but not including n *)
val range : int (* m *) -> int (* n *) -> int list

val repl : int -> 'a -> 'a list

val take : int -> 'a list -> 'a list

val drop : int -> 'a list -> 'a list

val string_ends_with : string -> string -> bool

val get_basename : string -> string

val id_app : Id.t -> string -> Id.t

val string_to_id : string -> Id.t

val intern_constr : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> Evd.evar_map * EConstr.t

val exists_global : string -> bool

val get_constr : string -> EConstr.t

val get_inductive : string -> inductive

val get_ind_name : inductive -> string

val get_ind_nparams : inductive -> int

val close : (Name.t * 'a * 'a -> 'a) -> (Name.t * 'a) list -> 'a -> 'a

val drop_lambdas : Evd.evar_map -> int -> EConstr.t -> EConstr.t * int

val take_lambdas : Evd.evar_map -> int -> EConstr.t -> (Name.t * EConstr.t) list

val take_prods : Evd.evar_map -> int -> EConstr.t -> (Name.t * EConstr.t) list

val drop_prods : Evd.evar_map -> int -> EConstr.t -> EConstr.t

val drop_all_lambdas : Evd.evar_map -> EConstr.t -> EConstr.t

val take_all_lambdas : Evd.evar_map -> EConstr.t -> (Name.t * EConstr.t) list

val drop_all_prods : Evd.evar_map -> EConstr.t -> EConstr.t

val take_all_prods : Evd.evar_map -> EConstr.t -> (Name.t * EConstr.t) list

val map_fold_constr : (int -> 'a -> EConstr.t -> 'a * EConstr.t) -> 'a -> Evd.evar_map -> EConstr.t -> 'a * EConstr.t

val map_constr : (int -> EConstr.t -> EConstr.t) -> Evd.evar_map -> EConstr.t -> EConstr.t

val fold_constr : (int -> 'a -> EConstr.t -> 'a) -> 'a -> Evd.evar_map -> EConstr.t -> 'a

val map_fold_constr_ker : (int -> 'a -> Constr.t -> 'a * Constr.t) -> 'a -> Constr.t -> 'a * Constr.t

val map_constr_ker : (int -> Constr.t -> Constr.t) -> Constr.t -> Constr.t

val fold_constr_ker : (int -> 'a -> Constr.t -> 'a) -> 'a -> Constr.t -> 'a

val rel_occurs : Evd.evar_map -> EConstr.t -> int list -> bool

val shift_binders_down : Evd.evar_map -> int -> EConstr.t -> EConstr.t

val shift_binders_up : Evd.evar_map -> int -> EConstr.t -> EConstr.t

val is_coinductive : inductive -> bool

val is_and_like : inductive -> bool

val is_exists_like : inductive -> bool

val get_inductive_typeargs : Evd.evar_map -> inductive -> (Name.t * EConstr.t) list

val process_inductive : Declarations.mutual_inductive_body -> Entries.mutual_inductive_entry

val declare_definition : Id.t -> ?opaque:bool -> Evd.evar_map -> EConstr.t -> unit
