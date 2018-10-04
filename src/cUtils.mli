(* Utilities *)

open Names

val range : int -> int -> int list

val string_ends_with : string -> string -> bool

val id_app : Id.t -> string -> Id.t

val resolve_evars : Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val intern_constr : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> Evd.evar_map * EConstr.t

val to_constr : Globnames.global_reference -> EConstr.t

val get_global : string -> Globnames.global_reference

val get_global_id : Id.t -> Globnames.global_reference

val get_constr : string -> EConstr.t

val get_constr_id : Id.t -> EConstr.t

val get_inductive : string -> inductive

val get_inductive_id : Id.t -> inductive

val close : (Name.t * 'a * 'a -> 'a) -> (Name.t * 'a) list -> 'a -> 'a

val e_new_sort : Evd.evar_map ref -> EConstr.t

val map_fold_constr : (int -> 'a -> EConstr.t -> 'a * EConstr.t) -> 'a -> Evd.evar_map -> EConstr.t -> 'a * EConstr.t

val map_constr : (int -> EConstr.t -> EConstr.t) -> Evd.evar_map -> EConstr.t -> EConstr.t

val is_coinductive : inductive -> bool

val get_inductive_typeargs : Evd.evar_map -> inductive -> (Name.t * EConstr.t) list

val process_inductive : Declarations.mutual_inductive_body -> Entries.mutual_inductive_entry

val declare_definition : Id.t -> ?opaque:bool -> Evd.evar_map -> EConstr.t -> unit
