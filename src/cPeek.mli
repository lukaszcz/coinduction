(* Peeking at coinductive values *)

val get_peek_name : string -> string

val get_peek_eq_name : string -> string

val declare_peek : Evd.evar_map -> string (* ind_name *) -> unit
