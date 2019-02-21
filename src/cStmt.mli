(* Statement translation *)

open CPred
open Names

type coarg =
    ATerm of EConstr.t
  | AEx of int (* a variable bound by an existential -- Rel index *)

type stmt =
    SProd of Name.t * EConstr.t (* type *) * stmt (* body *)
  | SPred of int (* copred index 0-based *) * copred * coarg list
  | SAnd (* and-like inductive type *) of inductive * stmt list
  | SEx (* exists-like inductive type *) of
      inductive * Name.t (* variable name *) * stmt (* type *) * stmt (* body *)

val map_fold_stmt : (int -> 'a -> stmt -> 'a * stmt) -> 'a -> stmt -> 'a * stmt

val map_stmt : (int -> stmt -> stmt) -> stmt -> stmt

val fold_stmt : (int -> 'a -> stmt -> 'a) -> 'a -> stmt -> 'a

val stmt_to_constr : (int -> int -> copred -> coarg list -> EConstr.t) -> stmt -> EConstr.t

val get_copreds : stmt -> (int * copred) list

val translate_statement :
  Evd.evar_map -> EConstr.t ->
  Evd.evar_map * stmt *
    EConstr.t (* translated statement (one cohyp) *) *
    EConstr.t (* translated statement (multiple cohyps) *)
