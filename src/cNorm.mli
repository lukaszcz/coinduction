(* Proof normalization *)

(* Proof normalization with beta *)
val norm_beta : Evd.evar_map -> EConstr.t -> EConstr.t
(* Proof normalization with beta-iota-zeta and head-delta *)
val norm : Evd.evar_map -> EConstr.t -> EConstr.t
