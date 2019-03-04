(* Proof normalization -- implementation *)

open CUtils

let progress = ref false

let norm_beta = Reductionops.nf_beta (Global.env ())

let norm_betaiotazeta = Reductionops.nf_betaiotazeta (Global.env ())

let norm_head_delta evd t =
  let open Constr in
  let open EConstr in
  let rec hlp t =
    match kind evd t with
    | Lambda (na, ty, b) ->
       mkLambda (na, ty, hlp b)
    | Case (ci, ret, value, branches) ->
       mkCase (ci, ret, value, Array.map hlp branches)
    | App (c, args) ->
       mkApp (hlp c, args)
    | Const _ ->
       let t' = Reductionops.whd_delta (Global.env ()) evd t in
       if t <> t' then
         begin
           progress := true;
           t'
         end
       else
         t
    | _ ->
       t
  in
  hlp t

let rec norm evd t =
  progress := false;
  let t = norm_betaiotazeta evd t in
  (* let t = norm_permut evd t in *)
  let t = norm_head_delta evd t in
  if !progress then
    norm evd t
  else
    t
