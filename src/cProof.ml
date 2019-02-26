(* Proof translation -- implementation *)

open Names
open CUtils
open CPred

let get_canonical_ind_name s = get_ind_name (get_inductive s)

let translate_proof copreds evd ty prf =
  let open Constr in
  let open EConstr in
  let ind_names = List.map (fun (_, cop) -> cop.cop_name) copreds in
  let p = List.length ind_names in
  let g_ind_assoc = List.map (fun cp -> (get_canonical_ind_name (get_green_name (snd cp) (snd cp).cop_name), cp)) copreds
  in
  let is_g_ind ind = List.mem_assoc (get_ind_name ind) g_ind_assoc in
  let fix_g_ind ind args f =
    let s = get_ind_name ind in
    let (_, cop) = List.assoc s g_ind_assoc in
    let a = List.length cop.cop_ex_arg_idxs + 1 in
    let args2 = Array.sub args a (Array.length args - a) in
    if Array.length args2 = 0 then
      f (get_inductive cop.cop_name)
    else
      mkApp (f (get_inductive cop.cop_name), args2)
  in
  let injs =
    List.map
      begin fun name ->
        let typeargs = get_inductive_typeargs evd (get_inductive name) in
        let m = List.length typeargs in
        let args = Array.of_list (List.rev (List.map mkRel (range 1 (m + 1)))) in
        close mkLambda typeargs (mkLambda (Name.Anonymous,
                                           mkApp (get_constr name, args),
                                           mkRel 1))
      end
      ind_names
  in
  let rec hlp m t =
    if m = 2 * p + 1 then
      let b =
        map_constr
          begin fun m t ->
            match kind evd t with
            | Rel i when i > m + 1 && i <= m + 1 + p ->
               (* Rel points at an injection *)
               List.nth injs (i - m - 2)
            | Rel i when i > m + 1 + p && i <= m + 1 + 2 * p ->
               (* Rel points at a red parameter *)
               mkInd (get_inductive (List.nth ind_names (m + 1 + 2 * p - i)))
            | App (c, args) ->
               begin
                 match kind evd c with
                 | Ind (ind, u) when is_g_ind ind ->
                    fix_g_ind ind args mkInd
                 | Construct ((ind, i), u) when is_g_ind ind ->
                    fix_g_ind ind args (fun ind -> mkConstruct (ind, i))
                 | _ ->
                    t
               end
            | _ ->
               t
          end
          evd
          t
      in
      mkCoFix (0, ([| Name.Anonymous |], [| ty |], [| b |]))
    else
      match kind evd t with
      | Lambda (na, _, b) ->
         hlp (m + 1) b
      | _ ->
         failwith "can't translate the proof: bad prefix"
  in
  let prf' = CNorm.norm evd prf
  in
  Feedback.msg_notice (Printer.pr_constr (EConstr.to_constr evd prf'));
  let r = CNorm.norm_beta evd (hlp 0 prf')
  in
  Feedback.msg_notice (Printer.pr_constr (EConstr.to_constr evd r));
  (evd, r)
