(* Proof translation -- implementation *)

open Names
open CUtils

let translate_proof ind_ids evd ty prf =
  let open Constr in
  let open EConstr in
  let p = List.length ind_ids in
  let g_ind_names =
    List.map
      begin fun id ->
        let s = Id.to_string id in
        (MutInd.to_string (fst (get_inductive (s ^ "__g"))), s)
      end
      ind_ids
  in
  let is_g_ind ind = List.mem_assoc (MutInd.to_string (fst ind)) g_ind_names in
  let fix_g_ind ind =
    let s = MutInd.to_string (fst ind) in
    get_inductive (List.assoc s g_ind_names)
  in
  let the_True = get_constr "True" in
  let evm = ref evd in
  let mk_lams =
    close mkLambda
      (List.map (fun _ -> (Name.Anonymous, e_new_sort evm)) (range 1 (p + 1)))
  in
  let injs =
    List.map
      begin fun id ->
        let typeargs = get_inductive_typeargs evd (get_inductive_id id) in
        let m = List.length typeargs in
        let args = Array.of_list (List.rev (List.map mkRel (range 1 (m + 1)))) in
        close mkLambda typeargs (mkLambda (Name.Anonymous,
                                           mkApp (get_constr_id id, args),
                                           mkRel 1))
      end
      ind_ids
  in
  let rec hlp m t =
    if m = 2 * p + 1 then
      let b =
        map_constr
          begin fun m t ->
            match kind !evm t with
            | Rel i when i > m + 1 && i <= m + 1 + p ->
               List.nth injs (i - m - 2)
            | Rel i when i > m + 1 + p && i <= m + 1 + 2 * p ->
               the_True
            | Ind (ind, u) ->
               if is_g_ind ind then
                 mk_lams (mkInd (fix_g_ind ind))
               else
                 t
            | Construct ((ind, i), u) ->
               if is_g_ind ind then
                 mk_lams (mkConstruct (fix_g_ind ind, i))
               else
                 t
            | _ ->
               t
          end
          !evm
          t
      in
      mkCoFix (0, ([| Name.Anonymous |], [| ty |], [| b |]))
    else
      match kind !evm t with
      | Lambda (na, _, b) ->
         hlp (m + 1) b
      | _ ->
         failwith "can't translate the proof: bad prefix"
  in
  let norm x = Reductionops.nf_betaiotazeta (Global.env ()) !evm x
  in
  let r = norm (hlp 0 (norm prf))
  in
  (!evm, r)
