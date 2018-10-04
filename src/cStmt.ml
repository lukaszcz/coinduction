(* Statement translation -- implementation *)

open CUtils
open Names

(* n - the original number of parameters *)
let fix_cons p n t =
  let open Constr in
  let get_params2 m =
    Array.of_list (List.map mkRel (List.rev (range (n + m) (n + m + p))))
  in
  let rec hlp m t =
    match kind t with
    | Prod (na, ty, c) ->
       mkProd (na, ty, (hlp (m + 1) c))
    | Rel i when i >= n + m ->
       mkApp (mkRel (i + p), get_params2 m)
    | App (c, args) ->
       begin
         match kind c with
         | Rel i when i >= n + m ->
            mkApp (mkRel (i + p), Array.append (get_params2 m) args)
         | _ ->
            failwith "unsupported coinductive type"
       end
    | _ ->
       failwith "unsupported coinductive type"
  in
  hlp 1 t

let translate_coinductive evd (ind : inductive) =
  let env = Global.env () in
  let mind_body = fst (Inductive.lookup_mind_specif env ind) in
  let mind = CUtils.process_inductive mind_body in
  let open Entries in
  let p = List.length mind.mind_entry_inds
  and n = List.length mind.mind_entry_params
  in
  let inds2 =
    List.map
      begin fun e ->
        { e with
          mind_entry_typename = id_app e.mind_entry_typename "__g";
          mind_entry_consnames =
            List.map (fun id -> id_app id "__g") e.mind_entry_consnames;
          mind_entry_lc =
            List.map (fix_cons p n) e.mind_entry_lc;
        }
      end
      mind.mind_entry_inds
  in
  let ind_types =
    List.map
      begin fun e ->
        EConstr.to_constr evd
          (Retyping.get_type_of env evd (get_constr_id e.mind_entry_typename))
      end
      mind.mind_entry_inds
  in
  let params2 =
    List.map2 (fun e tp -> (id_app e.mind_entry_typename "__r", tp))
      mind.mind_entry_inds ind_types
  in
  let mind2 =
    { mind with
      mind_entry_inds = inds2;
      mind_entry_params =
        mind.mind_entry_params @
          (List.rev (List.map (fun (x, y) -> (x, LocalAssumEntry y)) params2));
    }
  in
  ignore (Declare.declare_mind mind2);
  ((List.nth mind.mind_entry_inds (snd ind)).mind_entry_typename,
   List.map (fun e -> e.mind_entry_typename) mind.mind_entry_inds,
   List.map (fun (x, y) -> (x, EConstr.of_constr y)) params2)

let translate_statement evd t =
  let open Constr in
  let open EConstr in
  let fix_ctx = List.map (fun (x, y) -> (Name.mk_name x, y))
  in
  let hlp2 ctx ind args =
    if is_coinductive ind then
      let (id, ind_ids, params2) = translate_coinductive evd ind in
      let m = List.length ctx
      and p = List.length ind_ids
      in
      let args2 =
        Array.append (Array.of_list (List.map mkRel (range (m + p + 2) (m + p + 2 + p)))) args
      in
      let impls =
        List.map2
          begin fun id i ->
            let typeargs = get_inductive_typeargs evd (get_inductive_id id) in
            let m = List.length typeargs in
            let args1 = Array.of_list (List.rev (List.map mkRel (range 1 (m + 1)))) in
            let args2 = Array.of_list (List.rev (List.map mkRel (range 2 (m + 2)))) in
            (id_app id "__r__inj",
             close mkProd typeargs (mkProd (Name.Anonymous,
                                            mkApp (get_constr_id id, args1),
                                            mkApp (mkRel (p - snd ind + i + m + 1), args2))))
          end
          ind_ids
          (range 0 p)
      in
      let r =
        close mkProd (fix_ctx params2)
          (close mkProd (fix_ctx impls)
             (mkProd (Name.Anonymous,
                      close mkProd (List.rev ctx) (mkApp (mkRel (p - snd ind + m + p), args)),
                      close mkProd (List.rev ctx) (mkApp (get_constr_id (id_app id "__g"), args2)))))
      in
      (ind_ids, evd, r)
    else
      failwith "unsupported coinductive statement"
  in
  let rec hlp ctx t =
    match kind evd t with
    | Prod (na, ty, c) ->
       hlp ((na,ty) :: ctx) c
    | Ind (ind, u) ->
       hlp2 ctx ind [| |]
    | App (f, args) ->
       begin
         match kind evd f with
         | Ind (ind, u) ->
            hlp2 ctx ind args
         | _ ->
            failwith "unsupported coinductive statement"
       end
    | _ ->
       failwith "unsupported coinductive statement"
  in
  hlp [] t
