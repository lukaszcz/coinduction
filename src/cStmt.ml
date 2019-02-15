(* Statement translation -- implementation *)
(* Read first:
   https://coq.inria.fr/distrib/current/refman/language/cic.html#inductive-definitions,
   kernel/entries.ml, kernel/constr.mli *)

open CUtils
open Names

type copred = {
  name : string; (* original name of the coinductive type *)
  ex_args : bool list; (* which arguments are existential variables? *)
  ind_names : string list; (* original names of coinductive types in the same mutual-coinductive block *)
  ind_arities : Constr.t list; (* original arities *)
}

type coarg =
    ATerm of EConstr.t
  | AEx of int

type stmt =
    SProd of Name.t * EConstr.t (* type *) * stmt (* body *)
  | SPred of copred * coarg list
  | SAnd (* and-like inductive type *) of inductive * stmt list
  | SEx (* exists-like inductive type *) of
      inductive * Name.t (* variable name *) * stmt (* type *) * stmt (* body *)

(* n - the original number of parameters *)
(* p - the number of mutual-coinductive types in the block *)
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
       (* this Rel points to the arity of one of the coinductive types;
          see kernel/entries.ml *)
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

let coind_hash = Hashtbl.create 128

let get_g_name s = get_basename s ^ "__g"

let translate_coinductive evd (ind : inductive) =
  let do_transl () =
    let env = Global.env () in
    let mind_body = fst (Inductive.lookup_mind_specif env ind) in
    let mind = CUtils.process_inductive mind_body in
    let open Entries in
    let p = List.length mind.mind_entry_inds
    (* p - the number of mutual-coinductive types in the block *)
    and n = List.length mind.mind_entry_params
    (* n - original number of parameters *)
    in
    let ind_names =
      List.map (fun n -> get_ind_name (fst ind, n))
        (range 0 (List.length mind.mind_entry_inds))
    in
    let ind_types =
      List.map
        begin fun name ->
          EConstr.to_constr evd
            (Retyping.get_type_of env evd (get_constr name))
        end
        ind_names
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
    let params2 =
      (* pairs (red name, arity) *)
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
    let r =
      (get_ind_name ind, ind_names,
       List.map (fun (x, y) -> (x, EConstr.of_constr y)) params2)
    in
    Hashtbl.add coind_hash ind r;
    r
  in
  if Hashtbl.mem coind_hash ind then
    begin
      if exists_global (get_g_name (get_ind_name ind)) then
        Hashtbl.find coind_hash ind
      else
        begin
          Hashtbl.remove coind_hash ind;
          do_transl ()
        end
    end
  else
    do_transl ()

let translate_statement evd t =
  let open Constr in
  let open EConstr in
  let fix_ctx = List.map (fun (x, y) -> (Name.mk_name x, y))
  in
  let hlp2 ctx ind args =
    if is_coinductive ind then
      let (name, ind_names, params2) = translate_coinductive evd ind in
      let m = List.length ctx
      and p = List.length ind_names
      in
      let args2 =
        Array.append (Array.of_list (List.map mkRel (range (m + p + 2) (m + p + 2 + p)))) args
      in
      let impls =
        List.map2
          begin fun name i ->
            let typeargs = get_inductive_typeargs evd (get_inductive name) in
            let m = List.length typeargs in
            let args1 = Array.of_list (List.rev (List.map mkRel (range 1 (m + 1)))) in
            let args2 = Array.of_list (List.rev (List.map mkRel (range 2 (m + 2)))) in
            (string_to_id (name ^ "__r__inj"),
             close mkProd typeargs (mkProd (Name.Anonymous,
                                            mkApp (get_constr name, args1),
                                            mkApp (mkRel (p - snd ind + i + m + 1), args2))))
          end
          ind_names
          (range 0 p)
      in
      let r =
        close mkProd (fix_ctx params2)
          (close mkProd (fix_ctx impls)
             (mkProd (Name.Anonymous,
                      close mkProd (List.rev ctx) (mkApp (mkRel (p - snd ind + m + p), args)),
                      close mkProd (List.rev ctx) (mkApp (get_constr (get_g_name name), args2)))))
      in
      (ind_names, evd, r)
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
