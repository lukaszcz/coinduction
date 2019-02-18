(* Statement translation -- implementation *)
(* Read first:
   https://coq.inria.fr/distrib/current/refman/language/cic.html#inductive-definitions,
   kernel/entries.ml, kernel/constr.mli *)

open CUtils
open CPred
open Names

type coarg =
    ATerm of EConstr.t
  | AEx of int

type stmt =
    SProd of Name.t * EConstr.t (* type *) * stmt (* body *)
  | SPred of copred * coarg list
  | SAnd (* and-like inductive type *) of inductive * stmt list
  | SEx (* exists-like inductive type *) of
      inductive * Name.t (* variable name *) * stmt (* type *) * stmt (* body *)

let translate_statement evd t =
  let open Constr in
  let open EConstr in
  let fix_ctx = List.map (fun (x, y) -> (Name.mk_name x, y))
  in
  let hlp2 ctx ind args =
    if is_coinductive ind then
      let cop = translate_coinductive evd ind [] in
      let m = List.length ctx
      and p = List.length cop.ind_names
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
            (string_to_id (get_red_name cop name ^ "__inj"),
             close mkProd typeargs (mkProd (Name.Anonymous,
                                            mkApp (get_constr name, args1),
                                            mkApp (mkRel (p - snd ind + i + m + 1), args2))))
          end
          cop.ind_names
          (range 0 p)
      in
      let params2 =
        List.map2
          begin fun x y ->
            (Id.of_string (get_red_name cop x), y)
          end
          cop.ind_names
          cop.ind_types
      in
      let r =
        close mkProd (fix_ctx params2)
          (close mkProd (fix_ctx impls)
             (mkProd (Name.Anonymous,
                      close mkProd (List.rev ctx) (mkApp (mkRel (p - snd ind + m + p), args)),
                      close mkProd (List.rev ctx) (mkApp (get_constr (get_green_name cop cop.name), args2)))))
      in
      (cop.ind_names, evd, r)
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
