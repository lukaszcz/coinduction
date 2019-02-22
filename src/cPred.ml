(* Coinductive predicates -- implementation *)
(* Read first:
   https://coq.inria.fr/distrib/current/refman/language/cic.html#inductive-definitions,
   kernel/entries.ml, kernel/constr.mli *)
(* De Bruijn indices in Rel are 1-based! *)

open CUtils
open Names

module IntMap = Map.Make(struct type t = int let compare : int -> int -> int = compare end)

type copred = {
  cop_name : string; (* original name of the coinductive type *)
  cop_type : EConstr.t; (* original arity *)
  cop_ex_args : bool list; (* which arguments are existential variables? *)
  cop_ind_names : string list; (* original names of coinductive types in the same mutual-coinductive block *)
  cop_ind_types : EConstr.t list; (* original arities *)
}

let get_suffix (ex_args : bool list) =
  if List.exists (fun x -> x) ex_args then
    "__" ^ List.fold_right (fun x acc -> (if x then "1" else "0") ^ acc) ex_args ""
  else
    ""
let get_name name ex_args suf = get_basename (name) ^ suf ^ get_suffix ex_args
let get_green_name (p : copred) name = get_name name p.cop_ex_args "__g"
let get_red_name (p : copred) name = get_name name p.cop_ex_args "__r"

(* TODO: injection axioms as parameters *)

(* n - the original number of parameters *)
(* m - how deep we are into a constructor type (= the number of binders up) *)
(* p - the number of mutual-coinductive types in the block *)
(* a - the number of ex-arg parameters (= the number of 1s in ex_args) *)
(* idx - the index of the main coinductive type *)
let fix_type idx p a n m ex_args (mp : int IntMap.t) ty : int IntMap.t * Constr.t =
  let open Constr in
  if a = 0 then
    (mp, ty)
  else
    map_fold_constr_ker
      begin fun k mp t ->
        match kind t with
        | App (c, args) ->
           begin
             match kind c with
             | Rel i when i = p - idx + n + m + k ->
                (* Rel is pointing at the main coinductive type *)
                let (args2, mp2, _) =
                  List.fold_right2
                    begin fun arg b (lst, mp, l) ->
                      if b then
                        match kind arg with
                        | Rel j when j >= k + 1 && j < k + m + 1 ->
                           (* Rel is pointing at one of the variables
                             bound in the constructor type *)
                           let r = m + k - j in
                           (* r is the absolute 0-based top-down index
                              of the variable (counting from the top
                              of the constructor type) *)
                           if IntMap.mem r mp && IntMap.find r mp <> l then
                             failwith ("unsupported coinductive type: " ^
                                          "inconsistent dependent existential arguments")
                           else
                             (mkRel (a + p + n + m + k - l) :: lst, IntMap.add r l mp, l - 1)
                        | _ ->
                           failwith ("unsupported coinductive type: " ^
                                        "a dependent existential argument is not a variable")
                      else
                        (arg :: lst, mp, l)
                    end
                    (Array.to_list args)
                    ex_args
                    ([], mp, a - 1)
                in
                (mp2, mkApp (mkRel (i + p + a), (Array.of_list args2)))
             | _ ->
                (mp, t)
           end
        | _ ->
           (mp, t)
      end
      mp
      ty

let fix_args idx p a n m ex_args (mp : int IntMap.t) ex_arg_indnames args =
  snd (List.fold_right2
         begin fun (b, indname) x (l, acc) ->
           if b then
             let x' =
               map_constr_ker
                 begin fun k t ->
                   let open Constr in
                   match kind t with
                   | App (y, args) ->
                      begin
                        match kind y with
                        | Construct ((ind, i), u) when get_ind_name ind = indname ->
                           mkApp (mkConstruct (get_inductive (get_name indname [] "__g"), i),
                                  Array.append [| mkRel (k + m + n + p + a - l + 1) |] args)
                        | _ ->
                           t
                      end
                   | Construct ((ind, i), u) when get_ind_name ind = indname ->
                      mkApp (mkConstruct (get_inductive (get_name indname [] "__g"), i),
                             [| mkRel (k + m + n + p + a - l + 1) |])
                   | _ ->
                      t
                 end
                 x
             in
             (l - 1, x' :: acc)
           else
             (l, x :: acc)
         end
         (List.combine ex_args ex_arg_indnames)
         args
         (a, []))

let fix_cons idx p a n ex_args ex_arg_indnames t =
  let open Constr in
  let get_params2 m =
    Array.of_list (List.map mkRel (List.rev (range (n + m + 1) (n + m + p + a + 1))))
  in
  let rec hlp m map t =
    match kind t with
    | Prod (na, ty, c) ->
       let (map, ty') = fix_type idx p a n m ex_args map ty
       in
       let (r, map) = hlp (m + 1) map c
       in
       if IntMap.mem m map then
         (mkProd (na, mkRel (m + n + p + a - IntMap.find m map), r), map)
       else
         (mkProd (na, ty', r), map)
    | Rel i when i >= n + m + 1 ->
       (* this Rel points at one of the coinductive types;
          see kernel/entries.ml *)
       (mkApp (mkRel (i + p + a), get_params2 m), map)
    | App (c, args) ->
       begin
         match kind c with
         | Rel i when i >= n + m + 1 ->
            let args = Array.to_list args in
            if List.length args <> List.length ex_args then
              failwith "unsupported coinductive type"
            else
              (mkApp (mkRel (i + p + a),
                      Array.append (get_params2 m)
                        (Array.of_list (fix_args idx p a n m ex_args map ex_arg_indnames args))),
               map)
         | _ ->
            failwith "unsupported coinductive type"
       end
    | _ ->
       failwith "unsupported coinductive type"
  in
  fst (hlp 0 IntMap.empty t)

(* m - the number of parameters above tp up to but not including ex_arg parameters *)
(* a - the number of ex_arg parameters *)
let fix_ex_args m a evd ex_args tp =
  let open Constr in
  let open EConstr in
  let rec hlp n k lst tp =
    match lst with
    | [] -> tp
    | h :: t ->
       begin
         match kind evd tp with
         | Prod (na, ty, body) ->
            if h then
              mkProd (na, mkRel (n + m + a - k), hlp (n + 1) (k + 1) t body)
            else
              mkProd (na, ty, hlp (n + 1) k t body)
         | _ ->
            failwith "unsupported coinductive type"
       end
  in
  if a > 0 then
    hlp 0 0 ex_args tp
  else
    tp

let get_ex_arg_indnames m a evd ex_args tp =
  let open Constr in
  let open EConstr in
  let rec hlp lst tp =
    match lst with
    | [] -> []
    | h :: t ->
       begin
         match kind evd tp with
         | Prod (na, ty, body) ->
            if h then
              begin
                match kind evd ty with
                | App (x, _) ->
                   begin
                     match kind evd x with
                     | Ind (ind, _) ->
                        get_ind_name ind
                     | _ ->
                        failwith "unsupported coinductive type"
                   end
                | Ind (ind, _) ->
                   get_ind_name ind
                | _ ->
                   failwith "unsupported coinductive type"
              end ::
                hlp t body
            else
              "" :: hlp t body
         | _ ->
            failwith "unsupported coinductive type"
       end
  in
  hlp ex_args tp

let rec drop_prefix evd n tp =
  if n = 0 then
    tp
  else
    let open Constr in
    let open EConstr in
    match kind evd tp with
    | Prod (na, ty, body) ->
       drop_prefix evd (n - 1) body
    | _ ->
       failwith "prefix too short"

let coind_hash = Hashtbl.create 128

let translate_coinductive evd (ind : inductive) (ex_args : bool list) =
  let do_transl () =
    let env = Global.env () in
    let mind_body = fst (Inductive.lookup_mind_specif env ind) in
    let mind = CUtils.process_inductive mind_body in
    let open Entries in
    let p = List.length mind.mind_entry_inds
    (* p - the number of mutual-coinductive types in the block *)
    and n = List.length mind.mind_entry_params
    (* n - the original number of parameters *)
    and a = List.fold_left (fun a x -> if x then a + 1 else a) 0 ex_args
    (* a - the number of ex-arg parameters *)
    in
    let ind_names =
      List.map (fun n -> get_ind_name (fst ind, n))
        (range 0 (List.length mind.mind_entry_inds))
    in
    let ind_types =
      List.map
        begin fun name ->
          Retyping.get_type_of env evd (get_constr name)
        end
        ind_names
    in
    let idx = snd ind in
    let l1 = CUtils.take idx ind_types
    and l2 = CUtils.drop (idx + 1) ind_types
    and tp = List.nth ind_types idx
    in
    let ex_arg_indnames = get_ex_arg_indnames idx a evd ex_args tp
    in
    let tp_red_param = fix_ex_args idx a evd ex_args tp
    in
    let ind_types_red_params = l1 @ [tp_red_param] @ l2
    in
    let tp_red = fix_ex_args p a evd ex_args tp
    in
    let ind_types_red = l1 @ [tp_red] @ l2
    in
    let suf = get_suffix ex_args
    in
    let inds2 =
      List.map2
        begin fun e tp ->
          { e with
            mind_entry_typename = id_app e.mind_entry_typename ("__g" ^ suf);
            mind_entry_arity = (EConstr.to_constr evd (drop_prefix evd n tp_red));
            mind_entry_consnames =
              List.map (fun id -> id_app id ("__g" ^ suf)) e.mind_entry_consnames;
            mind_entry_lc =
              List.map (fix_cons idx p a n ex_args ex_arg_indnames) e.mind_entry_lc;
          }
        end
        mind.mind_entry_inds
        ind_types_red
    in
    let params_red =
      (* pairs (red name, arity) *)
      List.map2 (fun e tp -> (id_app e.mind_entry_typename ("__r" ^ suf), tp))
        mind.mind_entry_inds ind_types_red_params
    in
    let evm = ref evd in
    let ex_arg_params =
      List.map (fun x -> ("AA__" ^ string_of_int x, e_new_sort evm)) (range 0 a)
    in
    let evd = !evm
    in
    let uctx = Evd.universe_context_set evd
    in
    let univs =
      match mind.mind_entry_universes with
      | Monomorphic_ind_entry c ->
         Monomorphic_ind_entry (Univ.ContextSet.union c uctx)
      | Polymorphic_ind_entry c ->
         Polymorphic_ind_entry (Univ.UContext.union c (Univ.ContextSet.to_context uctx))
      | Cumulative_ind_entry c ->
         Cumulative_ind_entry
           (Univ.CumulativityInfo.make
              ((Univ.UContext.union (Univ.CumulativityInfo.univ_context c) (Univ.ContextSet.to_context uctx)),
               Univ.CumulativityInfo.variance c))
    in
    let mind2 =
      { mind with
        mind_entry_inds = inds2;
        mind_entry_universes = univs;
        mind_entry_params =
          mind.mind_entry_params @ (* TODO *)
            (List.rev (List.map (fun (x, y) -> (x, LocalAssumEntry (EConstr.to_constr evd y))) params_red)) @
            (List.rev (List.map (fun (x, y) -> (Id.of_string x, LocalAssumEntry (EConstr.to_constr evd y))) ex_arg_params));
      }
    in
    ignore (Declare.declare_mind mind2);
    print_endline "akuku";
    let pred = { cop_name = get_ind_name ind;
                 cop_type = Retyping.get_type_of env evd (get_constr (get_ind_name ind));
                 cop_ex_args = ex_args;
                 cop_ind_names = ind_names;
                 cop_ind_types = ind_types }
    in
    Hashtbl.add coind_hash (ind, ex_args) pred;
    (evd, pred)
  in
  if Hashtbl.mem coind_hash (ind, ex_args) then
    begin
      if exists_global (get_name (get_ind_name ind) ex_args "__g") then
        (evd, Hashtbl.find coind_hash (ind, ex_args))
      else
        begin
          Hashtbl.remove coind_hash (ind, ex_args);
          do_transl ()
        end
    end
  else
    do_transl ()
