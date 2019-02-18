(* Coinductive predicates -- implementation *)
(* Read first:
   https://coq.inria.fr/distrib/current/refman/language/cic.html#inductive-definitions,
   kernel/entries.ml, kernel/constr.mli *)
(* De Bruijn indices in Rel are 1-based! *)

open CUtils
open Names

module IntMap = Map.Make(struct type t = int let compare : int -> int -> int = compare end)

type copred = {
  name : string; (* original name of the coinductive type *)
  ex_args : bool list; (* which arguments are existential variables? *)
  ind_names : string list; (* original names of coinductive types in the same mutual-coinductive block *)
  ind_types : EConstr.t list; (* original arities *)
}

let get_suffix (ex_args : bool list) =
  if List.exists (fun x -> x) ex_args then
    "__" ^ List.fold_right (fun x acc -> (if x then "1" else "0") ^ acc) ex_args ""
  else
    ""
let get_name name ex_args suf = get_basename (name) ^ suf ^ get_suffix ex_args
let get_green_name (p : copred) name = get_name name p.ex_args "__g"
let get_red_name (p : copred) name = get_name name p.ex_args "__r"

(* TODO: injection axioms as parameters *)

(* n - the original number of parameters *)
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
             | Rel i when i = (p - idx - 1) + n + m + k ->
                (* Rel is pointing at the main coinductive type *)
                let (args2, mp2, _) =
                  List.fold_right2
                    begin fun arg b (lst, mp, l) ->
                      if b then
                        match kind arg with
                        | Rel j when j >= k + 1 && j < k + m ->
                          let r = m + k - j in
                          if IntMap.mem r mp && IntMap.find r mp <> l then
                            failwith ("unsupported coinductive type: " ^
                                         "inconsistent dependent existential arguments")
                          else
                            (mkRel (a + p + n + m + k - r) :: lst, IntMap.add r l mp, l - 1)
                        | _ ->
                           failwith ("unsupported coinductive type: " ^
                                        "a dependent existential argument is not a variable")
                      else
                        (arg :: lst, mp, l - 1)
                    end
                    (Array.to_list args)
                    ex_args
                    ([], mp, List.length ex_args)
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

let fix_args idx p a n m ex_args (mp : int IntMap.t) args = args (* TODO *)

let fix_cons idx p a n ex_args t =
  let open Constr in
  let get_params2 m =
    Array.of_list (List.map mkRel (List.rev (range (n + m) (n + m + p + a))))
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
    | Rel i when i >= n + m ->
       (* this Rel points at one of the coinductive types;
          see kernel/entries.ml *)
       (mkApp (mkRel (i + p + a), get_params2 m), map)
    | App (c, args) ->
       begin
         match kind c with
         | Rel i when i >= n + m ->
            (mkApp (mkRel (i + p + a), Array.append (get_params2 m) (fix_args idx p a n m ex_args map args)), map)
         | _ ->
            failwith "unsupported coinductive type"
       end
    | _ ->
       failwith "unsupported coinductive type"
  in
  fst (hlp 1 IntMap.empty t)

let fix_ex_args m a evd ex_args tp =
  let open Constr in
  let open EConstr in
  let rec hlp n lst tp =
    match lst with
    | [] -> tp
    | h :: t ->
       begin
         match kind evd tp with
         | Prod (na, ty, body) ->
            if h then
              mkProd (na, mkRel (m + a - n), hlp (n + 1) t body)
            else
              mkProd (na, ty, hlp (n + 1) t body)
         | _ ->
            failwith "unsupported coinductive type"
       end
  in
  if a > 0 then
    hlp 0 ex_args tp
  else
    tp

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
    let tp = fix_ex_args (List.length l1) a evd ex_args tp
    in
    let ind_types = l1 @ [tp] @ l2
    in
    let suf = get_suffix ex_args
    in
    let inds2 =
      List.map
        begin fun e ->
          { e with
            mind_entry_typename = id_app e.mind_entry_typename ("__g" ^ suf);
            mind_entry_consnames =
              List.map (fun id -> id_app id ("__g" ^ suf)) e.mind_entry_consnames;
            mind_entry_lc =
              List.map (fix_cons idx p a n ex_args) e.mind_entry_lc;
          }
        end
        mind.mind_entry_inds
    in
    let params2 =
      (* pairs (red name, arity) *)
      List.map2 (fun e tp -> (id_app e.mind_entry_typename ("__r" ^ suf), tp))
        mind.mind_entry_inds ind_types
    in
    let evm = ref evd in
    let ex_arg_params =
      List.map (fun x -> ("AA__" ^ string_of_int x, e_new_sort evm)) (range 0 a)
    in
    let evd = Evd.minimize_universes !evm
    in
    let mind2 =
      { mind with
        mind_entry_inds = inds2;
        mind_entry_params =
          mind.mind_entry_params @
            (List.rev (List.map (fun (x, y) -> (x, LocalAssumEntry (EConstr.to_constr evd y))) params2)) @
            (List.rev (List.map (fun (x, y) -> (Id.of_string x, LocalAssumEntry (EConstr.to_constr evd y))) ex_arg_params));
      }
    in
    ignore (Declare.declare_mind mind2);
    let pred = { name = get_ind_name ind; ex_args = ex_args; ind_names = ind_names; ind_types = ind_types }
    in
    Hashtbl.add coind_hash (ind, ex_args) pred;
    pred
  in
  if Hashtbl.mem coind_hash (ind, ex_args) then
    begin
      if exists_global (get_name (get_ind_name ind) ex_args "__g") then
        Hashtbl.find coind_hash (ind, ex_args)
      else
        begin
          Hashtbl.remove coind_hash (ind, ex_args);
          do_transl ()
        end
    end
  else
    do_transl ()
