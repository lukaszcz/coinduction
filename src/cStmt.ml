(* Statement translation -- implementation *)
(* Read first:
   https://coq.inria.fr/distrib/current/refman/language/cic.html#inductive-definitions,
   kernel/entries.ml, kernel/constr.mli *)

open CUtils
open CPred
open Names

type coarg =
    ATerm of EConstr.t
  | AEx of int (* a variable bound by an existential -- Rel index *)

type stmt =
    SProd of Name.t Context.binder_annot * EConstr.t (* type *) * stmt (* body *)
  | SPred of int (* copred index 0-based *) * copred * coarg list
  | SAnd (* and-like inductive type *) of inductive * stmt list
  | SEx (* exists-like inductive type *) of
      inductive * Name.t Context.binder_annot (* variable name *) * stmt (* type *) * stmt (* body *)

let map_fold_stmt (f : int -> 'a -> stmt -> 'a * stmt) acc stmt =
  let rec hlp n acc stmt =
    match stmt with
    | SProd(na, ty, body) ->
       let (acc2, body2) = hlp (n + 1) acc body in
       f n acc2 (SProd(na, ty, body2))
    | SPred _ ->
       f n acc stmt
    | SAnd (ind, args) ->
       let (acc2, args2) =
         List.fold_right
           begin fun x (acc, args2) ->
             let (acc2, x2) = hlp n acc x in
             (acc2, x2 :: args2)
           end
           args
           (acc, [])
       in
       f n acc2 (SAnd (ind, args2))
    | SEx (ind, na, ty, body) ->
       let (acc, ty2) = hlp n acc ty in
       let (acc, body2) = hlp (n + 1) acc body in
       f n acc (SEx (ind, na, ty2, body2))
  in
  hlp 0 acc stmt

let map_stmt (f : int -> stmt -> stmt) stmt =
  snd (map_fold_stmt (fun n () x -> ((), f n x)) () stmt)

let fold_stmt (f : int -> 'a -> stmt -> 'a) acc stmt =
  fst (map_fold_stmt (fun n acc x -> (f n acc x, x)) acc stmt)

let stmt_to_constr (f : int -> int -> copred -> coarg list -> EConstr.t) =
  let open EConstr in
  let rec hlp n stmt =
    match stmt with
    | SProd(na, ty, body) ->
       mkProd (na, ty, hlp (n + 1) body)
    | SPred(p, cop, coargs) ->
       f n p cop coargs
    | SAnd (ind, args) ->
       mkApp(mkInd ind, Array.of_list (List.map (hlp n) args))
    | SEx (ind, na, ty, body) ->
       let ty2 = hlp n ty in
       let body2 = hlp (n + 1) body in
       mkApp(mkInd ind, [| ty2; mkLambda(na, ty2, body2) |])
  in
  hlp 0

let get_copreds s =
  let rec hlp s acc =
    match s with
    | SProd(na, ty, body) ->
       hlp body acc
    | SPred(p, cop, coargs) ->
       (p, cop) :: acc
    | SAnd (ind, args) ->
       List.fold_left (fun acc x -> hlp x acc) acc args
    | SEx (ind, na, ty, body) ->
       hlp body (hlp ty acc)
  in
  List.rev (hlp s [])

let translate_coargs ectx evd args =
  let open Constr in
  let open EConstr in
  List.map begin fun x ->
    match kind evd x with
    | Rel i when fst (List.nth ectx (i - 1)) <> "" -> AEx i
    | _ -> ATerm x (* TODO: check if existential variables do not occur in `x' *)
  end args

let make_stmt evd t =
  let get_ex_arg_indname evd ty =
    let open Constr in
    let open EConstr in
    match kind evd ty with
    | App (t, args) ->
       begin
         match kind evd t with
         | Ind (ind, _) when is_coinductive ind ->
            get_ind_name ind
         | _ ->
            failwith ("unsupported coinductive statement: " ^
                        "the type of an existential variable should be coinductive")
       end
    | Ind (ind, _) when is_coinductive ind ->
       get_ind_name ind
    | _ ->
       failwith ("unsupported coinductive statement: " ^
                   "the type of an existential variable should be coinductive")
  in
  let open Constr in
  let open EConstr in
  (* p - the number of copreds "to the left" *)
  let rec hlp evd p ectx t =
    match kind evd t with
    | Prod (na, ty, c) ->
       let (evd, a, x) = hlp evd p (("", 0) :: ectx) c in
       (evd, a, SProd (na, ty, x))
    | Ind (ind, u) when is_coinductive ind ->
       let (evd, cop) = translate_coinductive evd ind [] [] in
       (evd, p + 1, SPred (p, cop, []))
    | App (f, args) ->
       begin
         match kind evd f with
         | Ind (ind, u) when is_coinductive ind ->
            let coargs = translate_coargs ectx evd (Array.to_list args) in
            let ex_args =
              List.map (function ATerm _ -> "" | AEx i -> fst (List.nth ectx (i - 1))) coargs
            in
            let ex_arg_idxs =
              List.filter (fun i -> i >= 0)
                (List.map (function ATerm _ -> -1 | AEx i -> snd (List.nth ectx (i - 1))) coargs)
            in
            let (evd, cop) = translate_coinductive evd ind ex_args ex_arg_idxs in
            (evd, p + 1, SPred (p, cop, coargs))
         | Ind (ind, u) when is_and_like ind && Array.length args = get_ind_nparams ind ->
            let (evd, p', rargs') =
              List.fold_left
                begin fun (evd, p, acc) x ->
                  let (evd, a, y) = hlp evd p ectx x in
                  (evd, a, y :: acc)
                end
                (evd, p, [])
                (Array.to_list args)
            in
            (evd, p', SAnd (ind, List.rev rargs'))
         | Ind (ind, u) when is_exists_like ind ->
            begin
              match args with
              | [| ty; pred |] ->
                 begin
                   match kind evd pred with
                   | Lambda(na, _, body) ->
                      begin
                        let (evd, p1, cp) = hlp evd p ectx ty in
                        match cp with
                        | SPred (_, cop, _) ->
                           begin
                             CPeek.declare_peek evd cop.cop_name;
                             let (evd, p2, x) =
                               hlp evd p1 ((get_ex_arg_indname evd ty, p) :: ectx) body
                             in
                             (evd, p2, SEx (ind, na, cp, x))
                           end
                        | _ ->
                           failwith "unsupported coinductive statement (1)"
                      end
                   | _ ->
                      failwith "unsupported coinductive statement (2)"
                 end
              | _ ->
                 failwith "unsupported coinductive statement (3)"
            end
         | _ ->
            failwith "unsupported coinductive statement (4)"
       end
    | _ ->
       failwith "unsupported coinductive statement (5)"
  in
  let (evd, _, s) = hlp evd 0 [] t
  in
  (evd, s)

(* m - the total number of coinductive predicates (= the number of red parameters) *)
(* n - the number of non-ex binders up *)
(* p - the index of the current cop (0-indexed) *)
let make_ch_red_cop m n p cop coargs =
  let open EConstr in
  let args =
    List.map
      begin function
      | ATerm t -> t
      | AEx i -> failwith "AEx"
      end
      coargs
  in
  mkApp (mkRel (n + m + m + m), Array.of_list args)

let fix_rels evd n =
  let open Constr in
  let open EConstr in
  map_constr
    begin fun k t ->
      match kind evd t with
      | Rel i when i >= k + n + 1 -> mkRel (i - 1)
      | _ -> t
    end
    evd

(* m - the total number of coinductive predicates (= the number of red parameters) *)
(* n - the number of non-ex binders up *)
let fix_stmt_rels evd m n p s =
  let open EConstr in
  map_stmt
    begin fun k x ->
      match x with
      | SProd (na, ty, body) -> SProd (na, fix_rels evd k ty, body)
      | SPred (idx, cop, coargs) ->
         SPred (idx, cop,
                List.map
                  begin function
                  | ATerm t -> ATerm (fix_rels evd k t)
                  | AEx i when i = k + 1 ->
                     let args =
                       List.rev (List.map mkRel (range (k + 1) (k + n + 1)))
                     in
                     ATerm (mkApp (mkRel (k + n + idx - p), Array.of_list args))
                  | x -> x
                  end
                  coargs)
      | _ -> x
    end
    s

(* m - the total number of coinductive predicates (= the number of red parameters) *)
let make_coind_hyps evd m s =
  let open EConstr in
  (* n - the number of non-ex binders up *)
  let rec hlp n s =
    match s with
    | SProd (na, ty, body) ->
       List.map (fun x -> mkProd (na, ty, x)) (hlp (n + 1) body)
    | SPred (p, cop, coargs) ->
       [make_ch_red_cop m n p cop coargs]
    | SAnd (ind, args) ->
       List.concat (List.map (hlp n) args)
    | SEx (ind, na, ty, body) ->
       begin
         match ty with
         | SPred (p, _, _) -> hlp n ty @ hlp n (fix_stmt_rels evd m n p body)
         | _ -> failwith "SEx"
       end
  in
  hlp 0 s

let make_red k =
  stmt_to_constr begin fun n p cop coargs ->
    let open EConstr in
    let args =
      List.map
        begin function
        | ATerm t -> t
        | AEx i -> mkRel i
        end
        coargs
    in
    mkApp (mkRel (n + k - p), Array.of_list args)
  end

let make_green_cop k p cop args =
  let open EConstr in
  let args =
    List.map (fun idx -> mkRel (k - idx)) cop.cop_ex_arg_idxs @
    [ mkRel (k - p) ] @
    args
  in
  mkApp (get_constr (get_green_name cop cop.cop_name), Array.of_list args)

let make_green k =
  stmt_to_constr begin fun n p cop coargs ->
    let open EConstr in
    make_green_cop (n + k) p cop
      (List.map
         begin function
           | ATerm t -> t
           | AEx i -> mkRel i
         end
         coargs)
  end

let get_red_type evd p cop =
  let open Constr in
  let open EConstr in
  let rec hlp k lst idxs t =
    match lst with
    | head :: tail ->
       begin
         match kind evd t with
         | Prod (na, ty, body) ->
            if head <> "" then
              begin
                mkProd (na, fix_ex_arg_e_red evd (k + p - List.hd idxs) ty,
                        hlp (k + 1) tail (List.tl idxs) body)
              end
            else
              mkProd (na, ty, hlp (k + 1) tail idxs body)
         | _ ->
            failwith "unsupported coinductive type"
       end
    | [] ->
       t
  in
  hlp 0 cop.cop_ex_args cop.cop_ex_arg_idxs cop.cop_type

let fix_ex_arg_inj_args evd p cop m k typeargs args2 =
  let rec hlp n lst ex_args tyargs idxs =
    match lst, ex_args, tyargs with
    | h :: t1, arg :: t2, ty :: t3 ->
       if arg <> "" then
         let i = k + 1 + p - List.hd idxs
         in
         let open Constr in
         let open EConstr in
         let h2 =
           match kind evd ty with
           | Ind (_) ->
              mkApp (mkRel i, [| h |])
           | App (_, args) ->
              let args' =
                Array.map
                  begin fun x ->
                    map_constr
                      begin fun l y ->
                        match kind evd y with
                        | Rel j when j > l ->
                           mkRel (j + k - n + 1)
                        | _ ->
                           y
                      end
                      evd
                      x
                  end
                  args
              in
              mkApp (mkRel i, Array.append args' [| h |])
           | _ ->
              failwith "unsupported coinductive type (2)"
         in
         h2 :: hlp (n + 1) t1 t2 t3 (List.tl idxs)
       else
         h :: hlp (n + 1) t1 t2 t3 idxs
    | _ ->
       lst
  in
  hlp 0 args2 cop.cop_ex_args (List.map snd typeargs) cop.cop_ex_arg_idxs

let fix_injg_typeargs evd k copreds cop typeargs =
  let rec hlp n ex_args tyargs idxs =
    match ex_args, tyargs with
    | arg :: t1, ty :: t2 ->
       if arg <> "" then
         let p2 = List.hd idxs in
         let cop2 = List.nth copreds p2 in
         let open Constr in
         let open EConstr in
         let ty2 =
           match kind evd ty with
           | Ind (_) ->
              make_green_cop (k + n) p2 cop2 []
           | App (_, args) ->
              make_green_cop (k + n) p2 cop2 (Array.to_list args)
           | _ ->
              failwith "unsupported coinductive type (2)"
         in
         ty2 :: hlp (n + 1) t1 t2 (List.tl idxs)
       else
         ty :: hlp (n + 1) t1 t2 idxs
    | _ ->
       []
  in
  List.combine
    (List.map fst typeargs)
    (hlp 0 cop.cop_ex_args (List.map snd typeargs) cop.cop_ex_arg_idxs)

let translate_statement evd t =
  let open EConstr in
  let fix_ctx = List.map (fun (x, y) -> (Context.make_annot (Name.mk_name (string_to_id x)) Sorts.Relevant, y))
  in
  let (evd, stmt) = make_stmt evd t in
  let copreds = get_copreds stmt in
  let m = List.length copreds in
  let red_copred_decls =
    List.map
      begin fun (p, cop) ->
        (get_red_name cop cop.cop_name, get_red_type evd p cop)
      end
      copreds
  in
  let injections =
    List.map
      begin fun (p, cop) ->
        let typeargs = get_inductive_typeargs evd (get_inductive cop.cop_name) in
        let k = List.length typeargs in
        let args1 = Array.of_list (List.rev (List.map mkRel (range 1 (k + 1)))) in
        let args2_l = List.rev (List.map mkRel (range 2 (k + 2))) in
        let args2 = Array.of_list (fix_ex_arg_inj_args evd p cop m k typeargs args2_l) in
        (get_red_name cop cop.cop_name ^ "__inj",
         close mkProd typeargs (mkProd (Context.make_annot Name.Anonymous Sorts.Relevant,
                                        mkApp (get_constr cop.cop_name, args1),
                                        mkApp (mkRel (k + 1 + m), args2))))
      end
      copreds
  in
  let injections2 =
    List.map
      begin fun (p, cop) ->
        let typeargs0 = get_inductive_typeargs evd (get_inductive cop.cop_name) in
        let typeargs = fix_injg_typeargs evd (2 * m + p) (List.map snd copreds) cop typeargs0 in
        let k = List.length typeargs in
        let args1_l = List.rev (List.map mkRel (range 1 (k + 1))) in
        let args2_l = List.rev (List.map mkRel (range 2 (k + 2))) in
        let args2 = Array.of_list (fix_ex_arg_inj_args evd p cop m k typeargs0 args2_l) in
        (get_red_name cop cop.cop_name ^ "__injg",
         close mkProd typeargs (mkProd (Context.make_annot Name.Anonymous Sorts.Relevant,
                                        make_green_cop (m + m + k + p) p cop args1_l,
                                        mkApp (mkRel (k + 1 + m + m), args2))))
      end
      copreds
  in
  let result =
    close mkProd (fix_ctx red_copred_decls)
      (close mkProd (fix_ctx injections)
         (close mkProd (fix_ctx injections2)
            (mkProd (Context.make_annot Name.Anonymous Sorts.Relevant, make_red (m + m + m) stmt, make_green (m + m + m + 1) stmt))))
  in
  let cohyps = make_coind_hyps evd m stmt
  in
  (evd, stmt, cohyps, result)
