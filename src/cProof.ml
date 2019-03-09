(* Proof translation -- implementation *)

open Names
open CUtils
open CPred
open CStmt

let get_canonical_ind_name s = get_ind_name (get_inductive s)

let make_coproof evd s funs =
  let open EConstr in
  (* n - number of non-omitted binders up *)
  (* m - total number of binders up (including omitted ex binders) *)
  let mk_copred_prf l n p =
    let pr = List.nth funs p n in
    if n = l then
      pr
    else
      mkApp (pr, Array.of_list (List.rev (List.map mkRel (range (l + 1) (n + 1)))))
  in
  let mk_copred_type ctx k n p cop coargs =
    let args =
      List.map
        begin function
        | ATerm t ->
           shift_binders_down evd k t
        | AEx i ->
           let (p, l) = List.nth ctx (i - 1) in
           if p = -1 then
             mkRel i
           else
             mk_copred_prf (n - l) n p
        end
        coargs
    in
    mkApp (get_constr cop.cop_name, Array.of_list args)
  in
  let rec mk_type ctx k n s =
    match s with
    | SProd(na, ty, body) ->
       mkProd (na, shift_binders_down evd k ty, mk_type ((-1,0) :: ctx) k (n + 1) body)
    | SPred(p, cop, coargs) ->
       mk_copred_type ctx k n p cop coargs
    | SAnd (ind, args) ->
       mkApp(mkInd ind, Array.of_list (List.map (mk_type ctx k n) args))
    | SEx (ind, na, ty, body) ->
       begin
         match ty with
         | SPred(p, _, _) ->
            let ty2 = mk_type ctx k n ty in
            let body2 = mk_type ((-1,0) :: ctx) k (n + 1) body in
            mkApp(mkInd ind, [| ty2; mkLambda(na, ty2, body2) |])
         | _ ->
            failwith "SEx"
       end
  in
  let rec mk_prf ctx n m s =
    match s with
    | SProd (na, ty, body) ->
       mkLambda (na, shift_binders_down evd (m - n) ty, mk_prf ((-1,0) :: ctx) (n + 1) (m + 1) body)
    | SPred (p, cop, coargs) ->
       mk_copred_prf 0 n p
    | SAnd (ind, args) ->
       let tys = List.map (mk_type ctx (m - n) n) args in
       mkApp (mkConstruct (ind, 1), Array.of_list (tys @ List.map (mk_prf ctx n m) args))
    | SEx (ind, na, ty, body) ->
       begin
         match ty with
         | SPred (p, _, _) ->
            let ty2 = mk_type ctx (m - n) n ty in
            let predty = mkLambda (na, ty2, mk_type ((-1,0) :: ctx) (m - n) (n + 1) body) in
            let arg = mk_prf ctx n m ty in
            let body2 = mk_prf ((p, n) :: ctx) n (m + 1) body in
            mkApp (mkConstruct (ind, 1), [| ty2; predty; arg; body2 |])
         | _ ->
            failwith "make_coproof"
       end
  in
  mk_prf [] 0 0 s

let make_full_coproof evd s prfs =
  let open EConstr in
  let p = List.length prfs in
  let rec hlp prfs =
    match prfs with
    | (ty, pr) :: tl ->
       mkLetIn (Name.Anonymous, pr, ty, hlp tl)
    | [] ->
       make_coproof evd s (List.map (fun i n -> mkRel (n + p - i)) (range 0 p))
  in
  hlp prfs

(* k - absolute (top-down) index *)
let subst evd k t s =
  let open Constr in
  let open EConstr in
  map_constr
    begin fun n s ->
      match kind evd s with
      | Rel i when n - i = k ->
         shift_binders_up evd n t
      | _ ->
         s
    end
    evd
    s

(* k - absolute (top-down) index *)
let rec update_ctx evd k n t ctx =
  match ctx with
  | [] -> []
  | (j, _, _) :: ctx1 when j = k ->
     (j, n, t) :: update_ctx evd k n t ctx1
  | (j, m, s) :: ctx1 ->
     (j, n, subst evd k t (shift_binders_up evd (n - m) s)) :: update_ctx evd k n t ctx1

let skip_cases extract evd n ctx tctx t cont =
  let open Constr in
  let open EConstr in
  let rec skip b_start n j ctx tctx t =
    let combine m ci (f : EConstr.t array -> EConstr.t -> EConstr.t) branches ret value =
      let lst1 =
        List.map2
          begin fun k br ->
            let (t, i) = drop_lambdas evd (m + k + j) br in
            let tps = List.rev (List.map snd (take_lambdas evd (m + k + j - i) br)) in
            skip false (n + m + k + j - i) i ctx (tps @ tctx) t
          end
          (Array.to_list ci.ci_cstr_ndecls)
          branches
      in
      let lambdas1 =
        List.map2 (fun k -> take_lambdas evd (m + k + j))
          (Array.to_list ci.ci_cstr_ndecls) branches
      in
      let lambdas2 = take_all_lambdas evd ret in
      let k = List.length lambdas2 in
      let retargs =
        match kind evd value with
        | Rel i ->
           begin
             assert (n = List.length tctx);
             let ty = List.nth tctx (i - 1) in
             match kind evd ty with
             | App (c, args) ->
                List.map (shift_binders_up evd i)
                  (drop (Array.length args - k + 1) (Array.to_list args))
             | _ ->
                failwith "skip_cases: match on an unsupported (co)inductive type"
           end
        | _ -> repl (k - 1) mkSet
      in
      let retargs = retargs @ [ value ] in
      assert (List.length retargs = k);
      let ret0 = drop_all_lambdas evd ret in
      let peek_needed = rel_occurs evd ret0 (range 1 (k + 1)) in
      let prods = take_prods evd m ret0 in
      let ret0 = drop_prods evd m ret0 in
      let ctx =
        match kind evd value with
        | Rel i -> update_ctx evd (n - i) (n + k) (mkRel 1) ctx
        | _ -> ctx
      in
      let lst2 = extract retargs peek_needed (peek_needed && b_start) n m k ctx ret0 in
      let len = List.length (List.hd lst1) in
      assert (List.length lst2 = len);
      let rec hlp lst1 lst2 len acc =
        if len = 0 then
          List.rev acc
        else
          let lst = List.map (List.hd) lst1 in
          let p = fst (List.hd lst) in
          let lst = List.map snd lst in
          let branches2 = Array.of_list (List.map2 (close mkLambda) lambdas1 lst) in
          let case2 =
            List.hd lst2
              begin fun h ->
                let ret2 = close mkLambda lambdas2 (close mkProd prods h) in
                if k > 0 then
                  f branches2 ret2
                else
                  f branches2 ret2
              end
          in
          hlp (List.map (List.tl) lst1) (List.tl lst2) (len - 1) ((p, case2) :: acc)
      in
      hlp lst1 lst2 len []
    in
    match kind evd t with
    | Case (ci, ret, value, branches) ->
       combine 0 ci
         (fun br ret -> mkCase (ci, ret, value, br))
         (Array.to_list branches) ret value
    | App (c, args) ->
       begin
         match kind evd c with
         | Case (ci, ret, value, branches) ->
            combine (Array.length args) ci
              (fun br ret -> mkApp (mkCase (ci, ret, value, br), args))
              (Array.to_list branches) ret value
         | _ ->
            cont tctx n t
       end
    | _ ->
       cont tctx n t
  in
  skip true n 0 ctx tctx t

let make_ch_prf evd n p i ctx =
  let open EConstr in
  mkApp (mkRel (n + 3 * p - i),
         Array.of_list (List.rev (List.map (fun (_, k, t) ->
                                      shift_binders_up evd (n - k) t) ctx)))

let translate_proof stmt copreds cohyps evd ty prf =
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
  let fix_g_args ind args =
    let s = get_ind_name ind in
    let (_, cop) = List.assoc s g_ind_assoc in
    drop (List.length cop.cop_ex_arg_idxs + 1) args
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
  (* k1 - the number of variables between the proof and the injections
     (coinductive hypotheses) which the term assumes *)
  (* k2 - the number of coinductive hypotheses added *)
  let fix_proof k1 k2 evd pr =
    CNorm.norm_beta evd
      (map_constr
         begin fun m t ->
           match kind evd t with
           | Rel i when i > m + k1 && i <= m + k1 + p ->
              (* Rel points at an injection *)
              List.nth injs (m + k1 + p - i)
           | Rel i when i > m + k1 + p && i <= m + k1 + 2 * p ->
              (* Rel points at a red parameter *)
              mkInd (get_inductive (List.nth ind_names (m + k1 + 2 * p - i)))
           | Rel i when i > m + k1 + 2 * p && i <= m + k1 + 3 * p ->
              (* Rel points at a (unfixed) coinductive hypothesis *)
              let q = m + k1 + 3 * p - i in
              mkRel (m + k2 - q)
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
         pr)
  in
  (* m - the number of implications dropped from the return type *)
  (* k - the number of lambdas in case return type *)
  let rec extract_types fa n0 retargs peek_needed peek_eq_needed m k ctx n s t =
    let id x = x in
    match s with
    | SProd (na, ty, body) ->
       begin
         match kind evd t with
         | Prod (na1, ty1, body1) ->
            extract_types (fun x -> fa (mkProd (na1, ty1, x)))
              n0 retargs peek_needed peek_eq_needed m k
              ((n, n + 1, mkRel 1) :: ctx) (n + 1) body body1
         | _ ->
            failwith "extract_types: unsupported coinductive type (1)"
       end
    | SPred _ ->
       [(fun f -> f (fa t))]
    | SAnd (ind, args) ->
       begin
         match kind evd t with
         | App (c, args2) when Array.length args2 = List.length args ->
            List.concat (List.map2
                           (extract_types fa n0 retargs peek_needed peek_eq_needed m k ctx n)
                           args (Array.to_list args2))
         | _ ->
            failwith "extract_types: unsupported coinductive type (2)"
       end
    | SEx (ind, na, SPred (i, cop, _), body) ->
       begin
         let prods = take_all_prods evd t in
         let t = drop_all_prods evd t in
         let plen = List.length prods in
         let prods2 = List.map (fun (na, x) -> (na, shift_binders_up evd 1 x)) prods in
         match kind evd t with
         | App (c, [| t1; t2 |]) ->
            begin
              let pr = make_ch_prf evd (n + plen) p i ctx in
              match kind evd t2 with
              | Lambda (na2, ty2, body2) ->
                 let (tyind, tyargs) =
                   match kind evd ty2 with
                   | Ind _ -> (ty2, [])
                   | App (c, args) -> (c, Array.to_list args)
                   | _ -> failwith "extract_types: expected a (co)inductive type"
                 in
                 let ind =
                   match kind evd tyind with
                   | Ind (ind, _) -> ind
                   | _ -> failwith "extract_types: expected a (co)inductive type"
                 in
                 let tyargs1 = fix_g_args ind tyargs
                 in
                 let pr =
                   if peek_needed then
                     mkApp (get_constr (CPeek.get_peek_name cop.cop_name),
                            Array.of_list (tyargs1 @ [pr]))
                   else
                     pr
                 in
                 let t3 = CNorm.norm_beta evd (mkApp (t2, [| pr |])) in
                 let tps =
                   List.combine
                     (extract_types (fun x -> fa (close mkProd prods x))
                        n0 retargs peek_needed peek_eq_needed
                        m k ctx (n + plen) body t3)
                     (extract_types (fun x -> fa (close mkProd prods2 x))
                        n0 retargs false false
                        m k ctx (n + plen + 1) body body2)
                 in
                 (fun f -> f (close mkProd prods t1)) ::
                   if peek_eq_needed then
                     List.map begin fun (fx, fy) f ->
                       assert (k > 0);
                       let x = fx f in
                       let y = fy id in
                       if rel_occurs evd y (range 1 (m + k + 1)) then
                         let pr0 =
                           mkApp (mkRel (n0 + 3 * p - i),
                                  Array.of_list
                                    (List.rev (List.map
                                                 (fun (j, _, _) -> mkRel (n0 - j))
                                                 ctx)))
                         in
                         let tyargs0 = List.map (shift_binders_down evd (n - n0 + plen)) tyargs1 in
                         let ty0 = shift_binders_down evd (n - n0 + plen) ty2 in
                         let subst_retargs t =
                           CNorm.norm_beta evd
                             (mkApp (List.fold_left
                                       (fun acc _ -> mkLambda (na2, ty2, acc))
                                       t retargs,
                                     Array.of_list retargs))
                         in
                         let ret =
                           subst_retargs (shift_binders_down evd m (mkLambda (na2, ty2, y)))
                         in
                         mkApp (get_constr "eq_ind",
                                [| ty0;
                                   mkApp (get_constr (CPeek.get_peek_name cop.cop_name),
                                          Array.of_list (tyargs0 @ [pr0]));
                                   ret;
                                   x;
                                   pr0;
                                   mkApp (get_constr (CPeek.get_peek_eq_name cop.cop_name),
                                          Array.of_list (tyargs0 @ [pr0]));
                                |])
                       else
                         x
                     end tps
                   else
                     (List.map fst tps)
              | _ ->
                 failwith "extract_types: unsupported coinductive type (3)"
            end
         | _ ->
            failwith "extract_types: unsupported coinductive type (4)"
       end
    | _ ->
       failwith "impossible"
  in
  let rec extract_proofs ctx tctx n s t =
    let skip =
      skip_cases
        begin fun retargs peek_needed peek_eq_needed n m k ctx ->
          extract_types (fun x -> x) n retargs peek_needed peek_eq_needed m k ctx (n + k + m) s
        end
        evd n ctx tctx t
    in
    match s with
    | SProd (na, ty, body) ->
       skip
         begin fun tctx n t ->
           match kind evd t with
           | Lambda (na1, ty1, body1) ->
              List.map (fun (p, x) -> (p, mkLambda (na1, ty1, x)))
                (extract_proofs ((n, n + 1, mkRel 1) :: ctx) (ty1 :: tctx) (n + 1) body body1)
           | _ ->
              failwith "unsupported coinductive proof (1)"
         end
    | SPred (p, cop, coargs) ->
       [(p, t)]
    | SAnd (ind, args) ->
       begin
         let m = List.length args in
         skip
           begin fun tctx n t ->
             match kind evd t with
             | App (c, args2) when Array.length args2 = 2 * m ->
                List.concat (List.map2 (extract_proofs ctx tctx n)
                               args
                               (drop m (Array.to_list args2)))
             | _ ->
                failwith "unsupported coinductive proof (2)"
           end
       end
    | SEx (ind, na, ty, body) ->
       begin
         skip
           begin fun tctx n t ->
             match kind evd t with
             | App (c, [| _; _; t1; t2 |]) ->
                extract_proofs ctx tctx n ty t1 @ extract_proofs ctx tctx n body t2
             | _ ->
                begin
                  failwith "unsupported coinductive proof (3)"
                end
           end
       end
  in
  let rec hlp m t =
    if m = 2 * p + 1 then
      begin
        if p = 1 then
          mkCoFix (0, ([| Name.Anonymous |], [| ty |], [| fix_proof 1 1 evd t |]))
        else
          let ch = make_coproof evd stmt (List.map (fun i n -> mkRel (n + 3 * p - i)) (range 0 p))
          in
          let t2 = CNorm.norm evd (mkApp (mkLambda (Name.Anonymous, ty, t), [| ch |]))
          in
          (* Assumption: all and-like and ex-like constructors in ch
             will be destroyed by normalizing t2; if any are left then
             t2 is not well-typed *)
          let lst =
            List.map2
              begin fun (p, pr) ty ->
                let ty2 = fix_proof p p evd ty in
                (ty2,
                 mkCoFix (0, ([| Name.Anonymous |],
                              [| ty2 |],
                              [| fix_proof 0 (p + 1) evd pr |])))
              end
              (extract_proofs [] [] 0 stmt t2)
              cohyps
          in
          make_full_coproof evd stmt lst
      end
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
  let r = hlp 0 prf'
  in
  Feedback.msg_notice (Printer.pr_constr (EConstr.to_constr evd r));
  (evd, r)
