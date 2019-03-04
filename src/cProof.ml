(* Proof translation -- implementation *)

open Names
open CUtils
open CPred
open CStmt

let get_canonical_ind_name s = get_ind_name (get_inductive s)

let shift_binders evd k t =
  if k = 0 then
    t
  else
    let open EConstr in
    let dummy = mkSet in
    let rec hlp k t =
      if k = 0 then
        t
      else
        mkLambda (Name.Anonymous, dummy, hlp (k - 1) t)
    in
    CNorm.norm_beta evd (mkApp (hlp k t, Array.of_list (repl k dummy)))

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
           shift_binders evd k t
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
       mkProd (na, shift_binders evd k ty, mk_type ((-1,0) :: ctx) k (n + 1) body)
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
       mkLambda (na, shift_binders evd (m - n) ty, mk_prf ((-1,0) :: ctx) (n + 1) (m + 1) body)
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

let rec drop_lambdas evd n t =
  let open Constr in
  let open EConstr in
  if n = 0 then
    t
  else
    match kind evd t with
    | Lambda (na, ty, body) -> drop_lambdas evd (n - 1) body
    | _ -> failwith "drop_lambdas"

let rec take_lambdas evd n t =
  let open Constr in
  let open EConstr in
  if n = 0 then
    []
  else
    match kind evd t with
    | Lambda (na, ty, body) -> (na, ty) :: take_lambdas evd (n - 1) body
    | _ -> failwith "drop_lambdas"

let rec drop_all_lambdas evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | Lambda (na, ty, body) -> drop_all_lambdas evd body
  | _ -> t

let rec take_all_lambdas evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | Lambda (na, ty, body) -> (na, ty) :: take_all_lambdas evd body
  | _ -> []

let rec make_lambdas pref t =
  let open Constr in
  let open EConstr in
  match pref with
  | (na, ty) :: tl -> mkLambda (na, ty, make_lambdas tl t)
  | [] -> t

let skip_cases extract evd t cont =
  let open Constr in
  let open EConstr in
  let rec skip t =
    let combine ci (f : EConstr.t array -> EConstr.t -> EConstr.t) branches ret value =
      let lst1 = List.map skip (List.map2 (drop_lambdas evd) (Array.to_list ci.ci_cstr_ndecls) branches) in
      let lambdas1 = List.map2 (take_lambdas evd) (Array.to_list ci.ci_cstr_ndecls) branches in
      let lambdas2 = take_all_lambdas evd ret in
      let k = List.length lambdas2 in
      let k1 = match kind evd value with Rel i -> i | _ -> -1 in
      let k1 = if k > 0 then k1 else -1 in
      let lst2 = extract k1 k (drop_all_lambdas evd ret) in
      let n = List.length (List.hd lst1) in
      assert (List.length lst2 = n);
      let rec hlp lst1 lst2 n acc =
        if n = 0 then
          List.rev acc
        else
          let lst = List.map (List.hd) lst1 in
          let p = fst (List.hd lst) in
          let lst = List.map snd lst in
          let branches2 = Array.of_list (List.map2 make_lambdas lambdas1 lst) in
          let case2 =
            List.hd lst2
              begin fun h ->
                let ret2 = make_lambdas lambdas2 h in
                if k > 0 then
                  f branches2 ret2
                else
                  f branches2 ret2
              end
          in
          hlp (List.map (List.tl) lst1) (List.tl lst2) (n - 1) ((p, case2) :: acc)
      in
      hlp lst1 lst2 n []
    in
    match kind evd t with
    | Case (ci, ret, value, branches) ->
       combine ci (fun br ret -> mkCase (ci, ret, value, br)) (Array.to_list branches) ret value
    | App (c, args) ->
       begin
         match kind evd c with
         | Case (ci, ret, value, branches) ->
            combine ci (fun br ret -> mkApp (mkCase (ci, ret, value, br), args)) (Array.to_list branches) ret value
         | _ ->
            cont t
       end
    | _ ->
       cont t
  in
  skip t

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
              List.nth injs (i - m - k1 - 1)
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
  (* k - the number of lambdas in case return type *)
  (* k1 - the absolute (top-down) index of the variable matched on (-1 if none) *)
  (* k2 - the absolute (top-down) index of the last lambda in case return type *)
  let rec extract_types fa do_peek k k1 k2 ctx n s t =
    let id x = x in
    match s with
    | SProd (na, ty, body) ->
       begin
         match kind evd t with
         | Prod (na1, ty1, body1) ->
            extract_types (fun x -> fa (mkProd (na1, ty1, x))) do_peek k k1 k2 (n :: ctx) (n + 1) body body1
         | _ ->
            failwith "extract_types: unsupported coinductive type (1)"
       end
    | SPred (p, cop, coargs) ->
       [(fun f -> f (fa t))]
    | SAnd (ind, args) ->
       begin
         match kind evd t with
         | App (c, args2) when Array.length args2 = List.length args ->
            List.concat (List.map2 (extract_types fa do_peek k k1 k2 ctx n) args (Array.to_list args2))
         | _ ->
            failwith "extract_types: unsupported coinductive type (2)"
       end
    | SEx (ind, na, SPred (i, _, _), body) ->
       begin
         match kind evd t with
         | App (c, [| t1; t2 |]) ->
            begin
              let pr =
                mkApp (mkRel (n + 3 * p - i),
                       Array.of_list (List.rev (List.map (fun j -> if j = k1 then mkRel (n - k2) else mkRel (n - j)) ctx)))
              in
              match kind evd t2 with
              | Lambda (na2, ty2, body2) ->
                 let peek_needed = do_peek && List.mem k1 ctx in
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
                     mkApp (get_constr "peek", Array.of_list (tyargs1 @ [pr]))
                   else
                     pr
                 in
                 let t3 = CNorm.norm_beta evd (mkApp (t2, [| pr |])) in
                 let tps =
                   List.combine
                     (extract_types fa do_peek k k1 k2 ctx n body t3)
                     (extract_types fa false k k1 k2 ctx (n + 1) body body2)
                 in
                 (fun f -> f t1) ::
                   if peek_needed then
                     List.map begin fun (fx, fy) f ->
                       assert (k > 0);
                       let x = fx f in
                       let y = fy id in
                       let pr0 =
                         mkApp (mkRel (n - k + 3 * p - i),
                                Array.of_list (List.rev (List.map (fun j -> mkRel (n - k - j)) ctx)))
                       in
                       let tyargs0 = List.map (shift_binders evd k) tyargs1 in
                       let ty0 = shift_binders evd k ty2 in
                       let ret =
                         shift_binders evd (k - 1)
                           (CNorm.norm_beta evd
                              (mkApp (mkLambda (na2, ty2, mkLambda (na2, ty2, y)), [| mkRel (n - k1 - 1) |])))
                       in
                       mkApp (get_constr "eq_ind",
                              [| ty0;
                                 mkApp (get_constr "peek", Array.of_list (tyargs0 @ [pr0]));
                                 ret;
                                 x;
                                 pr0;
                                 mkApp (get_constr "peek_eq", Array.of_list (tyargs0 @ [pr0]));
                              |])
                     end tps
                   else
                     (List.map fst tps)
              | _ ->
                 failwith "extract_types: unsupported coinductive type (3)"
            end
         | _ ->
            failwith "extract_types: unsupported coinductive type (4)"
       end
  in
  let rec extract_proofs ctx n s t =
    let skip =
      skip_cases (fun k1 k -> extract_types (fun x -> x) true k (n - k1) (n + k - 1) ctx (n + k) s) evd t
    in
    match s with
    | SProd (na, ty, body) ->
       skip
         begin fun t ->
           match kind evd t with
           | Lambda (na1, ty1, body1) ->
              List.map (fun (p, x) -> (p, mkLambda (na1, ty1, x))) (extract_proofs (n :: ctx) (n + 1) body body1)
           | _ ->
              failwith "unsupported coinductive proof (1)"
         end
    | SPred (p, cop, coargs) ->
       [(p, t)]
    | SAnd (ind, args) ->
       begin
         let m = List.length args in
         skip
           begin fun t ->
             match kind evd t with
             | App (c, args2) when Array.length args2 = 2 * m ->
                List.concat (List.map2 (extract_proofs ctx n) args (drop m (Array.to_list args2)))
             | _ ->
                failwith "unsupported coinductive proof (2)"
           end
       end
    | SEx (ind, na, ty, body) ->
       begin
         skip
           begin fun t ->
             match kind evd t with
             | App (c, [| _; _; t1; t2 |]) ->
                extract_proofs ctx n ty t1 @ extract_proofs ctx n body t2
             | _ ->
                failwith "unsupported coinductive proof (3)"
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
          Feedback.msg_notice (Printer.pr_constr (EConstr.to_constr evd ch));
          let t2 = CNorm.norm evd (mkApp (mkLambda (Name.Anonymous, ty, t), [| ch |]))
          in
          Feedback.msg_notice (Printer.pr_constr (EConstr.to_constr evd t2));
          (* Assumption: all and-like and ex-like constructors in ch
             will be destroyed by normalizing t2; if any are left then
             t2 is not well-typed *)
          let lst =
            List.map2
              begin fun (p, pr) ty ->
                Feedback.msg_notice (Printer.pr_constr (EConstr.to_constr evd pr));
                let ty2 = fix_proof p p evd ty in
                (ty2,
                 mkCoFix (0, ([| Name.Anonymous |],
                              [| ty2 |],
                              [| fix_proof 0 (p + 1) evd pr |])))
              end
              (extract_proofs [] 0 stmt t2)
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
