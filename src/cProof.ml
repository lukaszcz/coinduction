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

let mk_neutral evd k p cop coargs =
  let open EConstr in
  let args =
    List.map
      begin function
      | ATerm t ->
         shift_binders evd k t
      | AEx i ->
         failwith ("unsupported coinductive statement: " ^
                      "unsupported existential dependency")
      end
      coargs
  in
  mkApp (get_constr cop.cop_name, Array.of_list args)

let make_coproof evd s funs =
  let open EConstr in
  (* n - number of non-ex binders up *)
  (* m - total number of binders up *)
  let rec hlp n m s =
    match s with
    | SProd (na, ty, body) ->
       mkLambda (na, shift_binders evd (m - n) ty, hlp (n + 1) (m + 1) s)
    | SPred (p, cop, coargs) ->
       let pr = List.nth funs p n in
       if n = 0 then
         pr
       else
         mkApp (pr, Array.of_list (List.rev (List.map mkRel (range 1 (n + 1)))))
    | SAnd (ind, args) ->
       mkApp (mkConstruct (ind, 1), Array.of_list (List.map (hlp n m) args))
    | SEx (ind, na, ty, body) ->
       begin
         match ty with
         | SPred (p, cop, coargs) ->
            let arg = hlp n m ty in
            let body2 = hlp n (m + 1) body in
            let t =
              CNorm.norm_beta evd
                (mkApp (mkLambda (na, mk_neutral evd (m - n) p cop coargs, body2), [| arg |]))
            in
            mkApp (mkConstruct (ind, 1), [| arg; t |])
         | _ ->
            failwith "make_coproof"
       end
  in
  hlp 0 0 s

let make_full_coproof evd s prfs =
  let open EConstr in
  let p = List.length prfs in
  let rec hlp prfs =
    match prfs with
    | (ty, pr) :: tl ->
       mkApp (mkLambda (Name.Anonymous, ty, hlp tl), [| pr |])
    | [] ->
       make_coproof evd s (List.map (fun i n -> mkRel (n + p - i)) (range 0 p))
  in
  hlp prfs

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
  (* k - the number of variables between the proof and the injections
     (coinductive hypotheses) *)
  let fix_proof k =
    map_constr
      begin fun m t ->
        match kind evd t with
        | Rel i when i > m + k && i <= m + k + p ->
         (* Rel points at an injection *)
           List.nth injs (i - m - 2)
        | Rel i when i > m + k + p && i <= m + k + 2 * p ->
         (* Rel points at a red parameter *)
           mkInd (get_inductive (List.nth ind_names (m + k + 2 * p - i)))
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
  in
  let extract s t =
    let rec extract s t acc =
      match s with
      | SProd (na, ty, body) ->
         begin
           match kind evd t with
           | Lambda (na1, ty1, body1) ->
              List.map (fun (p, x) -> (p, mkLambda (na1, ty1, x))) (extract body body1 acc)
           | _ ->
              failwith "unsupported coinductive proof"
         end
      | SPred (p, cop, coargs) ->
         (p, t) :: acc
      | SAnd (ind, args) ->
         begin
           match kind evd t with
           | App (c, args2) when List.length args = Array.length args2 ->
              List.fold_left2 (fun acc s' t' -> extract s' t' acc) acc args (Array.to_list args2)
           | _ ->
              failwith "unsupported coinductive proof"
         end
      | SEx (ind, na, ty, body) ->
         begin
           match kind evd t with
           | App (c, [| t1; t2 |]) ->
              extract body t2 (extract ty t1 acc)
           | _ ->
              failwith "unsupported coinductive proof"
         end
    in
    List.rev (extract s t [])
  in
  let rec hlp m t =
    if m = 2 * p + 1 then
      begin
        if p = 1 then
          mkCoFix (0, ([| Name.Anonymous |], [| ty |], [| fix_proof 1 evd t |]))
        else
          let ch = make_coproof evd stmt (repl p (fun n -> mkRel (n + 1)))
          in
          let t2 = CNorm.norm evd (mkApp (mkLambda (Name.Anonymous, ty, t), [| ch |]))
          in
          let lst =
            List.map2
              begin fun (p, pr) ty ->
                let ty2 = fix_proof p evd ty in
                (ty2,
                 mkCoFix (0, ([| Name.Anonymous |],
                              [| ty2 |],
                              [| fix_proof (p + 1) evd pr |])))
              end
              (extract stmt t2)
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
  let r = CNorm.norm_beta evd (hlp 0 prf')
  in
  Feedback.msg_notice (Printer.pr_constr (EConstr.to_constr evd r));
  (evd, r)
