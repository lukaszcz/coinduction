open Names

(***************************************************************************************)

let do_coinduction id cexpr =
  let open CUtils in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let (evd, ty) = intern_constr env evd cexpr in
  let (evd, stmt, cohyps, ty1) = CStmt.translate_statement evd ty in
  let (evd, ty1) = Typing.solve_evars (Global.env ()) evd ty1 in
  let copreds = CStmt.get_copreds stmt in
  let terminator com =
    let open Proof_global in
    let (opaque, lemma_def) =
      match com with
      | Admitted _ -> (* TODO: should declare as axiom *)
         CErrors.user_err Pp.(str "Admitted isn't supported in CoInduction.")
      | Proved (_, Some _, _) ->
         CErrors.user_err Pp.(str "Cannot save a proof of CoInduction with an explicit name.")
      | Proved (opaque, None, obj) ->
         match Proof_global.(obj.entries) with
         | [lemma_def] ->
            (opaque <> Proof_global.Transparent,
             Safe_typing.inline_private_constants_in_definition_entry env lemma_def)
         | _ -> assert false
    in
    let ((prf, uctxs), ()) = Future.force Entries.(lemma_def.const_entry_body) in
    (* I'm not sure if ignoring uctxs won't create a bug somewhere,
       but I don't know how to combine it with evd *)
    let (evd, prf) = CProof.translate_proof stmt copreds cohyps evd ty (EConstr.of_constr prf) in
    CUtils.declare_definition id evd prf
  in
  let terminator = Proof_global.make_terminator terminator in
  let kind = Decl_kinds.(Global, true, DefinitionBody Definition) in
  let gprf =
    Proof_global.start_proof ~ontop:None
      evd (id_app id "ᶜ") kind [(Global.env (), ty1)] terminator
  in
  let p = List.length copreds in
  let tac =
    let rec hlp n =
      if n = 0 then
        Tactics.introduction (Id.of_string "CH")
      else
        Proofview.tclTHEN Tactics.intro (hlp (n - 1))
    in
    hlp (3 * p)
  in
  fst (Proof_global.with_current_proof begin fun _ prf ->
     Proof.run_tactic (Global.env ()) tac prf
  end gprf)

(***************************************************************************************)

let do_declare_peek id =
  let env = Global.env () in
  let evd = Evd.from_env env in
  CPeek.declare_peek evd (Id.to_string id)

let do_rewrite_peek ty =
  Proofview.Goal.enter
    begin fun gl ->
      let evd = Proofview.Goal.sigma gl in
      let open Constr in
      let open EConstr in
      let ind =
        match kind evd ty with
        | Ind (ind, _) -> ind
        | App(a, _) ->
           begin
             match kind evd a with
             | Ind(ind, _) -> ind
             | _ -> failwith "rewrite_peek: not a coinductive type"
           end
        | _ -> failwith "rewrite_peek: not a coinductive type"
      in
      let peek = CUtils.get_constr (CPeek.get_peek_eq_name (CUtils.get_ind_name ind)) in
      Equality.rewriteRL peek
    end
