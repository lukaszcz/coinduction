DECLARE PLUGIN "coinduction_plugin"

let coind_version_string = "CoInduction (dev) for Coq 8.9"

open Feedback

let () = Mltop.add_known_plugin (fun () ->
  Flags.if_verbose msg_info Pp.(str coind_version_string))
  "CoInduction"
;;

open Names
open Ltac_plugin
open Stdarg
open Extraargs

(***************************************************************************************)

let do_coinduction id cexpr =
  let open CUtils in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let (evd, ty) = intern_constr env evd cexpr in
  let (evd, stmt, cohyps, ty1) = CStmt.translate_statement evd ty in
  Feedback.msg_notice (Printer.pr_constr (EConstr.to_constr evd ty1));
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
  let kind = Decl_kinds.(Global, Flags.is_universe_polymorphism(), DefinitionBody Definition) in
  Proof_global.start_proof evd (id_app id "ᶜ") kind [(env, ty1)] terminator;
  let p = List.length copreds in
  let tac =
    let rec hlp n =
      if n = 0 then
        Tactics.introduction (Id.of_string "CH")
      else
        Proofview.tclTHEN Tactics.intro (hlp (n - 1))
    in
    hlp (2 * p)
  in
  ignore (Proof_global.with_current_proof begin fun _ prf ->
    Proof.run_tactic env tac prf
  end)

(***************************************************************************************)

let classify_proof_start_cmd _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]),VtLater)

VERNAC COMMAND EXTEND Coinduction_cmd CLASSIFIED BY classify_proof_start_cmd
| [ "CoInduction" ident(id) ":" lconstr(t) ] -> [ do_coinduction id t ]
END
