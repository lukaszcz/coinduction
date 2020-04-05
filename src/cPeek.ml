(* Peeking at coinductive values -- implementation *)

open Names
open CUtils

let get_peek_name ind_name = "peek__" ^ get_basename ind_name

let get_peek_eq_name ind_name = "peek_eq__" ^ get_basename ind_name

let declare_peek_fun evd ind_name =
  let open Constr in
  let open EConstr in
  let open Declarations in
  let anon = Context.make_annot Name.Anonymous Sorts.Relevant in
  let ind = get_inductive ind_name in
  let (mind, one_ind) = Inductive.lookup_mind_specif (Global.env ()) ind in
  let typeargs = get_inductive_typeargs evd ind in
  let tyind = EConstr.of_constr (Inductive.type_of_inductive (Global.env ()) (Univ.in_punivs (mind, one_ind))) in
  let nparams = mind.mind_nparams in
  let n = List.length typeargs in
  let params2 = List.rev (List.map mkRel (range (n - nparams + 2) (n + 2))) in
  let branches =
    List.map2
      begin fun (lc, i) p ->
        let lc = CNorm.norm_beta evd (EConstr.of_constr lc) in
        let lc = CNorm.norm_beta evd (mkApp(mkLambda (anon, tyind, lc), [| mkInd ind |])) in
        let lambdas = take_prods evd (i + nparams) lc in
        let t =
        CNorm.norm_beta evd
          (mkApp
             (close mkLambda lambdas
                (mkApp (mkConstruct (ind, p),
                        Array.of_list (List.rev (List.map mkRel (range 1 (i + nparams + 1)))))),
              Array.of_list params2))
        in
        t
      end
      (List.combine (Array.to_list one_ind.mind_user_lc) (Array.to_list one_ind.mind_consnrealargs))
      (range 1 (Array.length one_ind.mind_user_lc + 1))
  in
  let ci = Inductiveops.make_case_info (Global.env ()) ind Sorts.Relevant MatchStyle in
  let ty = mkApp(mkInd ind, Array.of_list (List.rev (List.map mkRel (range 1 (n + 1))))) in
  let ty0 = mkApp(mkInd ind, Array.of_list (List.rev (List.map mkRel (range 2 (n + 2))))) in
  let ret = close mkLambda typeargs (mkLambda (anon, ty, ty0)) in
  let ret = CNorm.norm_beta evd (mkApp (ret, Array.of_list params2)) in
  let case = mkCase(ci, ret, mkRel 1, Array.of_list branches) in
  let peek = close mkLambda typeargs (mkLambda (anon, ty, case)) in
  let (evd, peek) = Typing.solve_evars (Global.env ()) evd peek in
  declare_definition (string_to_id (get_peek_name ind_name)) evd peek

let declare_peek_eq evd ind_name =
  let open Constr in
  let open EConstr in
  let open Declarations in
  let anon = Context.make_annot Name.Anonymous Sorts.Relevant in
  let ind = get_inductive ind_name in
  let (mind, one_ind) = Inductive.lookup_mind_specif (Global.env ()) ind in
  let typeargs = get_inductive_typeargs evd ind in
  let tyind = EConstr.of_constr (Inductive.type_of_inductive (Global.env ()) (Univ.in_punivs (mind, one_ind))) in
  let nparams = mind.mind_nparams in
  let n = List.length typeargs in
  if n <> nparams then
    failwith "peeking is not supported for coinductive types with non-parameter arguments";
  let params2 = List.rev (List.map mkRel (range (n - nparams + 2) (n + 2))) in
  let peek = get_constr (get_peek_name ind_name) in
  let branches =
    List.map2
      begin fun (lc, i) p ->
        let lc = CNorm.norm_beta evd (EConstr.of_constr lc) in
        let lc = CNorm.norm_beta evd (mkApp(mkLambda (anon, tyind, lc), [| mkInd ind |])) in
        let lambdas = take_prods evd (i + nparams) lc in
        let params =
          List.rev (List.map mkRel (range (i + 1) (i + nparams + 1)))
        in
        let args =
          params @
            [ mkApp (mkConstruct (ind, p),
                     Array.of_list (List.rev (List.map mkRel (range 1 (i + nparams + 1))))) ]
        in
        CNorm.norm_beta evd
          (mkApp
             (close mkLambda lambdas
                (mkApp (get_constr "eq_refl",
                        [| mkApp (mkInd ind, Array.of_list params); mkApp (peek, Array.of_list args)|])),
              Array.of_list params2))
      end
      (List.combine (Array.to_list one_ind.mind_user_lc) (Array.to_list one_ind.mind_consnrealargs))
      (range 1 (Array.length one_ind.mind_user_lc + 1))
  in
  let ci = Inductiveops.make_case_info (Global.env ()) ind Sorts.Relevant MatchStyle in
  let ty = mkApp(mkInd ind, Array.of_list (List.rev (List.map mkRel (range 1 (n + 1))))) in
  let ty2 = mkApp(mkInd ind, Array.of_list (List.rev (List.map mkRel (range 2 (n + 2))))) in
  let ty0 =
    mkApp (get_constr "eq",
           [| ty2;
              mkApp(peek,
                    Array.of_list (List.rev (List.map mkRel (range 2 (n + 2))) @ [ mkRel 1 ]));
              mkRel 1
           |])
  in
  let ret0 = close mkLambda typeargs (mkLambda (anon, ty, ty0)) in
  let ret = CNorm.norm_beta evd (mkApp (ret0, Array.of_list params2)) in
  let case = mkCase(ci, ret, mkRel 1, Array.of_list branches) in
  let peek_eq = close mkLambda typeargs (mkLambda (anon, ty, case)) in
  let (evd, peek_eq) = Typing.solve_evars (Global.env ()) evd peek_eq in
  declare_definition (string_to_id (get_peek_eq_name ind_name)) evd peek_eq

let declare_peek evd ind_name =
  if not (exists_global (get_peek_name (ind_name))) then
    begin
      ignore (declare_peek_fun evd ind_name)
    end;
  if not (exists_global (get_peek_eq_name (ind_name))) then
    begin
      ignore (declare_peek_eq evd ind_name)
    end
