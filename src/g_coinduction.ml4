DECLARE PLUGIN "coinduction_plugin"

let coind_version_string = "CoInduction (dev) for Coq 8.8"

open Feedback

let () = Mltop.add_known_plugin (fun () ->
  Flags.if_verbose msg_info Pp.(str coind_version_string))
  "Coinduction"
;;

open Names
open Ltac_plugin
open Stdarg

let (++) f g x = f(g(x))

(***************************************************************************************)

let get_current_context () =
  try
    Pfedit.get_current_goal_context ()
  with _ ->
    let env = Global.env () in
    (Evd.from_env env, env)

let to_constr r =
  match r with
  | VarRef(v) -> Constr.mkVar v
  | ConstRef(c) -> Constr.mkConst c
  | IndRef(i) -> Constr.mkInd i
  | ConstructRef(cr) -> Constr.mkConstruct cr

let get_global s =
  Nametab.locate (Libnames.qualid_of_string s)

let get_global_id id =
  Nametab.locate (Libnames.qualid_of_ident id)

let get_constr s =
  to_constr (get_global s)

let get_constr_id id =
  to_constr (get_global_id id)

let get_type_of env evmap t =
  EConstr.to_constr evmap (Retyping.get_type_of env evmap (EConstr.of_constr t))

let get_inductive s =
  match get_global s with
  | IndRef(i) -> i
  | _ -> failwith "get_inductive: not an inductive type"

let get_inductive_id id =
  match get_global_id id with
  | IndRef(i) -> i
  | _ -> failwith "get_inductive_id: not an inductive type"

let typ_to_constr typ =
  let (sigma, env) = get_current_context () in
  let (typ, uctx) = Constrintern.interp_type env sigma typ in
  let sigma = Evd.from_ctx uctx in
  let evm = ref sigma in
  let typ = Typing.e_solve_evars env evm typ in
  EConstr.to_constr !evm typ

(***************************************************************************************)

let is_coinductive (ind : inductive) =
  let env = snd (get_current_context ()) in
  let mind = fst (Inductive.lookup_mind_specif env ind) in
  let open Declarations in
  match mind.mind_finite with
  | CoFinite -> true
  | _ -> false

let get_inductive_typeargs (ind : inductive) =
  let open Constr in
  let rec hlp acc t =
    match kind t with
    | Prod(x, ty, b) -> hlp ((x,ty) :: acc) b
    | _ -> List.rev acc
  in
  let env = snd (get_current_context ()) in
  let minds = Inductive.lookup_mind_specif env ind in
  let tp = Inductive.type_of_inductive env (Univ.in_punivs minds) in
  hlp [] tp

(***************************************************************************************)

(* numbers from m up to but not including n *)
let range m n =
  let rec go acc i j =
    if i >= j then acc else go (i :: acc) (i + 1) j
  in List.rev (go [] m n)

let id_app id app = Id.of_string (Id.to_string id ^ app)

(* n - the original number of parameters *)
let fix_cons p n t =
  let open Constr in
  let get_params2 m =
    Array.of_list (List.map mkRel (List.rev (range (n + m) (n + m + p))))
  in
  let rec hlp m t =
    match kind t with
    | Prod (na, ty, c) ->
       mkProd (na, ty, (hlp (m + 1) c))
    | Rel i when i >= n + m ->
       mkApp (mkRel (i + p), get_params2 m)
    | App (c, args) ->
       begin
         match kind c with
         | Rel i when i >= n + m ->
            mkApp (mkRel (i + p), Array.append (get_params2 m) args)
         | _ ->
            failwith "unsupported coinductive type"
       end
    | _ ->
       failwith "unsupported coinductive type"
  in
  hlp 1 t

let transform_coinductive (ind : inductive) =
  let (evmap, env) = get_current_context () in
  let mind_body = fst (Inductive.lookup_mind_specif env ind) in
  let mind = CUtils.process_inductive mind_body in
  let open Entries in
  let p = List.length mind.mind_entry_inds
  and n = List.length mind.mind_entry_params
  in
  let inds2 =
    List.map
      begin fun e ->
        { e with
          mind_entry_typename = id_app e.mind_entry_typename "__g";
          mind_entry_consnames =
            List.map (fun id -> id_app id "__g") e.mind_entry_consnames;
          mind_entry_lc =
            List.map (fix_cons p n) e.mind_entry_lc;
        }
      end
      mind.mind_entry_inds
  in
  let ind_types =
    List.map (fun e -> get_type_of env evmap (get_constr_id e.mind_entry_typename)) mind.mind_entry_inds
  in
  let params2 =
    List.map2 (fun e tp -> (id_app e.mind_entry_typename "__r", tp))
      mind.mind_entry_inds ind_types
  in
  let mind2 =
    { mind with
      mind_entry_inds = inds2;
      mind_entry_params =
        mind.mind_entry_params @
          (List.rev (List.map (fun (x, y) -> (x, LocalAssumEntry y)) params2));
    }
  in
  ignore (Declare.declare_mind mind2);
  ((List.nth mind.mind_entry_inds (snd ind)).mind_entry_typename,
   List.map (fun e -> e.mind_entry_typename) mind.mind_entry_inds,
   params2)

let transform_statement t =
  let open Constr in
  let rec close ctx t =
    match ctx with
    | [] -> t
    | (x,ty) :: l -> mkProd (x, ty, close l t)
  in
  let fix_ctx = List.map (fun (x, y) -> (Name.mk_name x, y))
  in
  let hlp2 ctx ind args =
    if is_coinductive ind then
      let (id, ind_ids, params2) = transform_coinductive ind in
      let m = List.length ctx
      and p = List.length ind_ids
      in
      let args2 =
        Array.append (Array.of_list (List.map mkRel (range (m + p + 2) (m + p + 2 + p)))) args
      in
      let impls =
        List.map2
          begin fun id i ->
            let typeargs = get_inductive_typeargs (get_inductive_id id) in
            let m = List.length typeargs in
            let args1 = Array.of_list (List.rev (List.map mkRel (range 1 (m + 1)))) in
            let args2 = Array.of_list (List.rev (List.map mkRel (range 2 (m + 2)))) in
            (id_app id "__r__inj",
             close typeargs (mkProd (Name.Anonymous,
                                     mkApp (get_constr_id id, args1),
                                     mkApp (mkRel (p - snd ind + i + m + 1), args2))))
          end
          ind_ids
          (range 0 p)
      in
      close (fix_ctx params2)
        (close (fix_ctx impls)
           (mkProd (Name.Anonymous,
                    close (List.rev ctx) (mkApp (mkRel (p - snd ind + m + p), args)),
                    close (List.rev ctx) (mkApp (get_constr_id (id_app id "__g"), args2)))))
    else
      failwith "unsupported coinductive statement"
  in
  let rec hlp ctx t =
    match kind t with
    | Prod (na, ty, c) ->
       hlp ((na,ty) :: ctx) c
    | Ind (ind, u) ->
       hlp2 ctx ind [| |]
    | App (f, args) ->
       begin
         match kind f with
         | Ind (ind, u) ->
            hlp2 ctx ind args
         | _ ->
            failwith "unsupported coinductive statement"
       end
    | _ ->
       failwith "unsupported coinductive statement"
  in
  hlp [] t

(***************************************************************************************)

let transform_proof prf =
  prf

(***************************************************************************************)

VERNAC COMMAND EXTEND Coinduction_cmd CLASSIFIED AS SIDEFF
| [ "Coinduction" constr(t) ] ->
   [ msg_info (Printer.pr_constr (transform_statement (typ_to_constr t))) ]
END

TACTIC EXTEND coinduct_tac
| [ "coinduct" ] ->
   [ Proofview.tclUNIT () ]
END
