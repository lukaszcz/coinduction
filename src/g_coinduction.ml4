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
    (Evd.empty, Global.env ())

let to_constr r =
  match r with
  | VarRef(v) -> Constr.mkVar v
  | ConstRef(c) ->Constr.mkConst c
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
  let mind2 =
    { mind with
      mind_entry_inds = inds2;
      mind_entry_params =
        mind.mind_entry_params @
          (List.rev (List.map2 (fun e tp -> (id_app e.mind_entry_typename "__r", LocalAssumEntry tp))
                       mind.mind_entry_inds ind_types));
    }
  in
  msg_info (Pp.str "akuku!");
  ignore (Declare.declare_mind mind2)

(***************************************************************************************)

VERNAC COMMAND EXTEND Coinduct_cmd CLASSIFIED AS SIDEFF
| [ "Coinduct" string(s) ] ->
   [ transform_coinductive (get_inductive s) ]
END

TACTIC EXTEND coinduct_tac
| [ "coinduct" ] ->
   [ Proofview.tclUNIT () ]
END
