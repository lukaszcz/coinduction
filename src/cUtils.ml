open Util
open CErrors
open Context
open Rel.Declaration
open Term
open Names
open Declarations
open Entries
open Globnames

(***************************************************************************************)

(* numbers from m up to but not including n *)
let range m n =
  let rec go acc i j =
    if i >= j then acc else go (i :: acc) (i + 1) j
  in List.rev (go [] m n)

let rec repl n x =
  if n = 0 then
    []
  else
    x :: repl (n - 1) x

let rec take n lst =
  if n > 0 then
    match lst with
    | [] -> []
    | h :: t -> h :: take (n - 1) t
  else
    []

let rec drop n lst =
  if n > 0 then
    match lst with
    | [] -> []
    | h :: t -> drop (n - 1) t
  else
    lst

let string_ends_with s1 s2 =
  let n1 = String.length s1
  and n2 = String.length s2
  in
  if n1 < n2 then
    false
  else
    String.sub s1 (n1 - n2) n2 = s2

let get_basename s  =
  try
    let i = String.rindex s '.' in
    String.sub s (i + 1) (String.length s - i - 1)
  with Not_found ->
    s

let id_app id app = Id.of_string (Id.to_string id ^ app)

let string_to_id s = Id.of_string (get_basename s)

(***************************************************************************************)

let intern_constr env evd cexpr =
  let (t, uctx) = Constrintern.interp_constr env evd cexpr in
  let sigma = Evd.from_ctx uctx in
  Typing.solve_evars env sigma t

let to_constr r =
  match r with
  | VarRef(v) -> EConstr.mkVar v
  | ConstRef(c) -> EConstr.mkConst c
  | IndRef(i) -> EConstr.mkInd i
  | ConstructRef(cr) -> EConstr.mkConstruct cr

let get_global s =
  Nametab.locate (Libnames.qualid_of_string s)

let exists_global s =
  try
    ignore (get_global s);
    true
  with Not_found -> false

let get_constr s =
  to_constr (get_global s)

let get_inductive s =
  match get_global s with
  | IndRef(i) -> i
  | _ -> failwith "get_inductive: not an inductive type"

let get_ind_name ind =
  Libnames.string_of_path (Nametab.path_of_global (Globnames.canonical_gr (IndRef ind)))

let get_ind_nparams ind =
  let mind = fst (Inductive.lookup_mind_specif (Global.env ()) ind) in
  let open Declarations in
  mind.mind_nparams

let rec close f ctx t =
  match ctx with
  | [] -> t
  | (x,ty) :: l -> f (x, ty, close f l t)

(***************************************************************************************)

let map_fold_constr f acc evd t =
  let open Constr in
  let open EConstr in
  let rec hlp m acc t =
    let fold_arr k ac ar =
      let (ac1, lst) =
        List.fold_left
          (fun (ac,l) x -> let (ac',x') = hlp k ac x in (ac',x'::l))
          (ac, [])
          (Array.to_list ar)
      in
      (ac1, Array.of_list (List.rev lst))
    in
    match kind evd t with
    | Rel _ | Meta _ | Var _ | Sort _ | Const _ | Ind _ | Construct _ ->
       f m acc t
    | Cast (ty1,ck,ty2) ->
       let (acc1, ty1') = hlp m acc ty1 in
       let (acc2, ty2') = hlp m acc1 ty2 in
       f m acc2 (mkCast(ty1',ck,ty2'))
    | Prod (na,ty,c)    ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, c') = hlp (m+1) acc1 c in
       f m acc2 (mkProd(na,ty',c'))
    | Lambda (na,ty,c)  ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, c') = hlp (m+1) acc1 c in
       f m acc2 (mkLambda(na,ty',c'))
    | LetIn (na,b,ty,c) ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, b') = hlp m acc1 b in
       let (acc3, c') = hlp (m+1) acc2 c in
       f m acc3 (mkLetIn(na,b',ty',c'))
    | App (a,args) ->
       let (acc1, a') = hlp m acc a in
       let (acc2, args') = fold_arr m acc1 args in
       f m acc2 (mkApp(a',args'))
    | Proj (p,c) ->
       let (acc1, c') = hlp m acc c in
       f m acc1 (mkProj(p,c'))
    | Evar (evk,cl) ->
       let (acc1, cl') = fold_arr m acc cl in
       f m acc1 (mkEvar(evk,cl'))
    | Case (ci,p,c,bl) ->
       let (acc1, p') = hlp m acc p in
       let (acc2, c') = hlp m acc1 c in
       let (acc3, bl') = fold_arr m acc2 bl in
       f m acc3 (mkCase(ci,p',c',bl'))
    | Fix (nvn,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let (acc1, typs') = fold_arr m acc typs in
       let (acc2, bodies') = fold_arr (m + Array.length typs) acc1 bodies in
       f m acc2 (mkFix(nvn,(fnames,typs',bodies')))
    | CoFix (n,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let (acc1, typs') = fold_arr m acc typs in
       let (acc2, bodies') = fold_arr (m + Array.length typs) acc1 bodies in
       f m acc2 (mkCoFix(n,(fnames,typs',bodies')))
  in
  hlp 0 acc t

let map_constr f evd x = snd (map_fold_constr (fun m () t -> ((), f m t)) () evd x)

let fold_constr f acc evd x = fst (map_fold_constr (fun m acc t -> (f m acc t, t)) acc evd x)

let map_fold_constr_ker f acc t =
  let open Constr in
  let rec hlp m acc t =
    let fold_arr k ac ar =
      let (ac1, lst) =
        List.fold_left
          (fun (ac,l) x -> let (ac',x') = hlp k ac x in (ac',x'::l))
          (ac, [])
          (Array.to_list ar)
      in
      (ac1, Array.of_list (List.rev lst))
    in
    match kind t with
    | Rel _ | Meta _ | Var _ | Sort _ | Const _ | Ind _ | Construct _ ->
       f m acc t
    | Cast (ty1,ck,ty2) ->
       let (acc1, ty1') = hlp m acc ty1 in
       let (acc2, ty2') = hlp m acc1 ty2 in
       f m acc2 (mkCast(ty1',ck,ty2'))
    | Prod (na,ty,c)    ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, c') = hlp (m+1) acc1 c in
       f m acc2 (mkProd(na,ty',c'))
    | Lambda (na,ty,c)  ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, c') = hlp (m+1) acc1 c in
       f m acc2 (mkLambda(na,ty',c'))
    | LetIn (na,b,ty,c) ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, b') = hlp m acc1 b in
       let (acc3, c') = hlp (m+1) acc2 c in
       f m acc3 (mkLetIn(na,b',ty',c'))
    | App (a,args) ->
       let (acc1, a') = hlp m acc a in
       let (acc2, args') = fold_arr m acc1 args in
       f m acc2 (mkApp(a',args'))
    | Proj (p,c) ->
       let (acc1, c') = hlp m acc c in
       f m acc1 (mkProj(p,c'))
    | Evar (evk,cl) ->
       let (acc1, cl') = fold_arr m acc cl in
       f m acc1 (mkEvar(evk,cl'))
    | Case (ci,p,c,bl) ->
       let (acc1, p') = hlp m acc p in
       let (acc2, c') = hlp m acc1 c in
       let (acc3, bl') = fold_arr m acc2 bl in
       f m acc3 (mkCase(ci,p',c',bl'))
    | Fix (nvn,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let (acc1, typs') = fold_arr m acc typs in
       let (acc2, bodies') = fold_arr (m + Array.length typs) acc1 bodies in
       f m acc2 (mkFix(nvn,(fnames,typs',bodies')))
    | CoFix (n,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let (acc1, typs') = fold_arr m acc typs in
       let (acc2, bodies') = fold_arr (m + Array.length typs) acc1 bodies in
       f m acc2 (mkCoFix(n,(fnames,typs',bodies')))
  in
  hlp 0 acc t

let map_constr_ker f x = snd (map_fold_constr_ker (fun m () t -> ((), f m t)) () x)

let fold_constr_ker f acc x = fst (map_fold_constr_ker (fun m acc t -> (f m acc t, t)) acc x)

(***************************************************************************************)

let is_coinductive (ind : inductive) =
  let mind = fst (Inductive.lookup_mind_specif (Global.env ()) ind) in
  let open Declarations in
  match mind.mind_finite with
  | CoFinite -> true
  | _ -> false

let is_like f (ind : inductive) =
  let mind = fst (Inductive.lookup_mind_specif (Global.env ()) ind) in
  let open Declarations in
  if mind.mind_ntypes <> 1 then
    false
  else
    let body = mind.mind_packets.(0) in
    if Array.length body.mind_user_lc <> 1 then
      false
    else
      f (mind.mind_nparams) (body.mind_user_lc.(0))

let is_and_like =
  is_like begin fun p t ->
    let open Constr in
    let rec drop_params n t cont =
      if n = 0 then
        cont t
      else
        match kind t with
        | Prod(na, ty, b) -> drop_params (n - 1) b cont
        | _ -> false
    in
    let rec hlp n t =
      match kind t with
      | Prod(na, ty, b) ->
         begin
           match kind ty with
           | Rel k when k = p -> hlp (n + 1) b
           | _ -> false
         end
      | App (r, args) ->
         begin
           match kind r with
           | Rel k when k = n + p + 1 ->
              List.filter begin fun x ->
                match kind x with
                | Rel k when k <= n + p && k > n -> false
                | _ -> true
              end (Array.to_list args)
              = []
           | _ -> false
         end
      | _ -> false
    in
    drop_params p t (hlp 0)
  end

let is_exists_like =
  is_like begin fun p t ->
    if p <> 2 then
      false
    else
      let open Constr in
      match kind t with
      | Prod(_, _, t) ->
         begin
           match kind t with
           | Prod(_, _, t) ->
              begin
                match kind t with
                | Prod(_, r, t) ->
                   begin
                     match kind r with
                     | Rel 2 ->
                        begin
                          match kind t with
                          | Prod(_, app, t) ->
                             begin
                               match kind app with
                               | App(r, args) ->
                                  begin
                                    match args with
                                    | [| a |] ->
                                       begin
                                         match (kind r, kind a) with
                                         | (Rel 2, Rel 1) ->
                                            begin
                                              match kind t with
                                              | App(r, _) ->
                                                 begin
                                                   match kind r with
                                                   | Rel 5 -> true
                                                   | _ -> false
                                                 end
                                              | _ -> false
                                            end
                                         | _ -> false
                                       end
                                    | _ -> false
                                  end
                               | _ -> false
                             end
                          | _ -> false
                        end
                     | _ -> false
                   end
                | _ -> false
              end
           | _ -> false
         end
      |  _ -> false
  end

let get_inductive_typeargs evd (ind : inductive) =
  let open Constr in
  let open EConstr in
  let rec hlp acc t =
    match kind evd t with
    | Prod(x, ty, b) -> hlp ((x,ty) :: acc) b
    | _ -> List.rev acc
  in
  let env = Global.env () in
  let minds = Inductive.lookup_mind_specif env ind in
  let tp = Inductive.type_of_inductive env (Univ.in_punivs minds) in
  hlp [] (EConstr.of_constr tp)

(***************************************************************************************)

(* The following contains code from https://github.com/CoqHott/exceptional-tt. *)

let detype_param =
  function
  | LocalAssum (Name id, p) -> id, LocalAssumEntry p
  | LocalDef (Name id, p,_) -> id, LocalDefEntry p
  | _ -> anomaly (Pp.str "Unnamed inductive local variable.")

(* Replace

     Var(y1)..Var(yq):C1..Cq |- Ij:Bj
     Var(y1)..Var(yq):C1..Cq; I1..Ip:B1..Bp |- ci : Ti

   by

     |- Ij: (y1..yq:C1..Cq)Bj
     I1..Ip:(B1 y1..yq)..(Bp y1..yq) |- ci : (y1..yq:C1..Cq)Ti[Ij:=(Ij y1..yq)]
*)

let abstract_inductive nparams inds =
(* To be sure to be the same as before, should probably be moved to process_inductive *)
  let params' = let (_,arity,_,_,_) = List.hd inds in
                let (params,_) = decompose_prod_n_assum nparams arity in
                List.map detype_param params
  in
  let ind'' =
  List.map
    (fun (a,arity,template,c,lc) ->
      let _, short_arity = decompose_prod_n_assum nparams arity in
      let shortlc =
        List.map (fun c -> snd (decompose_prod_n_assum nparams c)) lc in
      { mind_entry_typename = a;
        mind_entry_arity = short_arity;
        mind_entry_template = template;
        mind_entry_consnames = c;
        mind_entry_lc = shortlc })
    inds
  in (params',ind'')

let refresh_polymorphic_type_of_inductive (_,mip) =
  match mip.mind_arity with
  | RegularArity s -> s.mind_user_arity, false
  | TemplateArity ar ->
    let ctx = List.rev mip.mind_arity_ctxt in
      mkArity (List.rev ctx, Type ar.template_level), true

let process_inductive mib =
  let nparams = Context.Rel.length mib.mind_params_ctxt in
  let ind_univs = match mib.mind_universes with
  | Monomorphic_ind ctx -> Monomorphic_ind_entry ctx
  | Polymorphic_ind auctx ->
    let uctx = Univ.AUContext.repr auctx in
    Polymorphic_ind_entry uctx
  | Cumulative_ind cumi ->
    let auctx = Univ.ACumulativityInfo.univ_context cumi in
    let uctx = Univ.AUContext.repr auctx in
    Cumulative_ind_entry (Univ.CumulativityInfo.from_universe_context uctx)
  in
  let map mip =
    let arity, template = refresh_polymorphic_type_of_inductive (mib,mip) in
    (mip.mind_typename,
      arity, template,
      Array.to_list mip.mind_consnames,
      Array.to_list mip.mind_user_lc)
  in
  let inds = Array.map_to_list map mib.mind_packets in
  let (params', inds') = abstract_inductive nparams inds in
  let record = match mib.mind_record with
    | PrimRecord arr -> Some (Some (Array.map (fun (id, _, _) -> id) arr))
    | FakeRecord -> Some None
    | NotRecord -> None
  in
  { mind_entry_record = record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params';
    mind_entry_inds = inds';
    mind_entry_private = mib.mind_private;
    mind_entry_universes = ind_univs
  }

(* The following contains code from https://github.com/ybertot/plugin_tutorials *)

let edeclare ident (_, poly, _ as k) ~opaque env evd udecl body tyopt imps hook =
  let sigma = Evd.minimize_universes evd in
  let body = EConstr.to_constr sigma body in
  let tyopt = Option.map (EConstr.to_constr sigma) tyopt in
  let uvars_fold uvars c =
    Univ.LSet.union uvars (Univops.universes_of_constr c) in
  let uvars = List.fold_left uvars_fold Univ.LSet.empty
     (Option.List.cons tyopt [body]) in
  let sigma = Evd.restrict_universe_context sigma uvars in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  let ubinders = Evd.universe_binders sigma in
  let ce = Declare.definition_entry ?types:tyopt ~univs body in
  DeclareDef.declare_definition ident k ce ubinders imps hook

let declare_definition ident ?(opaque = false) evd body =
  let env = Global.env () in
  let (evd, body) = Typing.solve_evars env evd body in
  let k = (Decl_kinds.Global,
           Flags.is_universe_polymorphism (), Decl_kinds.Definition) in
  let udecl = UState.default_univ_decl in
  let nohook = Lemmas.mk_hook (fun _ x -> x) in
  ignore (edeclare ident k ~opaque:opaque env evd udecl body None [] nohook)
