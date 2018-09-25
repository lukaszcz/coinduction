(* This file contains some code from https://github.com/CoqHott/exceptional-tt. *)

open Util
open CErrors
open Context
open Rel.Declaration
open Names
open Term
open EConstr
open Declarations
open Entries
open Environ
open Term

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
    | Some (Some (id, _, _)) -> Some (Some id)
    | Some None -> Some None
    | None -> None
  in
  { mind_entry_record = record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params';
    mind_entry_inds = inds';
    mind_entry_private = mib.mind_private;
    mind_entry_universes = ind_univs
  }
