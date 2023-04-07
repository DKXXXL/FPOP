open Utils
open Familytype

(* This file is responsible for the Environment related data structure *)


(* This reference stores a stack of inheritance judgement
    the name indicating the name of the output family of the inheritance
*)
let inhcontentref = Summary.ref ~name:"InhContent" ([] : (name * inh) list)

let toplevel_inhdefs = Summary.ref ~name:"InhDefs" ([] : (name * inh) list )

(* Warning: 
  Top Level doesn't track the environment of the constructing family.
  This might cause some problems.
*)

(* TODO: make toplevel_famdefs into persistent storage. *)
let toplevel_famdefs = 
  Summary.ref 
  ~name:"FamilyDefs" 
  ([] : (name * ((family_term * family_type) typed)) list )

(* Invariance : len (! familyctxref) = len (! familycontentref)  *)



let ontopmember (l : 'a list) (f : 'a -> 'a) =
  match l with 
  | [] -> cerror ~einfo:"Unexpected Empty List." ()
  | h::t -> (f h) :: t

(* push to the top level family
    Assume current_has_open
*)


let current_has_open_judgement () : bool = 
  List.length (!inhcontentref) > 0
let assert_current_has_open_judgement () : unit = 
  assert_cerror ~einfo:"No open inh judgement" (fun _ ->current_has_open_judgement())




let ontopinh (f : 'a -> 'a) : unit =  
  assert_current_has_open_judgement();
  let topinh = pop inhcontentref in 
  push inhcontentref (f topinh)

(* TODO: Fix the binding for Field ... := ... . as well
    Just like the above   
*)
let only_support_one_name_term_type () = nonimplement ~moreinfo:__LOC__ () 

(* Return a map that maps from the parent family name to children family name
    for the current constructing   *)
let get_current_inh_name_mapping : (fam_name,fam_name) smap = 
  let all_inhs = !inhcontentref in 
  let all_names = 
    List.map (fun (x, ((((pname, _), (cname, _)) ,_), _)) -> (pname, cname)) all_inhs in 
  all_names
  

(* return the typed version of family type in the current ctx *)
let current_ctx_family_type_typed () : (name * (family_type typed)) list =
  let each_inh (fname, (((_, oup) , ctx), _)) = (fname,  (oup, ctx)) in 
  List.map each_inh (!inhcontentref)


(* Currently only supporting pointing to top level family  *)
let name_to_family_ref (fname : name) : family_ref =
  (* let current_ctx = current_ctx_family_type_typed () in  *)
  (match (List.assoc_opt fname (!toplevel_famdefs)) with
  | Some ((tm, ty), ctx) -> ToplevelRef (fname, ((tm, ty), ctx))
  | None -> cerror ~einfo:"Family Declaration Unfound." ())







let top_uninherited_field () : (name * (family_type_or_coq_type typed)) option = 
  (* Assume l1 >= l2*)
  let rec find_first_non_include (l1 : 'a list) (l2 : 'a list) : 'a option =
    match l1, l2 with
    | (h1::t1), (h2::t2) -> 
        (* TODO: *)
        (* assert_cerror ~einfo:"Unexpected Error -- list doesn't match" (h1 = h2); *)
        find_first_non_include t1 t2 
    | h1::t1, [] -> Some h1 
    | [], h2::t2 -> cerror ~einfo:"Unexpected Error - list 1 should be list 2's super set" ()
    | [], [] -> None in 
  let basis = peek inhbasestack in 
  (* Following we use 
        supf indicate the current family type of the basis
        subf indicating the current constructing family type
        i.e. we have constructed 
        Inh subf ?, targeting the input basis as supf
  *)
  let _, ( ((subf, _), ectx) , _ ) = peek inhcontentref in
  let supf, _ = get_family_ty_in_inhbase (fst subf) (basis, ectx) in  
  let subf, _ = unfold_typed_family_type (subf, ectx) in 
  let supf, _ = unfold_typed_family_type (supf, ectx) in 
  find_first_non_include (List.rev (snd supf)) (List.rev (snd subf))
let check_top_uninherited_field (expected : name) : unit =
  let fnamestr = Names.Id.to_string expected in 
      match top_uninherited_field() with
      | Some (fname2, _) -> assert_cerror ~einfo:(String.cat "The Current Inheriting Field is not " fnamestr) (fun _ ->fname2 = expected) 
      | _ -> cerror ~einfo:(String.cat "The Current Inheriting Field is not " fnamestr) () 



(* return the output ctx of the current judgement *)
let currentinh_output_ctx () : family_ctxtype =
  let result = 
  match !inhcontentref with 
  | [] -> FamCtx []
  | _ ->
    let fname, (((inp, oup) , FamCtx ctx), current_inh) = peek inhcontentref in 
    FamCtx ((fname, oup)::ctx) in 
  result

let check_field_non_exist_in_constructing_basis (fname : name) : unit =
    match !inhbasestack with 
    | _::_ ->
      (match peek inhbasestack with 
      | Nested {shifted = (current_basis, _); _} ->
      assert_cerror ~einfo:"Conflicting Name -- Name existent, Please use extend instead" 
                    (fun _ ->List.assoc_opt fname (snd current_basis) = None)
      | _ -> ())
    | [] -> ()

let current_family_name () : name option = 
  match !inhcontentref with 
  | [] -> None
  | _ ->
    let k, _ = peek inhcontentref in 
    Some k

    
(* check at the current situation, if all the field names are not mentioned in the current family and parent family *)
let if_fieldsname_totally_new (fname : name list) : bool =
  (* we get all the declared fields and fields to inherit
in the current family
    and check if fname in them *)
  let current_family_member : _ list = 
    match !inhcontentref with 
    | [] -> []
    | _ ->
      let _, (((_, (_, oup)) , _), _) = peek inhcontentref in 
      List.map fst oup in 
  let current_family_member = Set_Name.add_seq (List.to_seq current_family_member) Set_Name.empty in 
  let from_parent : _ list =
    match !inhbasestack with 
    | _::_ ->
      let (_, parent_famty), _ = get_family_ty_in_inhbase (dummy_famname) (peek inhbasestack, (currentinh_output_ctx ())) in 
      List.map fst parent_famty
    | [] -> [] in 
  let all_declared_fieldnames = Set_Name.add_seq (List.to_seq from_parent) current_family_member in 
  let to_query = Set_Name.add_seq (List.to_seq fname) Set_Name.empty in 
  (* we check if those to-added stuff has any intersection with all the declared stuff *)
  let if_no_intersection = 
    Set_Name.cardinal (Set_Name.inter all_declared_fieldnames to_query) = 0 in 
  if_no_intersection

let if_fieldname_totally_new (fname : name) : bool =
  if_fieldsname_totally_new [fname]

(* return true if the fname hasn't been defined in the current family *)
let if_fieldsname_not_defined_yet (fname : name) : bool = 
  let current_family_member : _ list = 
    match !inhcontentref with 
    | [] -> []
    | _ ->
      let _, (((_, (_, oup)) , _), _) = peek inhcontentref in 
      List.map fst oup in 
  let current_family_member = Set_Name.add_seq (List.to_seq current_family_member) Set_Name.empty in 
  not (Set_Name.mem fname current_family_member)

(* This will check if a given name exists already w.r.t. inheritance and etc
    if exists, then new field is not allowed in the same name and raise an exception
  *)
let if_allow_new_field (fname : name) : unit =
  let errormsg = (Names.Id.to_string fname)^( " has been declared already. ")^( __LOC__) in  
  assert_cerror_forced ~einfo:errormsg (fun _ -> if_fieldname_totally_new fname)

let if_allow_new_fields (fnames : name list) : unit =
  let errormsg = ( "Some names have been declared already. ")^( __LOC__) in  
  assert_cerror_forced ~einfo:errormsg (fun _ -> if_fieldsname_totally_new fnames)


let infer_fname_new_or_extend (fname : name) : [`New | `Extend] = 
  (* if fname is already implemented, then we signal error *)
  let fnamestr = Names.Id.to_string fname in 
  assert_cerror_forced ~einfo:(fnamestr ^" is already defined! "^__LOC__) 
  (fun _ -> if_fieldsname_not_defined_yet fname);

  (* otherwise, if it is in the parent, then we return `Extend *)
  (* otherwise we return `New *)
  if (if_fieldname_totally_new fname) then `New else `Extend
    
(* union d1 and d2, and duplicate key we choose from d1 *)
let shadow_union d1 d2: 'a Dict_Name.t = 
  Dict_Name.add_seq (Dict_Name.to_seq d1) d2
(* this will compute the directly accessible field
    i.e. those self__XX.[t] 
    [t] is directly accessible
  this function is helpful for removing self__ prefix
  we need multiple cache to make this function workable
  for each direct accessible term, we will return the self__XX it belongs to
    *)
let all_direct_accessible_field (targetctx : family_ctxtype)  : name Dict_Name.t = 
  (* both of the following functions are recursive
      so to cache them we need to write in open-rec style *)
  let open CCCache in 
  let direct_accessible_field_in_family = 
    let direct_accessible_field_in_family_ daff (famname : fam_name) ( f ) : name Dict_Name.t =
      let self_name = self_version_name (fst famname)  in 
      match f with 
      | [] -> Dict_Name.empty
      | (field_name, CoqIndTy {allnames; _}) :: tail -> 
        (* collect all the name and add them into the name dictionary *)
        List.fold_right (fun eachname d -> Dict_Name.add eachname self_name d) allnames (daff famname tail)
        
      | (field_name, _) :: tail -> Dict_Name.add field_name self_name (daff famname tail)  in  
    with_cache_rec (lru ~eq:(fun a b -> a == b) 64) direct_accessible_field_in_family_ in 
  let direct_accessible_field_in_ctx = 
    let direct_accessible_field_in_ctx_ dafc f  : name Dict_Name.t = 
      match f with 
      | [] -> Dict_Name.empty
      | (_, (fname, fty))::tail -> shadow_union (direct_accessible_field_in_family fname fty) (dafc (tail)) in 
    with_cache_rec (lru ~eq:(fun a b -> a == b) 16) direct_accessible_field_in_ctx_ in 
  match !inhcontentref with 
  | [] -> Dict_Name.empty
  | _ ->
    (* let fname, (((_, oup) , FamCtx ctx), _) = peek inhcontentref in 
    shadow_union (direct_accessible_field_in_family (fst oup) (snd oup)) (direct_accessible_field_in_ctx ctx) *)
    match targetctx with 
    | (FamCtx ctx) -> 
      direct_accessible_field_in_ctx ctx

    
      

(* given an rawterm, go through each identifier and attach self__ if possible
    definitely some ambiguity exists but *)
let attach_self_prefix ?(targetctx = (None : family_ctxtype option)) r =
  let open Constrexpr_ops in 
  let open Constrexpr in 
  let open Libnames in 
  let take_root_of_path (t : qualid) : Names.Id.t =
    fst (to_name_optionqualid t) in
  (* let replace_root_of_path (t : qualid) (nr : Names.Id.t) : qualid =
    let _, tail = to_name_qualid t in 
    _point_qualid_ nr tail in *)
  let targetctx = match targetctx with | None -> currentinh_output_ctx () | Some k -> k in
  let ctx_mapping = all_direct_accessible_field targetctx in 
  (* Copy and paste from repla replace_qualid_root *)
  (* let _ = 
    let open Pp in 
    Utils.msg_notice @@ (str "Current Environments : ") ++ (pr_list_name @@ List.map fst @@ List.of_seq @@ Dict_Name.to_seq ctx_mapping) 
  in  *)
  let rec replace_qualid_path dict r =
    match r with
    | { CAst.loc; v = CRef (qid,us) } as x when (not (qualid_is_ident qid))  ->
        (* rename the root *)
      (match Dict_Name.find_opt (take_root_of_path qid) dict with 
      | Some new_root -> 
          let newqid = _point_qualid_ new_root qid in 
            CAst.make (CRef (newqid, us))
      | None -> x
      )
    | { CAst.loc; CAst.v = CRef (qid,us) } as x when (qualid_is_ident qid)  ->
        (* rename the var *)
      (match Dict_Name.find_opt (qualid_basename qid) dict with 
      | Some new_root -> 
          let newqid = _point_qualid_ new_root qid in 
          CAst.make (CRef (newqid, us))
      | None -> x
      )
      (* now it is capture-avoiding substitution *)
    | cn -> map_constr_expr_with_binders (fun n dict ->  Dict_Name.remove n dict) replace_qualid_path dict cn in 
  replace_qualid_path ctx_mapping r

let attach_self_prefix_qualid ?(targetctx = (None : family_ctxtype option)) (q : fieldpath) : fieldpath = 
  let open Libnames in 
  let take_root_of_path (t : qualid) : Names.Id.t =
    fst (to_name_optionqualid t) in
  let targetctx = match targetctx with | None -> currentinh_output_ctx () | Some k -> k in
  (* let replace_root_of_path (t : qualid) (nr : Names.Id.t) : qualid =
    let _, tail = to_name_qualid t in 
    _point_qualid_ nr tail in *)
  let ctx_mapping = all_direct_accessible_field targetctx in 
  match Dict_Name.find_opt  (take_root_of_path q) ctx_mapping with 
  | None -> q 
  | Some new_root -> _point_qualid_ new_root q 


(* we go through all the rawterm inside a signature, and add prefix properly *)
let attach_self_prefix_coqindsig (q : CoqIndSigUtil.coq_ind_sig) : CoqIndSigUtil.coq_ind_sig = 
  let attach_self_prefix_coqindsig ((u, paramty, tyty, cstrty) : Vernacexpr.inductive_expr) : Vernacexpr.inductive_expr = 
    (* TODO: also take care of paramty later *)
    let tyty = Option.map attach_self_prefix tyty in 
    let cstrty = 
      match cstrty with 
      | Vernacexpr.Constructors l -> Vernacexpr.Constructors (List.map (fun (h, (a, c)) -> (h, (a, attach_self_prefix c))) l) 
      | _ -> nonimplement ~moreinfo:("Not Supporting Record Type yet "^__LOC__) () in 
    (u, paramty, tyty, cstrty)
  in 
  List.map (fun (a,b) -> (attach_self_prefix_coqindsig a, b)) q


type plugin_command_scope_kind = 
  FRecursion | FInduction 
  | OpenedFamily | OpenedFieldClaim 
  | OpenedMetadata
type plugin_command_scope = plugin_command_scope_kind * name * (unit -> unit)
(* the third term is a function responsible for closing, thus called closing handler  *)
let plugin_command_scopes = Summary.ref ~name:"PluginCommandScope" ([] : plugin_command_scope list)


let peek_scope () : plugin_command_scope option =
  match !plugin_command_scopes with
  | [] -> None 
  | h :: _ -> Some h 


(* adding the top with scope information (i.e. add another scope) *)
(* Note that, only OpenedFamily allows nesting, so *)
let push_scope (p : plugin_command_scope) =
  let _ = 
    (* nesting checking -- we only allow OpenedFamily to be nested *)
    match peek_scope () with 
    | None | Some (OpenedFamily, _, _) -> () 
    | _ -> cerror ~einfo:("Not allow nesting except in Family. Please Close the last scope first.") ()
  in 
  plugin_command_scopes := (p :: (!plugin_command_scopes));
  let _ = 
    let open Pp in 
    Utils.msg_notice @@ (str "Current Scope :") ++ pr_list_name (List.map (fun (_, n, _) -> n) (!plugin_command_scopes))
  in ()



(* if use_closing_handler = true, then we will use the closing handler
   if verify_name is specified, then we verify the given name  *)
let pop_scope ?(use_closing_handler = true) verify_name () =
  match (!plugin_command_scopes) with 
  | [] -> cerror ~einfo:("Empty Scope! "^__LOC__) ()
  | (_,thename,closing_handler)::tail ->
    begin
    let real_name = Names.Id.to_string thename in 
    assert_cerror_forced ~einfo:("Incorrect Scope Name, the last scope is  "^real_name^"  "^__LOC__) (fun _ -> verify_name = thename);
    if use_closing_handler then closing_handler () else ();
    plugin_command_scopes := tail;
    let _ = 
      let open Pp in 
      Utils.msg_notice @@ (str "Current Scope :") ++ pr_list_name (List.map (fun (_, n, _) -> n) (!plugin_command_scopes))
    in  ()
    end



let assert_in_scope_family () =
  assert_cerror_forced ~einfo:"We can only Nest Stuff in Family!" 
  (fun _ -> 
    match peek_scope () with 
    | Some (OpenedFamily, _, _) -> true 
    | _ -> false
    )

let pr_scope_kind (k : plugin_command_scope_kind) : string =
  match k with 
  | FRecursion -> "FRecursion"
  | FInduction -> "FInduction"
  | OpenedFamily -> "OpenedFamily"
  | OpenedFieldClaim -> "OpenedFieldClaim"
  | OpenedMetadata -> "OpenedMetadata"


let assert_in_scope f = 
  assert_cerror_forced ~einfo:("Currently not in appropriate scope. It should be in "^(pr_scope_kind f)^" "^__LOC__) 
  (fun _ -> 
    match peek_scope () with 
    | Some (k, _, _) -> f = k 
    | _ -> false
    )

let assert_in_empty_scope () = 
  assert_cerror_forced ~einfo:("Currently should not be in any scope "^__LOC__) 
  (fun _ -> !plugin_command_scopes = [])