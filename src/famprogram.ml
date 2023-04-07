(* The chaotic part that handling the interaction
    mainly inheritance judgement interaction, adding most fields happens here   
    also meta-data is here
*)
open Fenv
open Familytype
open Ftheorem
open Utils
open Ltac_plugin
open FamTyID
open CoqIndSigUtil
open Finh









(* TODO : refactoring the guarding code to here *)
let only_support_one_ind_no_binder (inddef : coq_ind_sig) : unit = 
  assert_cerror ~einfo:"FRecursor doesn't support mutual inductive type yet" (fun _ ->List.length inddef = 1);
  let s = fst (List.hd inddef) in 
  let (indtypename, ind_params, indtype, cstrlist) = s in 
  assert_cerror ~einfo:"FLemma doesn't support Inductive Parameter yet" (fun _ ->fst ind_params = [] && snd ind_params = None)


let add_ind_defs (e : coq_ind_sig)  : unit =
  assert_current_has_open_judgement();
  only_support_one_ind_no_binder e;
  let allname = extract_all_ident [e] in
  if_allow_new_fields allname;
  let indgroupname = List.hd allname in 
  (* TODO: extract all the name, and check name conflict *)
  (* check_field_non_exist_in_constructing_basis i; *)
  let current_ctx = currentinh_output_ctx() in 
  (* We do type checking by tranpiling to Coq  *)
  let _ = inductive_to_famtype ([e], current_ctx) in 
  let _ = inductive_to_famterm_and_recursor_type ([e], current_ctx) in 
  (* let typ = 
    CoqVernacUtils.runVernac @@
    match eT with 
    | None -> extract_modtype embedt 
    | Some rawty -> embed_ty i rawty current_ctx in  *)
    ontopinh
    (fun (name, current_inh) ->
      (name, inhnewind current_inh indgroupname (e, current_ctx)))





(* This command will check if  
    Currently we have this postfix parameter 
      for indicating which eliminator to use
    Check Indrec.mli for helper function
  *)
(* TODO : directly use Coq's Scheme command instead of error-pronely calling _rect *)
let add_recursor (fname : name) 
    (rec_mod : Libnames.qualid) 
    (motive : rawterm) 
    (indtype : Libnames.qualid) 
    (postfix : name) = 
  assert_current_has_open_judgement();
  if_allow_new_field fname;
  let current_ctx = currentinh_output_ctx() in 
  let postfix = Names.Id.to_string postfix in
  let parameters = famctx_to_parameters_selfprefix current_ctx in
  let _ = 
    let _, basename = to_qualid_name rec_mod in 
    let basename = Names.Id.to_string basename in 
    assert_cerror_forced ~einfo:"Recursor Module must be named ending with `cases`, `handler`, or `internal`" 
    (fun _ -> is_rec_handler basename)
  in
  (* Construct typed motive *)
  let motive : coqterm = 
    let open CoqVernacUtils in 
    ModTerm (runVernac @@
    define_module (freshen_name ~prefix:(Nameops.add_prefix "__motive_of_" fname) ()) parameters 
    (fun ctx ->
      define_term (Nameops.add_prefix "__motiveT" fname) motive
      ))
  in 
  ontopinh
  (fun (name, current_inh) ->
    (name, inhnewrec current_inh fname current_ctx (rec_mod, current_ctx) (motive, current_ctx) (indtype, current_ctx) postfix) )




(* Now closing fact has a concrete semantic
    it is 
    1. exposing every former overridable definition (pins everything)
    2. has a default proof script
*)

let asserting_closing_fact (fname : name) (axiomty : rawterm) (proof : rawterm_or_tactics) = 
  assert_current_has_open_judgement();
  if_allow_new_field fname;
  let current_ctx = currentinh_output_ctx() in 
  let embedaxiomty =
    let open CoqVernacUtils in
    let parameters = famctx_to_parameters_selfprefix current_ctx in 
    runVernac @@
    define_module (freshen_name ~prefix:fname ()) parameters 
    (fun ctx ->
      assume_parameter fname axiomty ) in 
  let embedaxiomtm_tydec =
    let open CoqVernacUtils in
    let parameters = famctx_to_parameters_selfprefix current_ctx in 
    runVernac @@
    define_module (freshen_name ~prefix:fname ()) parameters 
    (fun ctx ->
      define_term (Nameops.add_suffix fname "__type") axiomty) in
  let _ = 
    (* do type checking, at least at this point *)
    (* but doing so, but currently the closing fact doesn't expose information under all_expose *)
    (* TODO: Support for closing fact as well *)
    let ov_exposed = Some (PinsEverything) in 
    CoqVernacUtils.runVernac (embed_rawterm_or_proof fname axiomty proof ~ov_exposed current_ctx) in
  let typed_embedaxiomty = (ModType embedaxiomty) in 
  let typed_embedaxiomtm_tydec = (ModTerm embedaxiomtm_tydec) in 
  let newinhop =  (CInhNewAxiom proof ) in 
  let newoupty = (ClosingFactTy {ty = typed_embedaxiomty; tytm = typed_embedaxiomtm_tydec}),current_ctx in 
  ontopinh
    (fun (name, current_inh) ->
      (name, inhnew current_inh fname ~newinhop ~newoupty 
      ));  ()


(* The following asserting version is  *)
(* let asserting_closing_fact (fname : name) (axiomty : rawterm) (proof : rawterm_or_tactics) = 
  assert_current_has_open_judgement();
  check_field_non_exist_in_constructing_basis fname;
  let current_ctx = currentinh_output_ctx() in 
  let open CoqVernacUtils in 
  let embedaxiomty =
    runVernac @@ embed_ty fname axiomty current_ctx in 
  let embedt = 
    let ov_exposed = Some (PinsEverything) in 
    CoqVernacUtils.runVernac (embed_rawterm_or_proof fname axiomty proof ~ov_exposed current_ctx) in
  let typ = embedaxiomty
  in
  let tytm = 
    ModTerm (CoqVernacUtils.runVernac @@
    embed_tterm fname axiomty current_ctx), fname in 
  let typ = 
    let dependencies = (PinsEverything, current_ctx) in 
    OvCoqTyWithTerm {tm = ModType embedt ; ty = ModType typ ; dependencies; isopaque = false; default_retry = Some proof; tytm} in 
    (* if overridable then CoqTy (ModType typ) else CoqTyWithTerm {tm = ModType embedt ; ty = ModType typ}  *)
  let newinhop = CInhNew (ModTerm embedt, current_ctx) in 
  let newoupty = typ, current_ctx in 
  ontopinh
    (fun (name, current_inh) ->
      (name, inhnew current_inh fname ~newinhop ~newoupty));  () *)



(* TODO:
  Implement MetaData
      MetaData is a new kind of family_type_or_coq_type and family_term_or_coq_term
      What it will do is when
      ```
      FMetaData {
        [Anything here]
      } 
      ```
      [Anything here] will be type-checked in the current family context
            (i.e. by interpreting them inside the module)
            then this metadata will be part of family type and family term
      Implementation is easy -- in VERNAC, we use parsing rule
      "FMetaData" "{" gallina_ext "}"
      and then directly use the 
  The application is to introduce
  ```
  FMetaData {
    Ltac .... := ... 
  }
  ```
  so that the user can use tactic/definition from family-type.
*)


(* TODO: 
    implementing injection and discriminate for our datatype,
    the idea is to use partial recursor again, 
    intuitively we "expand" the first level
    For example, 
      FInductive T := 
        | a : (A -> T) 
        | b : (B -> T -> T) 
        | c : (C -> T)
          will be unfolded into (A + (B x T) + C)
    concretely, since the partial recursor is
        prec : 
        (P : Type) 
        -> (A -> P) -> (B -> T -> P -> P) -> (C -> P)
    we instantiate P := (A + (B x T) + C), and then
      define function Df := prec P (fun a => left a) (fun b t _ => right (left (b, t))) ... 
    by computation rule of prec, injection and discriminate are both easy --
    to prove 
      c x = c y -> Df (c x) = Df (c y) 
      -> right (right x) = right (right y) 
      -> use injection from the original coq because here sum and product type
          are both vanilla inductive type
      -> x = y 
    similar for discriminate
      c x = a y -> Df (c x) = Df (a y) 
      -> right right x = left y 
      -> use discriminate from the original coq
      -> False

*)

let opened_metadata_seg =  Summary.ref ~name:"MetaDataName" (None : ((name * name) option))
(* modname * fname *)
let open_meta_data_section (prefix : name) = 
  assert_current_has_open_judgement();
  assert_cerror_forced ~einfo:"Please Close Last MetaData" (fun () -> !opened_metadata_seg = None);
  assert_cerror_forced ~einfo:"Please close last claim" (fun () -> !claim_goal_info = None);
  let newname = freshen_name ~prefix () in 
  opened_metadata_seg := Some (newname, prefix);
  let parameters_with_self = famctx_to_parameters_selfprefix (currentinh_output_ctx ()) in 
  let parameters_ = 
    List.map 
      (fun (n,m) -> 
        (None, [CAst.make n], (m, Declaremods.DefaultInline))) parameters_with_self in 
  CAst.make newname, parameters_

let close_meta_data_section () =
  let modname, fname = 
    match !opened_metadata_seg with 
    | Some (modname, fname) -> modname, fname
    | None -> cerror ~einfo:"Not in any MetaData section!" () in 
  let _ = 
    let open CoqVernacUtils in 
    runVernac @@ 
    vernac_ (Vernacexpr.VernacEndSegment (CAst.make modname)) in 
  let current_ctx = currentinh_output_ctx () in
  let metadata = Libnames.qualid_of_ident modname in 
  let newinhop = CInhNew ((ModTerm metadata), current_ctx) in 
  let newoupty = MetaDataTy (ModType metadata), current_ctx in 
  ontopinh
    (fun (name, current_inh) ->
      (name, inhnew current_inh fname ~newinhop ~newoupty));
  opened_metadata_seg := None

let add_meta_data_section (t : coqterm typed) =
  let ModTerm metadata = fst t in  
  let fname = freshen_name ~prefix:(Libnames.qualid_basename metadata) () in  
  let current_ctx = currentinh_output_ctx () in
  (* let metadata = Libnames.qualid_of_ident modname in  *)
  let newinhop = CInhNew ((ModTerm metadata), current_ctx) in 
  let newoupty = MetaDataTy (ModType metadata), current_ctx in 
  ontopinh
    (fun (name, current_inh) ->
      (name, inhnew current_inh fname ~newinhop ~newoupty));
  opened_metadata_seg := None


(* Close the current constructing judgement 
    1. we will check current has an open constructing judgement
    2. check the basis for the current constructing judgement 
        a.  is exactly the input part of the current constructing judgement
        b.  is also exactly the one the earlier basis wanted (this should be ensured during 
                basis construction)
    3. stuff it into the earlier inheritance judgement, 
    4. (also we don't maintain context information anymore)
*)
let close_current_inh_judgement ?(is_sealing = false) () : unit =
  assert_current_has_open_judgement();
  let (currentname, current_inh) = peek inhcontentref in 
  let (((current_basis, _), _), inh_struct) = current_inh in
  match peek inhbasestack with 
  | NonNested (_, (ov_exposed, _)) -> 
    ();
    (* we are constructing inhnewfam *)
    assert_cerror ~einfo:"Expecting Inh Judgement with empty input." (fun _ ->(snd current_basis) = []);
    assert_cerror ~einfo:"Expect Empty inhbasestack" (fun _ ->List.length !inhbasestack > 1);
    let (_, current_inh) = pop inhcontentref in  
    let _ = pop inhbasestack in 
      ontopinh 
        (fun (parentnanme, parent_inh) ->
          (parentnanme, inhnewfam parent_inh currentname ~is_sealing ~ov_exposed current_inh))  
  
  | Nested {orig = orgbasis; shifted = (expected_basis, _); ov_exposed=(ov_exposed, _)} ->
      (* we are constructing inhextendinh *)
      assert_cerror ~einfo:"Currently Nested Extension doesn't allow " (fun _ -> not is_sealing);
      assert_cerror ~einfo:"Unfinished Inh Judgement." (fun _ ->current_basis = expected_basis);
      assert_cerror ~einfo:"Expect Non-Empty inhbasestack" (fun _ ->List.length !inhbasestack > 1);

      (* TODO : Check 2.b *)
      let (_, current_inh) = pop inhcontentref in  
      let _ = pop inhbasestack in      
        ontopinh 
            (fun (parentnanme, parent_inh) ->
              (parentnanme, inhextendinh parent_inh currentname orgbasis ~ov_exposed current_inh))
  | InitialInhBase fam ->
    ();
    (* we are constructing inhnewfam *)
    (* assert_cerror ~einfo:"Expecting Inh Judgement with empty input." (current_basis = []); *)
    assert_cerror ~einfo:"Expect Empty inhbasestack" (fun _ ->List.length !inhbasestack = 1);
    let (currentname, current_inh) = pop inhcontentref in  
    let ((_, outfamtype),ctx),_ = current_inh in 
    let _ = pop inhbasestack in 
      push toplevel_inhdefs (currentname, current_inh);
    (* Now List.length (! inhcontentref) = 0 
        and we need to push the inh into a top level family
    *)
    let staged_family, sfctx = inh_apply_famref current_inh fam in 
      (match staged_family with 
      | FamTm (ft) ->  
          let FamCtx sfctx_ = sfctx in 
          let _ = assert_cerror ~einfo:"Family Should Standalone" (fun _ ->List.length sfctx_ = 0) in
          let generated_mod = standalone_famterm_to_mod (ft, sfctx) in 
          let open CoqVernacUtils in 
          let _ = runVernac @@ 
            define_module currentname []
            (fun _ -> include_mod (pure generated_mod)) in
            (* let_mod currentname (pure generated_mod) in  *)
          (* TODO: let toplevel_famdefs also record translated module *)
          push toplevel_famdefs (currentname, ( (ft, outfamtype) ,sfctx));
          ()
      | _ -> cerror ~einfo:"Expect Standalone Family" ())
  | InitialOnMixedInh (i, parentfam, famname) -> 
    ();
    (* we are constructing inhnewfam *)
    (* assert_cerror ~einfo:"Expecting Inh Judgement with empty input." (current_basis = []); *)
    assert_cerror ~einfo:"Expect Empty inhbasestack" (fun _ ->List.length !inhbasestack = 1);
    let (currentname, current_inh) = pop inhcontentref in 
    let completed_inh = InhMixin.inh_direct_compose famname i current_inh in 
    (* Now List.length (! inhcontentref) = 0 
        before we push the current inh, we need to direct compose
        current_inh with the inhertiance in the basestack, i.e. the i
    *) 
    let ((_, outfamtype),ctx),_ = completed_inh in 
    let _ = pop inhbasestack in 
      push toplevel_inhdefs (currentname, completed_inh);

    let staged_family, sfctx = inh_apply_famref completed_inh (Some parentfam) in 
      (match staged_family with 
      | FamTm (ft) ->  
          let FamCtx sfctx_ = sfctx in 
          let _ = assert_cerror ~einfo:"Family Should Standalone" (fun _ ->List.length sfctx_ = 0) in
          let generated_mod = standalone_famterm_to_mod (ft, sfctx) in 
          let open CoqVernacUtils in 
          let _ = runVernac @@ 
            define_module currentname []
            (fun _ -> include_mod (pure generated_mod)) in
            (* let_mod currentname (pure generated_mod) in  *)
          (* TODO: let toplevel_famdefs also record translated module *)
          push toplevel_famdefs (currentname, ( (ft, outfamtype) ,sfctx));
          ()
      | _ -> cerror ~einfo:"Expect Standalone Family" ())
  | OverrideBase {orig = orgbasis; expected_final; _} ->
    assert_cerror ~einfo:"Expecting Inh Judgement with empty input." (fun _ ->(snd current_basis) = []);
    assert_cerror ~einfo:"Expect Empty inhbasestack" (fun _ ->List.length !inhbasestack > 1);
    let (_, current_inh) = pop inhcontentref in  
    let _ = pop inhbasestack in 
      ontopinh 
        (fun (parentnanme, parent_inh) ->
          (parentnanme, inhoverridefam parent_inh currentname current_inh orgbasis (fst expected_final) ))  

  

  (* Finally we construct standalone families from inh *)
  

  (* then we remove the top of the family ctx *)
  (* and then we *)


  
(* This one is for extending a family field of a given input family type *)
let extend_new_nested_inhjudgement (fname: name) : unit =
  assert_current_has_open_judgement();
  if_allow_extend_field fname;
  check_top_uninherited_field (fname);
    let (current_basis, cbctx) = 
      match peek inhbasestack with 
      | Nested {shifted = (current_basis, cbctx); _} -> (current_basis, cbctx)
      | NonNested (Some fref, _) -> get_family_ty_in_famref fref 
      | NonNested (None, _) -> cerror ~einfo:"Nothing to extends!" ()
      | InitialOnMixedInh (i, _, _) ->     
        let (((_, outty), ctx) , _) = i in
        outty, ctx
      | InitialInhBase (Some fref) -> get_family_ty_in_famref fref
      | InitialInhBase None -> cerror ~einfo:"Nothing to extends!" ()
      | OverrideBase _ -> nonimplement ~moreinfo:__LOC__ () in
    let (current_basis, cbctx) = unfold_typed_family_type (current_basis, cbctx) in 
    let current_outctx = currentinh_output_ctx () in 
        assert_cerror ~einfo:"Non-existent Name -- Extend must apply to existent member" 
                    (fun _ ->List.assoc_opt fname (snd current_basis) <> None);
      let parentty, parentctx = smap_assoc ~einfo:__LOC__ fname (snd current_basis) in 
      (match parentty with 
      | FamTy (parent, ov_exposed) ->
          let lifted_parent = wkinh_family_type  (parent, parentctx) current_outctx in 
          let ov_exposed = wkinh_paths ov_exposed current_outctx in 
          push inhbasestack @@ Nested ({orig = (parent, parentctx); shifted = lifted_parent; ov_exposed} ) ;
          push inhcontentref (fname, (empty_inh (fst current_basis) (fst current_basis) (currentinh_output_ctx ())))
      | _ -> cerror ~einfo:"Non Extensible Field -- Expecting a Family" ()
          )

(* This function is deprecated.
   We will not do more maintainence about it. *)
let override_nested_inhjudgement (fname: name) : unit =
  (* nonimplement ~moreinfo:("Deprecated. "^__LOC__) (); *)
  assert_current_has_open_judgement();
  if_allow_extend_field fname;
  check_top_uninherited_field (fname);
    let (current_basis, cbctx) = 
      match peek inhbasestack with 
      | Nested {shifted = (current_basis, cbctx); _} -> (current_basis, cbctx)
      | NonNested (Some fref, _) -> get_family_ty_in_famref fref 
      | InitialInhBase (Some fref) -> get_family_ty_in_famref fref
      | _ -> cerror ~einfo:"Non-existent Name -- Extend must apply to existent member" () in

    let (current_basis, cbctx) = unfold_typed_family_type (current_basis, cbctx) in 
    let current_outctx = currentinh_output_ctx () in 
        assert_cerror ~einfo:"Non-existent Name -- Extend must apply to existent member" 
                    (fun _ ->List.assoc_opt fname (snd current_basis) <> None);
      let parentty, parentctx = smap_assoc ~einfo:__LOC__ fname (snd current_basis) in
      (match parentty with 
      | SealedFamTy {sealed; _} ->
          let lifted_sealed = wkinh_family_type (sealed, parentctx) current_outctx in 
          push inhbasestack @@ OverrideBase {orig = (sealed, parentctx); expected_final = lifted_sealed} ;
          push inhcontentref (fname, (empty_inh (fst current_basis) (fst current_basis) (currentinh_output_ctx ())))
      | _ -> cerror ~einfo:"Non Sealed Family Cannot be overriden!" ()
          )

    
(* Add a brand new field and not possible to be inherited
    Since each field is dependent on the earlier stuff,
    we need to add a header, a varaible named as "self_" 
*)
let add_new_field (i : name) ?eT:(eT = None) (e : Constrexpr.constr_expr)  : unit =
  let eT : rawterm option = eT in
  assert_current_has_open_judgement();
  if_allow_new_field i;
  let current_ctx = currentinh_output_ctx() in 
  let embedt = CoqVernacUtils.runVernac (embed_tterm i ~eT e current_ctx) in
  (* let typ = 
      CoqVernacUtils.runVernac @@
      match eT with 
      | None -> extract_modtype embedt 
      | Some rawty -> embed_ty i rawty current_ctx 
  in *)
  let typ = CoqTyWithTerm {tm = ModType embedt} 
  in
  let newinhop = CInhNew (ModTerm embedt, current_ctx) in 
  let newoupty = typ, current_ctx in 
  ontopinh
    (fun (name, current_inh) ->
      (name, inhnew current_inh i ~newinhop ~newoupty));  ()

let fieldpath_add_prefix (prefix) (p : fieldpath) = 
  let f,r = to_name_optionqualid p in 
  let f = Nameops.add_prefix prefix f in 
  _point_optionqualid f r 

(* analyze the relative path of a given variable name *)
let name_analyze ?(predicate = fun _ -> true) (fname : name)  : fieldpath = 
  let current_inh = !inhcontentref in 
  let rec search f l = 
    match l with 
    | [] -> None 
    | h :: t -> match f h with | None -> search f t | Some res -> Some res  in 
  (* Very inefficient searching *)
  let name_search (fname : name) (i : inh_ty ) (current_path : fieldpath) : fieldpath option = 
    (* Following is the full/inefficient version *)
    (* match i with 
    | [] -> None 
    | (fname2, ty)::t when ((fname = fname2) && (predicate ty)) ->           
      Some (_qualid_point_ (Some current_path) fname)(* Found! *)
    | (fname2, (FamTy (_, nested))) :: t -> 
      let nested_new_path = (_qualid_point_ (Some current_path) fname) in 
        Option.bind (name_search fname nested nested_new_path) (fun _ -> name_search fname t current_path)
    | _ :: t -> name_search fname t current_path  *)
    (* TODO: make search more complete
        that includes 
        1. construct a cache/indexing from the inheritance structure to dictionary of name -> fieldpath
        2. reuse above indexing during construction *)
    (* Currently we only search for top level, don't search in the nested *)
    let dicti = dictionary_of_inh_ty i in 
    (* first search same level *)
    let iffound = Dict_Name.find_opt fname dicti in 
      match iffound with 
        | Some found when (predicate found) -> 
          Some (_qualid_point_ (Some current_path) fname)(* Found! *)
        | _ -> 
          (* Unfound, we try to find in deeper level *)
          None 

  in 
  let res = 
    search (fun (famname, (i, _)) -> name_search fname i (Libnames.qualid_of_ident famname)) current_inh
  in 
  match res with 
  | None -> cerror ~einfo:("Overridable Field Unfound! "^ (Names.Id.to_string fname)) ()
  | Some res -> res 


let overridable_names_analyze_to_paths (def_depend : name list) =
  let current_ctx = currentinh_output_ctx() in 
    let matching_overriding = 
      fun x ->
        match x with 
        | PRecTy _, _
        | (OvCoqTyWithTerm _), _ 
        | (CoqIndTy _), _ -> true 
        | _, _ -> false in 
    let dependencies =
      Set_Fieldpath.add_seq 
      (List.to_seq @@ 
      List.map (fun s -> fieldpath_add_prefix "self__" (name_analyze ~predicate:matching_overriding s)) def_depend) Set_Fieldpath.empty, current_ctx in 
  dependencies



(* open a new inheritance judgement to fill in 
      it is either used in 
        a. "Family ..." <- this case, parent = empty, name must be new
        b. "Extended Family ..." this case, parent = the basis from the current basis, name must be existent
    1. will set/stuck up the "basis" for inheritance judgement
    3. will alter the inhcontentref
    4. the inhjudgement will have ctx information
*)
let open_new_inhjudgement ?(bname : name option = None) ?(def_depend = []) (fname: name) : unit =
  assert_cerror ~einfo:"Conflicting duplicated Family name" 
                (fun _ ->List.assoc_opt fname !inhcontentref = None);
  if_allow_new_field fname;
  (* We need to handle alpha-equivalence *)
  let fname = (fname, newfid() ) in 
  let fref, basename = 
    match bname with 
    | None -> None, fname
    | Some bname -> 
    let (ToplevelRef (famname, ((ftm, fty), ctx) )) = name_to_family_ref bname in 
     (* let ref = 
        (ToplevelRef (famname, ((ftm, (family_type_rename fty fname)), ctx) )) in  *)
        let ref = 
          (ToplevelRef (famname, ((ftm, fty), ctx) )) in 
      Some ref, fst fty in 
  if (List.length (!inhbasestack) = 0)
  then (assert_cerror_forced ~einfo:"Top Level Family cannot pin." (fun _ -> def_depend = []);
        push inhbasestack (InitialInhBase fref))
  else 
    (
    let dependencies = overridable_names_analyze_to_paths def_depend in  
    push inhbasestack (NonNested (fref, dependencies))); 
  (* directly put the empty family, because it is a new judgement*)
  push inhcontentref ((fst fname), (empty_inh basename fname (currentinh_output_ctx ())))

  
(* Add a brand new overridable field
    specify the concrete definition that the current overridable field depends on
*)
let add_overridable_field (i : name) ?eT:(eT = None) ?(def_depend = ([] : name list)) (e : Constrexpr.constr_expr)  : unit =
  let eT : rawterm option = eT in
  assert_current_has_open_judgement();
  if_allow_new_field i;
  let current_ctx = currentinh_output_ctx() in 
  let dependencies = overridable_names_analyze_to_paths def_depend in  
  let embedt = 
    let ov_exposed = Some (Pins (fst dependencies)) in 
    CoqVernacUtils.runVernac (embed_tterm i ~eT e ~ov_exposed current_ctx) in
  let typ = 
      CoqVernacUtils.runVernac @@
      match eT with 
      | None -> extract_modtype embedt 
      | Some rawty -> embed_ty i rawty current_ctx 
  in
  let tytm = 
    ModTerm (CoqVernacUtils.runVernac @@
    match eT with 
    | None -> nonimplement ~moreinfo:__LOC__ ()
    | Some rawty -> embed_tterm i rawty current_ctx), i in 
  let typ = 
    let dependencies = (Pins (fst dependencies), (snd dependencies)) in 
    OvCoqTyWithTerm {tm = ModType embedt ; ty = ModType typ ; dependencies; isopaque = false; default_retry = Some (RawTerm e); tytm} in 
    (* if overridable then CoqTy (ModType typ) else CoqTyWithTerm {tm = ModType embedt ; ty = ModType typ}  *)
  let newinhop = CInhNew (ModTerm embedt, current_ctx) in 
  let newoupty = typ, current_ctx in 
  ontopinh
    (fun (name, current_inh) ->
      (name, inhnew current_inh i ~newinhop ~newoupty));  ()


(* override the current field *)
let override_current_field (fname : name) (e : rawterm) ?(new_dependency = (None : name list option)) (annotated_type : rawterm) : unit =
  assert_current_has_open_judgement();
  if_allow_extend_field fname;
  check_top_uninherited_field (fname);
  let current_ctx = currentinh_output_ctx () in
  let _ = peek inhbasestack in
  (match top_uninherited_field () with 
  | None -> ()
  | Some (fname , (OvCoqTyWithTerm _ , _)) -> 
    let open Pp in 
    Utils.msg_notice (str "(* Overriding ..." ++ (Names.Id.print fname) ++ str "*)")
  | Some (fname , _) ->
    (* let open Pp in   *)
    cerror ~einfo:( "Not an Overridable field! "^__LOC__) ()
  ); 
  match top_uninherited_field () with 
  | None -> cerror ~einfo:"Nothing To Override!" ()
    (* TOD: tytm can be used to do type-checking instead of the current annotated_type  *)
  | Some (fname, (OvCoqTyWithTerm {ty = inpty; tm=inptm; dependencies; isopaque; default_retry = inp_default_retry; tytm }, _)) ->
    Utils.msg_notice @@ pr_family_ctxtype (snd dependencies) ; 
    let new_dependencies = 
      match new_dependency with 
      | None -> wkinh_dependencies dependencies current_ctx  
      | Some aliases -> 
        ( let dependencies = overridable_names_analyze_to_paths aliases in 
          let dependencies = (Pins (fst dependencies), snd dependencies) in 
          dependencies) 
      in 
    let open Pp in
    Utils.msg_notice @@ (str "About ... ") ++ (Names.Id.print fname);
    (* let _ = Set_Fieldpath.map (fun p -> 
      Utils.msg_notice @@ (str "Dependencies  ") ++ (Libnames.pr_qualid p); 
      p
      ) (fst new_dependencies) in  *)
     
    let embedt = 
      let ov_exposed = Some (fst new_dependencies) in
      (* TODO: change to use embed_tm_using_embedded_tytm *)
      (* TODO: the equality between the overriding type and overriden type is not necessary
              because the important stuff is to make inheritance always work, then the above seems
                always happening *)
      (* here we assume annotated_type = previous overridden type = tytm *)
      CoqVernacUtils.runVernac (embed_tterm fname ~eT: (Some annotated_type) e ~ov_exposed current_ctx) in 
    let default_retry = Some (RawTerm e) in
      ontopinh 
      (fun (parentnanme, parent_inh) ->
        (* TODO: do type checking! i.e. do conversion checking between
           annotated_type and inpty *)
        (parentnanme, inhoverride parent_inh fname (ModTerm embedt, current_ctx) tytm ~inptm ~inpty ~dependencies ~new_dependencies ~isopaque ~inp_default_retry ~default_retry))
  | _ -> cerror ~einfo:"Only Support overriding Fields!" ()


(* This procedure is extending the top level ind type *)
let extend_ind_type (newdef : coq_ind_sig) : unit =
  (* This function will check if the top level 
      is a ind type and new definition can be compatible with the current one
    The requirement of compatibility is rather relaxed --
      we choose to make sure each new inductive type is already there in old inductive type
    *)
  let current_ctx = currentinh_output_ctx() in
  assert_current_has_open_judgement();
  let _ = 
    let type_name = List.hd @@ extract_type_ident [newdef] in 
    if_allow_extend_field type_name in

  let fname, parent_ind, oldctx,registered_prec = 
    match top_uninherited_field () with 
    | Some (fname, ((CoqIndTy ({indsigs_from_org_ctx = parent_ind, ctx; registered_prec; _}), _))) -> fname, parent_ind, ctx ,registered_prec
    | _ -> cerror ~einfo:__LOC__ () in 
  (* let complete_def = check_compatible_indsig_for_newcstrs (parent_ind, oldctx) (newdef, current_ctx) in 
  (* TODO: weaken the parent_ind signature as well, because it is typed in the oldctx *)
  (* Do type checking here *)
  let _ = inductive_to_famterm_and_recursor_type (complete_def :: parent_ind, current_ctx) in 
  let _ = inductive_to_famtype (complete_def :: parent_ind, current_ctx) in  *)
  ontopinh
  (fun (name, current_inh) ->
    (name, inhextendind_incrementally current_inh fname (parent_ind, oldctx) (newdef, current_ctx) !registered_prec))



let space_of_family_type () : (name * family_type) list =
  let registered_family_type =
    List.map (fun (x, ((y1, y2), z)) -> (x, y2)) !toplevel_famdefs in 
  let FamCtx inctx = currentinh_output_ctx  () in 
  List.append registered_family_type inctx
let pr_familytype_inctx (tm : name) : Pp.t = 
    let open Pp in 
    let all_ctx = space_of_family_type () in 
    let thefamily = 
      match List.assoc_opt tm all_ctx with
      | None -> CErrors.user_err (Pp.str "Unbound variable.")
      | Some res -> res in
      (Names.Id.print tm) ++ strbrk " : " ++ (pr_familytype thefamily)

let pr_familyterm_inctx (tm : name) : Pp.t = 
    let open List in 
    let allfamilies = map (fun (x,((y,z), h)) -> (x,(y,z))) !toplevel_famdefs  in
    let thefamily =   
      match assoc_opt tm allfamilies with
      | None -> CErrors.user_err (Pp.str "Unbound variable.")
      | Some (res, _) -> res in
      pr_familyterm tm thefamily


let printdefs (idname : Names.GlobRef.t) : unit =
  let open Names.GlobRef in
  match idname with 
  | ConstRef cst ->
  let cb = Global.lookup_constant cst in
    (match Global.body_of_constant_body Library.indirect_accessor cb with
    | None -> CErrors.user_err (Pp.str "UnBound")
    | Some(e, _, _) -> Utils.msg_notice @@ pr_constr e )
  | IndRef _ -> ()
  | _ -> CErrors.user_err (Pp.str "Only Support Constant Def yet")


(* doing top-level  *)
let inh_mixin newfname bname inhname1 inhname2 : unit =
  assert_cerror ~einfo:"Conflicting duplicated Family name" 
                (fun _ ->List.assoc_opt newfname !inhcontentref = None);
  let inh1 = smap_assoc ~einfo:__LOC__ inhname1 !toplevel_inhdefs in 
  let inh2 = smap_assoc ~einfo:__LOC__ inhname2 !toplevel_inhdefs in 
  let (bterm, _), bctx = smap_assoc ~einfo:__LOC__ bname !toplevel_famdefs in 
  let newfamname = (newfname, newfid() ) in 
  let open InhMixin in 
  (* let inhs = 
  match inhs with 
  | [] -> cerror ~einfo:__LOC__ ()
  | h::tail -> 
      extend_next_several (wrap h) tail in  *)
  let mixedinh = 
     (* first extend inh2's domain *)
    let (_, inh1_outputty), ctx = (fst inh1) in 
    let extended_inh2 = inh_extend_inputtype newfamname (inh1_outputty, ctx) inh2 in 
    inh_direct_compose newfamname inh1 extended_inh2
  in 
  let outputty = 
    let ((_, out), _), _ = mixedinh in  
    out
  in 
  (* Now we construct Inheritance judgement upon mixedinh *)
  (* let staged_family, sfctx = inh_Apply inhs (bterm, bctx) in *)
  let staged_family, sfctx = inh_apply mixedinh (bterm, bctx) in 
  let FamCtx sfctx_ = sfctx in 
  let _ = assert_cerror ~einfo:"Family Should Standalone" (fun _ ->List.length sfctx_ = 0) in
  let generated_mod = standalone_famterm_to_mod (staged_family, sfctx) in 
  let open CoqVernacUtils in 
  let _ = runVernac @@ 
    define_module newfname []
    (fun _ -> include_mod (pure generated_mod)) in
    (* let_mod currentname (pure generated_mod) in  *)
  (* TODO: let toplevel_famdefs also record translated module *)
  push toplevel_famdefs (newfname, ( (staged_family, outputty) ,sfctx));
  (* TODO: make inhs into  toplevel_inhdefs *)
  push toplevel_inhdefs (newfname, mixedinh);
  ()

(* complete a mixin of two inheritance 
      without this, a lot of mixin is not actually working, say

      Family A
      Inductive B
      f : B -> X
      End A

      Family C
      Inductive B
      End C

      After mixin, the f in A doesn't handle C.B well,
        so we need to give the user the ability to manually mixin two inheritance 
*)
let start_completing_mixin newfname bname inhname1 inhname2 : unit =
  (* we still get the mixin *)
  let inh1 = smap_assoc ~einfo:__LOC__ inhname1 !toplevel_inhdefs in 
  let inh2 = smap_assoc ~einfo:__LOC__ inhname2 !toplevel_inhdefs in 
  (* let (bterm, _), bctx = smap_assoc ~einfo:__LOC__ bname !toplevel_famdefs in  *)
  let newfamname = (newfname, newfid() ) in 
  let open InhMixin in 
  (* let inhs = 
  match inhs with 
  | [] -> cerror ~einfo:__LOC__ ()
  | h::tail -> 
      extend_next_several (wrap h) tail in  *)
  let mixedinh = 
     (* first extend inh2's domain *)
    let (_, inh1_outputty), ctx = (fst inh1) in 
    let extended_inh2 = inh_extend_inputtype ~postpone_recursor:true newfamname (inh1_outputty, ctx) inh2 in 
    inh_direct_compose newfamname inh1 extended_inh2
  in 
  assert_cerror ~einfo:"Conflicting duplicated Family name" 
                (fun _ ->List.assoc_opt newfname !inhcontentref = None);
  assert_cerror_forced ~einfo:"Mixin has to be at top level"
                (fun _ -> List.length (!inhbasestack) = 0);
  (* We need to handle alpha-equivalence *)
  let newfname = newfamname in 
  let fref, basename = 
    let (ToplevelRef (famname, ((ftm, fty), ctx) )) = name_to_family_ref bname in 
     (* let ref = 
        (ToplevelRef (famname, ((ftm, (family_type_rename fty fname)), ctx) )) in  *)
        let ref = 
          (ToplevelRef (famname, ((ftm, fty), ctx) )) in 
      ref, fst fty in 

  push inhbasestack (InitialOnMixedInh (mixedinh, fref, newfamname));
  (* directly put the empty family, because it is a new judgement*)
  push inhcontentref ((fst newfname), (empty_inh basename newfname (currentinh_output_ctx ())))
  


let add_prec (fname : name) 
(indref : fieldpath) = 
  assert_current_has_open_judgement ();
  if_allow_new_field fname;
  let current_ctx = currentinh_output_ctx() in 
  let inddef, prec_register_point = 
    let t = locate_in_fam_type_withself current_ctx indref in 
    match t with 
    | CoqIndTy {indsigs_from_org_ctx; registered_prec; _}-> indsigs_from_org_ctx, registered_prec
    | _ -> cerror ~einfo:"Should refer to an inductive type!" () in
  let validcstrs = extract_cstrs_ident (fst inddef) in 
    ontopinh
    (fun (name, current_inh) ->
      (name, inhnewprec current_inh fname indref validcstrs));
    (* register the name of prec, used by fdiscriminate *)
    prec_register_point := Some fname


let add_rec2d ?(fname = (None : name option)) 
~(recursorref : fieldpath) ()
(* ~(indref : fieldpath)  *)
= 
assert_current_has_open_judgement ();
let fname = 
  match fname with 
  | None ->   
  let _, basename = to_qualid_name recursorref in 
  let rec2dname = freshen_name ~prefix:(Nameops.add_prefix "RComp回" basename) () in  
  rec2dname 
  | Some fname -> fname
in 
if_allow_new_field fname;
let current_ctx = currentinh_output_ctx() in 
let indref = 
  let _ = 
    let open Pp in 
    Utils.msg_notice @@ (str "Trying to find") ++ Libnames.pr_qualid recursorref 
  in 
  let t = locate_in_fam_type_withself current_ctx recursorref in 
  match t with 
  | PRecTy {inductivedef = inductivedef, _; _} 
  | RecTy {inductivedef; _} -> inductivedef
  | _ -> cerror ~einfo:"Should refer to an inductive type!" () in
  ontopinh
  (fun (name, current_inh) ->
    (name, inhnewrec2d current_inh fname recursorref indref))

let add_rec2d_on (recursorref : name) = 
  let recursorref =  match current_family_name () with 
  | None -> cerror ~einfo:"Supposed to be in a family!" () 
  | Some current_family_name -> _point_qualid_ ((self_version_name current_family_name)) (Libnames.qualid_of_ident recursorref) in 
  add_rec2d ~recursorref ()

let add_recursor_and_rec2d fname rec_mod motive indref postfix = 
  add_recursor fname rec_mod motive indref postfix;
  add_rec2d_on fname

let add_prec_and_rec2d (fname : name) 
(indref : fieldpath) = 
  add_prec fname indref;
  add_rec2d_on fname 




(* given an inductive type reference, we generate *)
let generate_prec_name (indref : fieldpath) : name =
  assert_current_has_open_judgement ();
  let current_ctx = currentinh_output_ctx() in 
  let inddef = 
    let t = locate_in_fam_type_withself current_ctx indref in 
    match t with 
    | CoqIndTy {indsigs_from_org_ctx; _}-> indsigs_from_org_ctx
    | _ -> cerror ~einfo:"Should refer to an inductive type!" () in
  let validcstrs = extract_cstrs_ident (fst inddef) in 
  let validcstrnames = List.fold_left (fun n m -> n^(Names.Id.to_string m))  "" validcstrs in 
  let indty_name = extract_type_ident  (fst inddef) in 
  (* we only support single inductive type right now *)
  assert_cerror_forced ~einfo:"We only support single inductive type now"
  (fun _ -> List.length indty_name = 1);
  let indty_name = Names.Id.to_string @@ List.hd indty_name in 
  let final_name = 
  indty_name^validcstrnames^"_prec" in 
  Names.Id.of_string final_name
  (* we do name concat *)


(* only called directly after inductive type is defined  *)
let post_generate_prec_and_rec2d_after_inductive_def (indname : name) = 
  let indref = attach_self_prefix_qualid (Libnames.qualid_of_ident indname) in 
  let current_ctx = currentinh_output_ctx() in 
  (* we need to check if the inductive type is not inductive family *)
  let inddef = 
    let t = locate_in_fam_type_withself current_ctx indref in 
    match t with 
    | CoqIndTy {indsigs_from_org_ctx; _}-> indsigs_from_org_ctx
    | _ -> cerror ~einfo:"Should refer to an inductive type!" () in
  let is_sort = 
    let indcstrs = List.map (fun (x,_) -> extract_type_and_cstrs x) @@ List.hd @@ fst inddef in 
    let type_decl_sort = List.map (fun ((_, t), _) -> Option.get t) indcstrs in 
    List.for_all (
      fun t -> 
        match t.CAst.v with 
        | Constrexpr.CSort _ -> true 
        | _ -> false 
    ) type_decl_sort
  in 
  if is_sort then 
  (let precname = generate_prec_name indref in 
    add_prec_and_rec2d precname indref) 
  else () 

(* this function finds the correct frecursor
      to do appropriate rewriting *)
let do_frec_eval (recref : Evd.econstr) : unit Proofview.tactic = 
  let recref : fieldpath = 
    let env = Global.env() in 
    let sigma = Evd.from_env env in 
    let recref = EConstr.to_constr sigma recref in
    let recref = reflect_safeterm recref in 
    match recref with 
    | {CAst.v = Constrexpr.CRef (q, _); _} -> q
    | _ -> cerror ~einfo:"Expect A Path!" () in 
  let _ = 
    let open Pp in 
    Utils.msg_notice @@ (str "recursor path:") ++ Libnames.pr_qualid recref in  
  let current_ctx = currentinh_output_ctx () in 
  let recty = locate_in_fam_type_withself current_ctx recref in 
  let inddef, _ = 
    match recty with 
    | RecTy {inductivedef; _}  
    | PRecTy {inductivedef = inductivedef, _; _} -> 
      (let indty = locate_in_fam_type_withself current_ctx inductivedef in 
       match indty with 
       | CoqIndTy {indsigs_from_org_ctx; _} -> indsigs_from_org_ctx , inductivedef
       | _ -> cerror ~einfo:"Incorrect Type, should be an inductive type" ())
    | _ -> cerror ~einfo:"Should refer to a recursor/partial recursor!" () in
  let all_cstrs = extract_cstrs_ident (fst inddef) in 
  let all_rewrite_eqs = 
    List.map (
      fun each_cstr ->
        let pathprefix, base = to_qualid_name recref in 
        let each_cstr = Names.Id.to_string each_cstr in 
        let rewriteeq_name = Nameops.add_suffix base ("_on_"^each_cstr) in 
        let res = _qualid_point_ pathprefix rewriteeq_name in 
        let _ = 
          let open Pp in 
          Utils.msg_notice @@ (str "equation to rewrite:") ++ Libnames.pr_qualid res 
        in res
    ) all_cstrs 
  in 
  let open Tacexpr in 
  let open Constrexpr_ops in 
  (* Now that we know all the rewriting equation,
      we construct 
      repeat ( rewrite ... in * || ...) *)
  let res = 
    let each_rewrite_tactic (each_eq : fieldpath) = 
      (* this section can check g_tactic.mlg *)
      let rewrite_atom = mkRefC each_eq in 
      let l = [(true, Equality.Precisely 1, (None, ( rewrite_atom , Tactypes.NoBindings)))] in 
      let cl : 'a Locus.clause_expr = { Locus.onhyps=None; concl_occs=Locus.AllOccurrences } in 
      let t = None in 
      let rewrite_tacatom =  CAst.make @@ TacAtom (TacRewrite (false,l,cl,t)) in 
      rewrite_tacatom in 
    let all_rewrite_tactics = List.map each_rewrite_tactic all_rewrite_eqs in 
    let tacfail = 
      CAst.make (TacFail (TacLocal,Locus.ArgArg 0,[]))
    in 
    let union_rewrites = 
      List.fold_right (fun l r -> CAst.make (TacOrelse (l,r))) all_rewrite_tactics tacfail
    in 
    (* let repeat_union_rewrites = CAst.make (TacRepeat union_rewrites) in  *)
    Tacinterp.interp union_rewrites
  in 
  res

let finjection_on (cstrctr : Evd.econstr) (h : name) : unit Proofview.tactic = 
  let inj_prop_name = 
    let env = Global.env() in 
    let sigma = Evd.from_env env in 
    let cstrctr = EConstr.to_constr sigma cstrctr in
    let q = match reflect_safeterm cstrctr with 
    | {CAst.v = Constrexpr.CRef (q, _); _} -> q 
    | _ -> cerror ~einfo:"Expect a Reference" () in 

    let prefix, b = to_qualid_name q in 
    let b = Nameops.add_suffix b "__injective" in 
    _qualid_point_ prefix b in
  let target = 
    let open Constrexpr_ops in 
    mkAppC ((mkRefC inj_prop_name), [mkIdentC h]) in 
  let tactic = 
    CAst.make (Tacexpr.TacArg (Tacexpr.TacCall (CAst.make ( Libnames.qualid_of_ident (Names.Id.of_string "generalize_pose") ,[Tacexpr.ConstrMayEval (Genredexpr.ConstrTerm target)]))) ) in 
  Tacinterp.interp tactic


let fdiscriminate_by  (h : name) (typ : Evd.econstr) : unit Proofview.tactic = 
  let current_ctx = currentinh_output_ctx () in
  let prec_path = 
    let env = Global.env() in 
    let sigma = Evd.from_env env in 
    let typ = EConstr.to_constr sigma typ in
    let indref = match reflect_safeterm typ with 
    | {CAst.v = Constrexpr.CRef (q, _); _} -> q 
    | _ -> cerror ~einfo:"Expect a Reference" () in 
    let prec_name = 
      let t = locate_in_fam_type_withself current_ctx indref in 
      match t with 
      | CoqIndTy {registered_prec; _}-> !registered_prec
      | _ -> cerror ~einfo:"Should refer to an inductive type!" () in
    let prec_name = 
        match prec_name with
        | None -> cerror ~einfo:("Expect Registered Partial Recursor for "^ Libnames.string_of_qualid indref) ()
        | Some prec_name -> prec_name in
    let prec_path = 
        let prefix, _ = to_qualid_name indref in 
        _qualid_point_ prefix prec_name
      in 
    prec_path in 
  let h = Libnames.qualid_of_ident h in 
  let tactic = 
    CAst.make (Tacexpr.TacArg (Tacexpr.TacCall (CAst.make ( Libnames.qualid_of_ident (Names.Id.of_string "prec_discriminate") ,[Tacexpr.Reference prec_path; Tacexpr.Reference h]))) ) in 
  Tacinterp.interp tactic



module FRecursionSugar = struct
  

(* FRecursion as syntactic sugar for 
   1. a handler family, with "motive" as one member
   2. and a recursion checking field 
   
  So algorithmically speaking, For new FRecursion block 
  1. when start_frecursion_block happens, we will create a new family with one new field "motive" 
    (i.e. use open_new_inhjudgement and add_new_field)
  1.5 we will calculate, from the motive, what type each handler should have 
  2. inside which we can use `Case` to add fields. 
    (i.e. use add_new_field)
  3. when close_frecursion_block, we will `close_current_inh_judgement` and then `add_recursor`

  For extended FRecursion block 
  1. we will check if the parent family like `XXX_handler` and `XXX` exists where `XXX` is also an frecursor
     also we will check if `XXX_handler` has a member called `motive`
  1.5 we will calculate, from the motive, what type each handler should have 
  2. inside which we still use `Case` to add *new* fields
    (Note : So overriding is not supported here)
  3. when close_frecursion_block, we will `close_current_inh_judgement` and then inherit the recursor 

*)

(* This will be a map collecting  *)
(* let frecursion_defined_handlers = nonimplement () *)
let frecursion_handler_type : rawterm Dict_Name.t option ref = Summary.ref ~name:"FRecursionHandlerTypes" None 

type frecursion_config = {new_or_extend : [`New | `Extend] ; fname : name; motive : rawterm; indtype : fieldpath; postfix : name; outside_family_name : name}
let frecursion_config_record : frecursion_config option ref = Summary.ref ~name:"FRecursionConfiguration" None 

let handler_suffix fname = Nameops.add_suffix fname "_handler"
let _motive = (Names.Id.of_string "_motive")


(* helper function, not supposed to be used outside
   given the current FRecursion name and inductive type path
   we include the recursor handler type into a new module (with a new name) (into the current ctx)
   called handlers_mod_name into the current context
   also return all the constructor *)
let include_recursor_handler_type (fname : name) (indtype : fieldpath) (postfix : string) = 
  (* Setup frecursion_handler_type, frecursion_config_record *)
  let current_ctx = currentinh_output_ctx () in 
  let inddef = 
    let t = locate_in_fam_type_withself (currentinh_output_ctx()) indtype in 
    match t with 
    | CoqIndTy {indsigs_from_org_ctx; _}-> indsigs_from_org_ctx
    | _ -> cerror ~einfo:"Should refer to an inductive type!" () in
  let _, inddef_and_recursor_handlers = inductive_to_famterm_and_recursor_type inddef in 
  let (_, _ctx), all_recur_handler_types_smap = smap_assoc ~einfo:__LOC__ postfix inddef_and_recursor_handlers  in 
  (* we first gather all the handlers, and wrap them into one module *)
  let (all_recur_handler_types, handlers_mod_name) : (coqterm typed) * name = 
    let handlers_mod_name = freshen_name ~prefix:fname () in 
    
    let parameters_ = famctx_to_parameters_selfprefix _ctx in 
    let open CoqVernacUtils in 
    let inner_module = runVernac @@ (
      define_module handlers_mod_name parameters_ (
        fun ctx -> 
          let include_all_recur_handlers = 
            List.map 
              (fun (_, (ModTerm y, _)) -> 
                include_mod (apply_mods (pure y) ctx)) all_recur_handler_types_smap in 
          flatmap include_all_recur_handlers
      )
    ) in 
    let wrapped_module = runVernac @@ 
      wrap_inner_mod handlers_mod_name inner_module parameters_ in 
    (* after inclusion, handlers_mod_name is on the path to access each handler *)
    ((ModTerm wrapped_module, _ctx), handlers_mod_name) in 
  (* now we weaken it *)
  let all_recur_handler_types = wk_coq_term all_recur_handler_types current_ctx in 
  (* Now we include this gathering *)
  add_meta_data_section all_recur_handler_types;
  (* then we can construct the frecursion_handler_type, 
      basically each looks like self__XX_handler.YY回aaaa.cstri *)
  handlers_mod_name, List.map fst all_recur_handler_types_smap


(* helper function, not supposed to be used outside
   set up frecursion_handler_type correctly
   the idea is that, for the handler included in the above function, they are without motive
   this one when inclusion happens, will include motive
   *)
let prepare_frecursion_handler_type ~_motive_path ~current_family_name ~handlers_mod_name ~each_handler_name = 
  let motive_term = Constrexpr_ops.mkRefC _motive_path in 
  let proper_prefix t = _point_qualid_ (self_version_name current_family_name) @@ _point_qualid_ handlers_mod_name @@ (Libnames.qualid_of_ident (Nameops.add_prefix ("__handler_type_") t)) in 
  let rec_handler_type_of t = 
    Constrexpr_ops.mkAppC
    ((Constrexpr_ops.mkRefC (proper_prefix t)), [motive_term]) in 
  let each_cstr_rec_handler = List.map (fun (a) -> (a, rec_handler_type_of a)) each_handler_name in 
  let each_cstr_rec_handler = Dict_Name.add_seq (List.to_seq each_cstr_rec_handler) Dict_Name.empty in 
  frecursion_handler_type := Some each_cstr_rec_handler

let start_frecursion_block 
    (fname : name)  
    (motive : rawterm) 
    (indtype : fieldpath) 
    (postfix_ : name) : unit = 
    assert_current_has_open_judgement ();
    (* let's make sure all the scope manipulation happens in the mlg file *)
    (* assert_in_scope OpenedFamily; *)
    let fname_handler = handler_suffix fname in 
    let outside_family_name = fst (peek inhcontentref) in 
    if_allow_new_fields ([fname; fname_handler]);
    open_new_inhjudgement fname_handler; 
    add_new_field _motive motive;

    (* Now we prepare frecursion_handler_type *)
    let postfix = Names.Id.to_string postfix_ in
    let current_family_name = fname_handler in 
    let _motive_path : fieldpath = _point_qualid_ (self_version_name current_family_name) @@ Libnames.qualid_of_ident _motive in 
    let handlers_mod_name, each_handler_name = include_recursor_handler_type fname indtype postfix in 
    prepare_frecursion_handler_type ~_motive_path ~current_family_name ~handlers_mod_name ~each_handler_name;
    let motive_from_outside = 
      let motive_from_outside_path = 
        _point_qualid_ (self_version_name outside_family_name)
          @@ _point_qualid_ (current_family_name) @@ Libnames.qualid_of_ident _motive  
      in 
      Constrexpr_ops.mkRefC motive_from_outside_path 
    in 
    (* Then we construct frecursion_config_record *)    
    frecursion_config_record := Some { new_or_extend = `New; fname; motive = motive_from_outside; indtype ; postfix = postfix_ ; outside_family_name}

let extend_frecursion_block (fname : name) : unit = 
  (* TODO: do some sanity check *)
  let fname_handler = handler_suffix fname in
  let outside_family_name = fst (peek inhcontentref) in 
  (* get ind type and information first *)
  let (_, parent_family_ty), _ = 
    get_family_ty_in_inhbase (dummy_famname) (peek inhbasestack, (currentinh_output_ctx ())) 
  in 
  let indtype, postfix = 
    let fname_ty =  locate_in_fam_type parent_family_ty [fname] in 
    match fname_ty with 
    | RecTy {inductivedef; postfix; motive; _} -> (inductivedef, snd motive), postfix 
    | _ -> cerror ~einfo:("Can only extend parent FRecursion "^__LOC__) ()  
  in 
  let indtype = wkinh_path indtype (currentinh_output_ctx()) in 
  (* let's make sure all the scope manipulation happens in the mlg file *)
  (* assert_in_scope OpenedFamily; *)
  extend_new_nested_inhjudgement fname_handler;
  (* inherit the _motive *)
  add_inherited_fields_until_and_including _motive;
  (* Setup frecursion_handler_type, frecursion_config_record *)
  let current_family_name = fname_handler in 
  let _motive_path : fieldpath = _point_qualid_ (self_version_name current_family_name) @@ Libnames.qualid_of_ident _motive in 
  let handlers_mod_name, each_handler_name = include_recursor_handler_type fname (fst indtype) postfix in 
  prepare_frecursion_handler_type ~_motive_path ~current_family_name ~handlers_mod_name ~each_handler_name;
  let motive_from_outside = 
    let motive_from_outside_path = 
      _point_qualid_ (self_version_name outside_family_name)
        @@ _point_qualid_ (current_family_name) @@ Libnames.qualid_of_ident _motive  
    in 
    Constrexpr_ops.mkRefC motive_from_outside_path in
  (* Then we construct frecursion_config_record *)    
  frecursion_config_record := Some { new_or_extend = `Extend; fname; motive = motive_from_outside; indtype = fst indtype ; postfix = Names.Id.of_string postfix; outside_family_name}


let add_frecursion_handler (fname : name) (t : rawterm) = 
  assert_current_has_open_judgement ();
  if_allow_new_field fname;
  assert_in_scope FRecursion;
  let fieldty = 
    match !frecursion_handler_type with 
    | Some d -> 
      begin match Dict_Name.find_opt fname d with  
            | Some ty -> ty 
            | None -> cerror ~einfo:("No Corresponding Constructor for "^ Names.Id.to_string fname) ()
      end 
    | None -> cerror ~einfo:("Not supposed happening "^__LOC__ )() 
  in 
  (* let add_new_field_with_empty_top_ctx (i : name) eT (e : Constrexpr.constr_expr)  : unit = 
    assert_current_has_open_judgement();
    if_allow_new_field i;
    let current_ctx = currentinh_output_ctx() in 
    let top_cleared_ctx = 
      let FamCtx current_ctx = current_ctx in  
      match current_ctx with 
      | [] -> cerror ~einfo:("Unexpected"^__LOC__) () 
      | (hname, (hfname, _)) :: rest -> FamCtx ((hname, (hfname, [])) :: rest)
    in 
    let embedt = CoqVernacUtils.runVernac (embed_tterm i ~eT e top_cleared_ctx) in
    let typ = CoqTyWithTerm {tm = ModType embedt} 
  in
  let newinhop = CInhNew (ModTerm embedt, current_ctx) in 
  let newoupty = typ, current_ctx in 
  ontopinh
    (fun (name, current_inh) ->
      (name, inhnew current_inh i ~newinhop ~newoupty)); () in 
  (* We don't directly add_new_field but only add_new_field with "empty top context"
      because we don't want Case able to refer to each other  *)
  add_new_field_with_empty_top_ctx fname (Some fieldty) t *)
  
  (* However the above is not correct because attach_self_prefix is the one finding
      correct path *)
  add_new_field fname ~eT:(Some fieldty) t


let close_frecursion_block () = 
  assert_current_has_open_judgement ();
  let fname, new_or_extend, motive, indtype, postfix, outside_family_name = 
    match !frecursion_config_record with 
    | Some {fname; new_or_extend; motive; indtype; postfix; outside_family_name; _} -> fname, new_or_extend, motive, indtype, postfix, outside_family_name
    | None -> cerror ~einfo:("Not in any FRecursion scope! "^__LOC__ )() 
  in 
  begin match new_or_extend with 
  | `Extend ->
      inherits_all_remained(); 
      close_current_inh_judgement();
      add_inherited_fields_until_and_including fname;
  | `New -> 
      close_current_inh_judgement();
      (* add_recursor fname rec_mod motive indref postfix *)
      let outside_family_name_self = Libnames.qualid_of_ident (self_version_name outside_family_name) in 
      let fhandler_name = handler_suffix fname in 
      let rec_mod = _qualid_point_ (Some (outside_family_name_self)) fhandler_name in 
      add_recursor_and_rec2d fname rec_mod motive indtype postfix
  end;
  (* Now we clean up the two data structure *)
  frecursion_handler_type := None;
  frecursion_config_record := None

end