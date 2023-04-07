(* This file is responsible for the FTheorem/FClaim related functionality
    at the interaction level so it is the same level as famprogram   
*)
open Familytype
open Fenv
open Utils
open Ltac_plugin
open Finh
(* open FamTyID *)
(* open CoqIndSigUtil *)





(* Field Theorem Proving:
    We allow Field x : type. (starting proving model) FieldQed. 
  The idea is that, we will declare a module around it. 
  The user will construct the theorem inside this module. 
  The issue here is that when user input Qed. There won't be rejection. 
  Consider translation 
    Module ... 
      Theorem ... 
      Qed.  <--- Qed itself won't be rejected
    End Module... 
    Thus we need to have the invariance that 
      claim_goal_info = None iff current_proof_mode = off 
*) 

type claim_type = 
  | SimpleGoal 
  | FTheorem of {
                (* fname : name;  *)
  (* The name of the final fields of that theorem*)
                 goal_name : name; 
  (* The name of the proved goal inside the compiled mod *)
                 (* mod_name : name; *)
  (* The name of the compiled module *)
                 compiled_motive : coqtype ;
  (* The motive of the current theorem *)
                 motive_modname : name;
                 auxillary_motive_modname : name;
                 implementing_handlers : (name, coqterm typed) smap;
  (* the (new) case handlers (their types) to prove  *)
                 all_handler_names : name list;
                 extending : bool;
  (* Possibly inherited module *)
                 parameter_for_ctx : modtermref list;
  (* the ctx parameter of the current opening module *)
                 indref : Libnames.qualid typed;
                 postfix : string;
                 recty : coqtype typed ;
                 wrapped_recty_in_tm : coqterm typed;
                 }
type claim_goal_info_type = 
  { fname : name ;  (* the name of the field *)
    modname : name CAst.t ; (* The openning scope module has the name *)
    goal : rawterm ;  (* The rawterm for the goal *)
    claimT : claim_type; 
    ov_dependencies : pins_dependencies option;
    (* If it is None, it is usual, non-overridable fields; 
       if it is something then it is overridable *)
    overriding_info : family_type_or_coq_type typed option; 
    (* if it is None, then it is the first overridable term
       if it is something, then it is overriding parent terms *)
  }
let claim_goal_info = Summary.ref ~name:"FieldProofMode" (None : (claim_goal_info_type option))

(* TODO : implement transparent field (in module type) 
      by lifting definition into the module type 
*)

let assert_proof_mode_consistent () =
  let open Vernacstate in 
  let coq_state = (Vernacstate.freeze_interp_state ~marshallable:false) in
  let coq_proof_mode_is_close = (coq_state.lemmas = None) in 
  let plugin_proof_mode_is_close = (! claim_goal_info = None) in 
  assert_cerror ~einfo:"Inconsistent Proof Mode!" (fun _ ->coq_proof_mode_is_close = plugin_proof_mode_is_close)

let assert_proof_mode_open () = 
  assert_cerror ~einfo:"Not in a proof mode yet!" (fun _ -> !claim_goal_info <> None)


let assert_single_goal (goals : (name * Constrexpr.constr_expr) list) : name =
  assert_cerror_forced ~einfo:"Only Support Single Goal (No Mutual Recursive Allowed)" 
  (fun _ -> List.length goals = 1);
  let (fname , _) = List.hd goals in 
  fname


let only_support_one_name_type (goals : (name * Constrexpr.constr_expr) list) : (name * rawterm) = 
  assert_cerror ~einfo:"Currently Only Support One Goal!" (fun _ -> List.length goals = 1);
  let (id, rawtype) = List.hd goals in 
  id, rawtype


let open_claim_goal_info_prepare ?(ov_dependencies = (None : Set_Fieldpath.t option)) (goals : (name * Constrexpr.constr_expr) list) = 
  assert_current_has_open_judgement();
  let _ = 
    let fname = assert_single_goal goals in 
    if_allow_new_field fname
  in 
  assert_cerror_forced ~einfo:"Please close last claim" (fun () -> !claim_goal_info = None);
  let current_ctx = currentinh_output_ctx () in
  (* assert_cerror ~einfo:"Please Finish the Current Pending Proof First!" (!claim_goal_info = None); *)
  (* let's make things easier by onlu allow one goal with empty binders *)
  let fname, goal = only_support_one_name_type goals in 
  check_field_non_exist_in_constructing_basis fname;
  let modname = CAst.make @@ freshen_name ~prefix:fname () in
  let parameters_with_self = 
    match ov_dependencies with 
    | None -> famctx_to_parameters_selfprefix  current_ctx 
    | Some ov_exposed -> famctx_to_parameters_selfprefix ~ov_exposed current_ctx in  
  let parameters_ = 
    List.map 
      (fun (n,m) -> 
        (None, [CAst.make n], (m, Declaremods.DefaultInline))) parameters_with_self in 
  let ov_dependencies = Option.map (fun x -> Pins x) ov_dependencies in 
  claim_goal_info := Some {fname; modname; goal; claimT = SimpleGoal; ov_dependencies; overriding_info = None};
  (modname, parameters_)

let override_open_claim_goal_info_prepare ?(ov_dependencies = (None : Set_Fieldpath.t option)) (goals : (name * Constrexpr.constr_expr) list) = 
  assert_current_has_open_judgement();
  let _ = 
    let fname = assert_single_goal goals in 
    if_allow_extend_field fname in
  assert_cerror_forced ~einfo:"Please close last claim" (fun () -> !claim_goal_info = None);
  let current_ctx = currentinh_output_ctx () in
  (* assert_cerror ~einfo:"Please Finish the Current Pending Proof First!" (!claim_goal_info = None); *)
  (* let's make things easier by onlu allow one goal with empty binders *)
  let fname, goal = only_support_one_name_type goals in 
  check_top_uninherited_field fname;
  (* extract the parent type *)
  let modname = CAst.make @@ freshen_name ~prefix:fname () in
  let parentty, (past_dependencies, _) = 
    match top_uninherited_field () with 
    | None -> cerror ~einfo:"Nothing To Override!" ()
      (* TOD: tytm can be used to do type-checking instead of the current annotated_type  *)
    | Some (fname, (OvCoqTyWithTerm a, ctx)) -> 
      (OvCoqTyWithTerm a, ctx), wkinh_dependencies a.dependencies current_ctx
    | Some _ -> cerror ~einfo:"Not the overriding term!" () 
  in 
  let ov_dependencies = 
    match ov_dependencies with 
    | None -> Some past_dependencies
    | _ -> Option.map (fun x -> Pins x) ov_dependencies in  
  let parameters_with_self = famctx_to_parameters_selfprefix2 ov_dependencies current_ctx in
  let parameters_ = 
    List.map 
      (fun (n,m) -> 
        (None, [CAst.make n], (m, Declaremods.DefaultInline))) parameters_with_self in
  (* let ov_dependencies = Option.map (fun x -> Pins x) ov_dependencies in  *)
  claim_goal_info := Some {fname; modname; goal; claimT = SimpleGoal; ov_dependencies; overriding_info = Some parentty};
  (modname, parameters_)


let start_proving_claim_goal_info () = 
  let fname, goal = 
    match !claim_goal_info with 
    | None -> cerror ~einfo:"Should be inside FieldClaim!" ()
    | Some {fname; goal; _} -> fname, goal in  
  (* type checking *)
  let env = Global.env () in
  let evd = Evd.from_env env in
  let (evd, type_checked_goal) = Constrintern.interp_constr_evars env evd goal in 
  let info = Declare.Info.make () in
  let cinfo =
    Declare.CInfo.make ~name:fname ~typ:type_checked_goal () in 
  let ongoing_proof = Declare.Proof.start ~info ~cinfo evd in 
  ongoing_proof



let close_claim_and_collect_claim_goal_info () = 
    let fname, goal, modname, new_dependencies, overriding_info = 
      match !claim_goal_info with 
      | None -> cerror ~einfo:"Should be right after FieldClaim!" ()
      | Some {fname; goal; modname; ov_dependencies;overriding_info; _} -> fname, goal, modname, ov_dependencies, overriding_info in  
    assert_cerror_forced ~einfo:"Claim is not proved!" (fun _ -> Constrintern.is_global fname);
    let isopaque = 
      let fname_constant = Nametab.locate_constant (Libnames.qualid_of_ident fname) in 
      let env = Global.env () in 
      let fname_cst_body = (Environ.lookup_constant fname_constant env).Declarations.const_body in 
      match fname_cst_body with 
      | Declarations.OpaqueDef _ -> true 
      | _ -> false in 
    (* use lookup_constant to get constant_body
       then constant_body has constant_def that we can check if it is opaque or not *)
    (* check if fname is defined in opaque or transparent *)
    let open CoqVernacUtils in 
    let _ = 
      let open CoqVernacUtils in 
      runVernac @@ 
      vernac_ (Vernacexpr.VernacEndSegment modname) in 
    let current_ctx = currentinh_output_ctx () in
    let mtype = runVernac @@ embed_ty fname goal current_ctx in 
    (* TODO: make dependency applies here, to make embed_tterm with stronger information
        (i.e. pass in dependency to embed_tterm) 
        currently we don't do that for simiplication *)
    let mtytm = (ModTerm (runVernac @@ embed_tterm fname goal current_ctx), fname) in 
    let tm = (Libnames.qualid_of_ident modname.CAst.v) in 

    (* it could be either Override or a new Term  *)
    begin match overriding_info with 
    | None -> 
      let newinhop = CInhNew (ModTerm tm, current_ctx) in 
      (* if we are using Overridable pins, 
            then we will have dependencies = Some .., and we use OvCoqTyWithTerm
        if not we will have  dependencies = None and we use CoqTyWithTerm*)
      let newoupty = 
        match new_dependencies with 
        (* Automatic overidable *)
        | None when isopaque -> OvCoqTyWithTerm {tm = ModType tm; ty = ModType mtype; dependencies = Pins (Set_Fieldpath.empty), current_ctx ; isopaque; default_retry = None; tytm = mtytm}, current_ctx
        | None -> CoqTyWithTerm {tm = ModType tm}, current_ctx 
        | Some dependencies -> OvCoqTyWithTerm {tm = ModType tm; ty = ModType mtype; dependencies = dependencies, current_ctx ; isopaque; default_retry = None; tytm = mtytm}, current_ctx
      in
      (* let newoupty = CoqTy (ModType mtype), current_ctx in  *)
      (* legacy code above, change to overridable coqty *)
      (* let dependencies = dependencies, current_ctx in  *)
      (* let newoupty = OvCoqTyWithTerm {tm = ModType tm; ty = ModType mtype; dependencies ; isopaque}, current_ctx in *)
      ontopinh
        (fun (name, current_inh) ->
          (name, inhnew current_inh fname ~newinhop ~newoupty))
    | Some (OvCoqTyWithTerm {tm = inptm; tytm; ty = inpty; dependencies; default_retry; _}, _) -> 
      let new_dependencies = 
        match new_dependencies with 
        | None -> cerror ~einfo:"Should be overridable" ()
        | Some e -> (e, current_ctx)
      in 
      ontopinh 
      (fun (parentnanme, parent_inh) ->
        (* TODO: do type checking! i.e. do conversion checking between
           annotated_type and inpty *)
        (parentnanme, inhoverride parent_inh fname (ModTerm tm, current_ctx) tytm ~inptm ~inpty ~dependencies ~new_dependencies ~isopaque ~inp_default_retry:default_retry ~default_retry))
    | _ -> cerror ~einfo:"Unexpected Overridden Parent" ()
    end;
    claim_goal_info := None

  

(* FTheorem related *)
let open_ftheorem_info_prepare 
    (* ?(ov_dependencies = Set_Fieldpath.empty) *)
    (fname : name) 
    (motive : rawterm) 
    ?(postfix = "_ind_comp")
    (indtype : Libnames.qualid) = 
  (* we still use claim_goal facility *)
  assert_current_has_open_judgement();
  if_allow_new_field fname;
  assert_cerror_forced ~einfo:"Please close last claim" (fun () -> !claim_goal_info = None);
  let current_ctx = currentinh_output_ctx () in
  let open CoqVernacUtils in 
  (* we first compile the motive to pass the type-checking of the motive *)
  let compiled_motive = 
    let modname = freshen_name ~prefix:(Nameops.add_suffix fname "_motive_mod") () in 
    let parameters = famctx_to_parameters_selfprefix current_ctx in 
    runVernac @@ 
    define_module modname parameters 
    (fun ctx -> define_term ((Nameops.add_prefix "__motiveT" fname)) motive) in 
  let compiled_motive = ModType compiled_motive, current_ctx in

  (*  then we locate the inddefs, and get the recursor (type) *)
  let inddef = 
    let t = locate_in_fam_type_withself current_ctx indtype in 
    match t with 
    | CoqIndTy {indsigs_from_org_ctx; _}-> indsigs_from_org_ctx
    | _ -> cerror ~einfo:"Should refer to an inductive type!" () in
  let _, inddef_and_recursor_handlers = inductive_to_famterm_and_recursor_type inddef in 
  let _, all_recur_handlers = smap_assoc ~einfo:__LOC__ postfix  inddef_and_recursor_handlers  in 

  (* we initialize some name here, freshen_name has side effect so it is using a new name now *)
  let open Constrexpr_ops in 
  let goal_name = freshen_name ~prefix:fname () in 
  let motive_modname = freshen_name ~prefix:(Nameops.add_suffix fname "_motive_mod") () in  
  let modname = CAst.make @@ freshen_name ~prefix:fname () in
  (* what is auxillary_motive_modname? *)
  let auxillary_motive_modname = 
    let s = Names.Id.to_string fname in 
    let s = string_of_int (Hashtbl.hash s) in 
    let open Nameops in 
    (add_suffix (add_prefix "_auxillary_motive_mod_" fname) s) in 
  
  (* Starting from here it is too chaotic
     The story here is that, FTheorem needs to be extensible and mixable
     so there will be some name-confusion to avoid the conflict when we do "include" during mixin
     each_subhandler will not be repeated, but motive might be so we need name-confusing only for the motives

    TODO: refactorization!
      *)
  let recty, wrapped_recty_in_tm = 
    let ModType motive, _ctx = compiled_motive in  
    let parameters_ = (famctx_to_parameters_selfprefix _ctx) in 
    let wrapped_compiled_motive_incoqty =
      runVernac @@ wrap_modtype_into_module_modtype auxillary_motive_modname motive parameters_ in 
    (* We wrap the motive inside motive_modname *)
    let motiveTpathprefix = Some (Libnames.qualid_of_ident auxillary_motive_modname) in 
    let res1 = get_recty_from_motive ~motiveTpathprefix fname (ModTerm wrapped_compiled_motive_incoqty, _ctx) in 
    let wrapped_compiled_motive_incoqterm =
      runVernac @@ wrap_inner_mod auxillary_motive_modname motive parameters_ in 
    let res2 = ModTerm wrapped_compiled_motive_incoqterm, _ctx in 
    res1, res2
  in
  let goal = 
    let motive_modname = Libnames.qualid_of_ident motive_modname in 
    let the_motive = mkRefC @@ _qualid_point_ (Some motive_modname) (Nameops.add_prefix "__motiveT" fname) in 
    let __True = mkIdentC (Names.Id.of_string "True") in
    let __prod l r = 
      let using_prod_or_conj = if postfix = "_ind_comp" then "and" else "prod" in  
      mkAppC (mkIdentC (Names.Id.of_string using_prod_or_conj), [l; r]) in
    let all_recur_name = List.map (fun x -> Nameops.add_prefix "__handler_type_" (fst x)) all_recur_handlers in 
    let all_recur_ = List.map mkIdentC ( all_recur_name) in 
    let all_applied_recur = List.map (fun x -> mkAppC (x, [the_motive])) all_recur_ in 
    List.fold_right __prod all_applied_recur __True in 
  let parameters_with_self = famctx_to_parameters_selfprefix current_ctx in 
  let parameter_for_ctx =
    List.map 
      (fun (n,m) ->
        Libnames.qualid_of_ident n) parameters_with_self in 
  let indref = (indtype, current_ctx) in 
  let all_recur_handlers = List.map (fun (x, y) -> x, (wk_coq_term y current_ctx) ) all_recur_handlers in 
  let all_handler_names = List.map fst all_recur_handlers in 
  let compiled_motive = fst compiled_motive in 
  claim_goal_info := Some
  {fname; modname; goal; ov_dependencies = None;
        overriding_info = None;
    claimT = FTheorem {goal_name;compiled_motive; implementing_handlers = all_recur_handlers;all_handler_names; extending = false; parameter_for_ctx; indref; postfix; motive_modname; recty; wrapped_recty_in_tm; auxillary_motive_modname}}

let open_extend_ftheorem_info_prepare 
    (fname : name)  = 
  (* we still use claim_goal facility *)
  (* assert *)
  assert_current_has_open_judgement();
  if_allow_extend_field fname;
  assert_cerror_forced ~einfo:"Please close last claim" (fun () -> !claim_goal_info = None);
  let motive, indref, postfix, recty, legacy_handlers = 
    (match top_uninherited_field () with 
      | Some (fname_, (FTheoremTy {motive; indref; postfix; recty; all_handlers = legacy_handlers} , oldctx)) -> assert_cerror_forced ~einfo:"Not Correct Uninherited Field!" (fun _ -> fname = fname_); 
      motive, indref, postfix, recty, legacy_handlers
      | _ -> cerror ~einfo:"Not Correct Uninherited Field!" ()) in 
  
  let current_ctx = currentinh_output_ctx () in
  
  (* let open CoqVernacUtils in  *)
  let compiled_motive = motive in 
  let indref = wkinh_path indref current_ctx in 
  (*  first we locate the inddefs *)
  let inddef = 
    let t = locate_in_fam_type_withself current_ctx (fst indref) in 
    match t with 
    | CoqIndTy {indsigs_from_org_ctx; _} -> indsigs_from_org_ctx
    | _-> cerror ~einfo:"Should refer to an inductive type!" () in
  let _, inddef_and_recursor_handlers = inductive_to_famterm_and_recursor_type inddef in 
  let _, all_recur_handlers = smap_assoc ~einfo:__LOC__ postfix inddef_and_recursor_handlers  in 
  let all_recur_handlers = List.map (fun (x, y) -> x, (wk_coq_term y current_ctx) ) all_recur_handlers in 
  let all_handler_names = List.map fst all_recur_handlers in 
  let implementing_handlers = 
    let inside (x : 'a) (l : 'a list) = List.exists (fun k -> k = x) l in 
    List.filter (fun (x, y) -> not (inside x legacy_handlers)) all_recur_handlers in 
  let open Constrexpr_ops in 
  let goal_name = freshen_name ~prefix:fname () in 
  let modname = CAst.make @@ freshen_name ~prefix:fname () in
  let motive_modname = freshen_name ~prefix:(Nameops.add_suffix fname "_motive_mod") () in  
  let auxillary_motive_modname = 
    let s = Names.Id.to_string fname in 
    let s = string_of_int (Hashtbl.hash s) in 
    let open Nameops in 
    (add_suffix (add_prefix "_auxillary_motive_mod_" fname) s) in 
  let recty, wrapped_recty_in_tm = 
    let open CoqVernacUtils in 
    let _ctx = current_ctx in 
    let ModType motive = compiled_motive in  
    let parameters_ = (famctx_to_parameters_selfprefix _ctx) in 
    let wrapped_compiled_motive_incoqty =
      runVernac @@ wrap_modtype_into_module_modtype auxillary_motive_modname motive parameters_ in 
    (* We wrap the motive inside motive_modname *)
    let motiveTpathprefix = Some (Libnames.qualid_of_ident auxillary_motive_modname) in 
    let res1 = get_recty_from_motive ~motiveTpathprefix fname (ModTerm wrapped_compiled_motive_incoqty, _ctx) in 
    let wrapped_compiled_motive_incoqterm =
      runVernac @@ wrap_inner_mod auxillary_motive_modname motive parameters_ in 
    let res2 = ModTerm wrapped_compiled_motive_incoqterm, _ctx in 
    res1, res2
  in
  let goal = 
    let motive_modname = Libnames.qualid_of_ident motive_modname in 
    let the_motive = mkRefC @@ _qualid_point_ (Some motive_modname) (Nameops.add_prefix "__motiveT" fname) in 
    let __True = mkIdentC (Names.Id.of_string "True") in
    let __prod l r = 
      let using_prod_or_conj = if postfix = "_ind_comp" then "and" else "prod" in  
      mkAppC (mkIdentC (Names.Id.of_string using_prod_or_conj), [l; r]) in
    let implementing_names = List.map (fun x -> Nameops.add_prefix "__handler_type_" (fst x)) implementing_handlers in 
    let implementing_recur_ = List.map mkIdentC (implementing_names) in 
    let implementing__applied_recur = List.map (fun x -> mkAppC (x, [the_motive])) implementing_recur_ in 
    List.fold_right __prod implementing__applied_recur __True in 
  let parameters_with_self = famctx_to_parameters_selfprefix current_ctx in 
  let parameter_for_ctx =
    List.map 
      (fun (n,m) ->
        Libnames.qualid_of_ident n) parameters_with_self in 
  claim_goal_info := Some
  {fname; modname; goal; ov_dependencies = None ;
        overriding_info = None;
    claimT = FTheorem {goal_name;compiled_motive; implementing_handlers;all_handler_names; extending = true; parameter_for_ctx; indref; postfix; motive_modname;
    auxillary_motive_modname; recty; wrapped_recty_in_tm}}

let prepare_proving_ftheorem1 () = 
  let current_ctx = currentinh_output_ctx () in
  let modname, claimT = 
  match !claim_goal_info with 
  | None -> cerror ~einfo:"Should be inside FTheorem!" ()
  | Some ({modname; claimT; _}) -> modname, claimT in
  let _ = 
    match claimT with 
    | FTheorem _ -> ()
    | SimpleGoal -> cerror ~einfo:"Should be inside FTheorem!" () in 
  let parameters_with_self = famctx_to_parameters_selfprefix current_ctx in 
  let parameters_ = 
    List.map 
      (fun (n,m) -> 
        (None, [CAst.make n], (m, Declaremods.DefaultInline))) parameters_with_self in
    (modname, parameters_) 


let prepare_proving_ftheorem2 () =
  (* let current_ctx = currentinh_output_ctx () in *)
  let goal, claimT, claimbody = 
  match !claim_goal_info with 
  | None -> cerror ~einfo:"Should be inside FTheorem!" ()
  | Some ({goal; claimT; _} as claimbody) -> goal, claimT, claimbody in
  let all_recur_handlers, extending, parameter_for_ctx,compiled_motive,motive_modname, wrapped_recty_in_tm = 
    match claimT with 
    | FTheorem {implementing_handlers;extending;parameter_for_ctx;compiled_motive;motive_modname; wrapped_recty_in_tm; _} -> implementing_handlers, extending, parameter_for_ctx,compiled_motive,motive_modname, wrapped_recty_in_tm
    | SimpleGoal -> cerror ~einfo:"Should be inside FTheorem!" () in 
  (* weaken all_recur_handlers *)
  (* Note : weakening shouldn't be allowed here because
      we are in a defining module *)
  
  let open CoqVernacUtils in 
  let _ = runVernac @@ 
    (
    let include_all_recur_handlers = 
      List.map 
        (fun (x, (ModTerm y, z)) -> 
          include_mod (apply_mods (pure y) parameter_for_ctx) ) all_recur_handlers in 
    let* _ = flatmap include_all_recur_handlers in
    let (ModType motive) = compiled_motive in 
    let* _ = define_module motive_modname []
    (fun _ -> 
      include_mod (apply_mods (pure motive) parameter_for_ctx)
      )
     in 
     (* let (ModTerm motive, _) = wrapped_recty_in_tm in 
     let* _ = include_mod (apply_mods (pure motive) parameter_for_ctx)
      in  *)
    return ()
    ) in ()
  
    


let start_proving_ftheorem ?(split=true) () = 
  let goal, claimT = 
  match !claim_goal_info with 
  | None -> cerror ~einfo:"Should be inside FTheorem!" ()
  | Some {goal; claimT; _} -> goal, claimT in
  let goal_name, extending = 
    match claimT with 
    | FTheorem {goal_name;extending; _} -> goal_name, extending
    | SimpleGoal -> cerror ~einfo:"Should be inside FTheorem!" () in 
  (* type checking *)
  let env = Global.env () in
  let evd = Evd.from_env env in
  let _ = 
    let open Pp in 
    let wrap_comment x = str "(*" ++ x ++ str "*)" in 
    Utils.msg_notice @@ wrap_comment (pr_constr_expr goal) in 
  let (evd, type_checked_goal) = Constrintern.interp_constr_evars env evd goal in 

  let info = Declare.Info.make () in
  let cinfo =
    Declare.CInfo.make ~name:goal_name ~typ:type_checked_goal () in 
  let ongoing_proof = Declare.Proof.start ~info ~cinfo evd in

  (* let unfold_all_definition = 
    let open Tacexpr in 
    let open Genredexpr in 
    let open Locus in 
    let tac = TacAtom (TacReduce (Cbv (Redops.make_red_flag [FDeltaBut []]) , {onhyps = None; concl_occs = AllOccurrences })) in 
    let intp_tac = Tacinterp.interp (CAst.make tac) in 
    intp_tac
  in  *)
  let unfold_first_level = 
    let __unfold_motive_helper = 
      CAst.make (Tacexpr.TacArg (Tacexpr.TacCall (CAst.make ( Libnames.qualid_of_ident (Names.Id.of_string "__unfold_ftheorem_motive") ,[]))) ) in 
      Tacinterp.interp __unfold_motive_helper
  in 
  let unfold_nonsplit = 
    let __unfold_motive_helper = 
      CAst.make (Tacexpr.TacArg (Tacexpr.TacCall (CAst.make ( Libnames.qualid_of_ident (Names.Id.of_string "__unfold_ftheorem_motive_nested") ,[]))) ) in 
      Tacinterp.interp __unfold_motive_helper
  in 
  let repeat_split = Tacticals.tclREPEAT (Tactics.split_with_bindings false [Tactypes.NoBindings]) in
  let repeat_split_then_unfold = Tacticals.tclTHEN repeat_split unfold_first_level in
  let starting_operation = if split then repeat_split_then_unfold else unfold_nonsplit in 
  (* let is_complete_proof x = Proof.is_complete (Declare.Proof.get x) in 
  let ongoing_proof, _ = Declare.Proof.by unfold_all_definition ongoing_proof in 
  if is_complete_proof ongoing_proof then ongoing_proof 
  else *)

  (* let ongoing_proof, _ = Declare.Proof.by repeat_split ongoing_proof in *)
  let ongoing_proof, _ = Declare.Proof.by starting_operation ongoing_proof in
  ongoing_proof


(* Close the current goal and prove  *)
let close_ftheorem () = 
  let fname, goal, modname, claimT = 
  match !claim_goal_info with 
  | None -> cerror ~einfo:"Should be inside FTheorem!" ()
  | Some {fname; goal; modname; claimT;  _} -> fname, goal, modname, claimT in  
  let goal_name, extending, implemented_handlers, parameter_for_ctx, indref,compiled_motive, postfix, all_handler_names, motive_modname, auxillary_motive_modname, recty, wrapped_recty_in_tm  = 
  match claimT with 
  | FTheorem {goal_name;extending;compiled_motive; implementing_handlers; parameter_for_ctx; indref; postfix;all_handler_names;motive_modname;auxillary_motive_modname;recty;wrapped_recty_in_tm; _} -> goal_name, extending, implementing_handlers, parameter_for_ctx, indref,compiled_motive,postfix,all_handler_names,motive_modname,auxillary_motive_modname,recty,wrapped_recty_in_tm
  | SimpleGoal -> cerror ~einfo:"Should be inside FTheorem!" () in
  assert_cerror_forced ~einfo:"Claim is not proved!" (fun _ -> Constrintern.is_global goal_name);
  let all_implemented_handler_names = List.map fst implemented_handlers in 
  let current_ctx = currentinh_output_ctx () in 
  
  let open Constrexpr_ops in 
  let coq_fst (x : rawterm) : rawterm = 
    let fst = 
      let using_prod_or_conj = if postfix = "_ind_comp" then "proj1" else "fst" in 
      mkRefC @@ Libnames.qualid_of_ident (Names.Id.of_string using_prod_or_conj) in 
    mkAppC (fst, [x]) in 
  let coq_snd (x : rawterm) : rawterm = 
    let snd = 
      let using_prod_or_conj = if postfix = "_ind_comp" then "proj2" else "snd" in 
      mkRefC @@ Libnames.qualid_of_ident (Names.Id.of_string using_prod_or_conj)  in 
    mkAppC (snd, [x]) in 
  let rec _proj_each_case_handlers (all_recur_names : name list) (acc_case_handlers : rawterm) : (name, rawterm) smap = 
    match all_recur_names with 
    | [] -> [] 
    | h :: t -> 
      (h , coq_fst acc_case_handlers) :: _proj_each_case_handlers t (coq_snd acc_case_handlers) in 
  let implemented_case_names_handlers = _proj_each_case_handlers all_implemented_handler_names (mkIdentC goal_name) in 
  let open CoqVernacUtils in 

  let _ = runVernac @@ 
        let define_implemented_case_names_handlers =
          List.map (fun (x,y) -> define_term x y) implemented_case_names_handlers in 
        let* _ = flatmap define_implemented_case_names_handlers in
        let* _ = vernac_ (Vernacexpr.VernacEndSegment modname) in return () in 
  (* let handler_mod_name = freshen_name ~prefix:fname () in  *)
  let handlers_in_mod = (ModTerm (Libnames.qualid_of_lident modname), current_ctx) in
  (* let handlers_in_one_wrapped_mod = 
    let parameters_ = famctx_to_parameters_selfprefix current_ctx in 
    runVernac (wrap_inner_mod handler_mod_name (Libnames.qualid_of_lident modname) parameters_) in 
  let handlers_in_one_wrapped_mod = ModTerm handlers_in_one_wrapped_mod, current_ctx in  *)
  (* let implemented = all_implemented_handler_names in  *)
  (* Now we calculate the motive type, 
     we decide to create another inner_module that store the motive
     that is auxillary_motive_modname *)
  (* let recty = 
    let ModType motive, _ctx = compiled_motive in  
    get_recty_from_motive fname (ModTerm motive, _ctx) 
  in *)
  (* Construct the recursor, also record the context for it *)
  let raw_recursor indref_prepath handler_mod_name cstrnames =
    (* let cstrnames = all_handler_names in  *)
    let the_motive = 
      let motive_base = 
        Libnames.qualid_of_ident (Nameops.add_prefix "__motiveT" fname) in
       _point_qualid_ auxillary_motive_modname motive_base
      in 
    let args = cstrnames in 
    let args = List.map (_qualid_point_ (Some (Libnames.qualid_of_ident handler_mod_name))) args in 
    let args = the_motive :: args in 
    let args = List.map mkRefC args in 
    let indrec_path = 
      let _, indtypename = to_qualid_name (fst indref) in 
      let indrecname = 
      internal_version_name
          (Nameops.add_suffix indtypename postfix) in 
      _qualid_point_ indref_prepath indrecname 
    in 
    (mkAppC (mkRefC indrec_path, args)) in 
  let new_or_extend = 
    if extending then Option.map snd ( top_uninherited_field ()) else None 
    in
  (* deal with the inheritance judgement *)
  ontopinh
  (fun (name, current_inh) ->
    (name, inhnew_or_extend_fthm current_inh fname new_or_extend raw_recursor handlers_in_mod  compiled_motive indref recty all_handler_names wrapped_recty_in_tm));
  claim_goal_info := None


