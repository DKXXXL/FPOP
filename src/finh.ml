open Fenv
open Familytype
open Utils





(* Inherit the following field in the basis
     return the added field name.
*)
let add_one_inherited_field (): name =
  assert_current_has_open_judgement();
  let current_ctx = currentinh_output_ctx () in
  
  let _ = peek inhbasestack in
  (match top_uninherited_field () with 
  | None -> ()
  | Some (fname , _) -> 
    let open Pp in 
    Utils.msg_notice (str "(* Inheriting ..." ++ (Names.Id.print fname) ++ str "*)")); 
  match top_uninherited_field () with 
  | None -> cerror ~einfo:"Nothing To Inherit!" ()
  | Some (fname , ((OvCoqTyWithTerm ({ty = inpty; tm=inptm; dependencies; isopaque; default_retry; tytm; _} as ovty) , oldctx))) ->
    (* first weaken the dependencies *)
    let dependencies = wkinh_dependencies dependencies current_ctx in 
      (* Set_Fieldpath.map (fun p -> fst (wkinh_path (p, ctx) current_ctx)) dependencies  *)
    let check_if_all_dependencies_inherited = 
      let current_inh_info = !inhcontentref in 
      let current_inh_info_withself = List.map (fun (n, k) -> (Nameops.add_prefix "self__" n, k)) current_inh_info in  
      overridable_dependency_check_if_all_inherited current_inh_info_withself (fst dependencies) in 
    (* Past version : directly don't allow if check_if_all_dependencies_inherited =/= true *)
    (* assert_cerror_forced ~einfo:"All dependencies must be inherited to inherit the current field!" (fun _ -> check_if_all_dependencies_inherited); *)
    
    let _ = if check_if_all_dependencies_inherited 
            then 
              (* then do stupid inheritance *)
              ontopinh 
              (fun (parentnanme, parent_inh) ->
                (* TODO: Double check why we do a weakening here, so weird *)
                let inpty = OvCoqTyWithTerm {ovty with dependencies = dependencies}, oldctx  in 
                (parentnanme, inhinhgeneric parent_inh fname ~inpty))
            else
            (
            (* TODO : weaken the untyped stuff in default_retry *)
            match default_retry with 
            | None -> cerror ~einfo:"Fail to Inherit when not all dependencies are inherited" ()
            | Some raw ->
              (* Current Version -- we directly use retry to inherit! *)
              (
                let embedt = 
                  let ov_exposed = Some (fst dependencies) in 
                  CoqVernacUtils.runVernac (embed_tm_using_embedded_tytm fname tytm raw ~ov_exposed current_ctx) in
                  ontopinh 
                  (fun (parentnanme, parent_inh) ->
                    (* TODO: do type checking! i.e. do conversion checking between
                       annotated_type and inpty *)
                    (parentnanme, inhoverride parent_inh fname (ModTerm embedt, current_ctx) tytm ~inptm ~inpty ~dependencies ~new_dependencies:dependencies ~isopaque ~inp_default_retry:default_retry ~default_retry))
            
              ))
      in 
    fname 
    (* for overridable item to be inherited, we must make sure every dependencies are directly inherited *)
  | Some (fname , ((FamTy ( fty, dependencies) , oldctx))) -> 
    (* For family type, we also need to check overridability is feasible*)
    let dependencies = wkinh_paths dependencies current_ctx in 
    let inpty = FamTy (fty, dependencies), oldctx in 
    assert_cerror_forced ~einfo:"All dependencies must be inherited to inherit the current field!" (fun _ -> 
      let current_inh_info = !inhcontentref in 
      let current_inh_info_withself = List.map (fun (n, k) -> (Nameops.add_prefix "self__" n, k)) current_inh_info in  
      overridable_dependency_check_if_all_inherited current_inh_info_withself (Pins (fst dependencies)));
    ontopinh 
    (fun (parentnanme, parent_inh) ->
      (parentnanme, inhinhgeneric parent_inh fname ~inpty));
      fname 
  | Some (fname, inpty) ->
    (* For the rest case, dead-simple inh is enough *)
      ontopinh 
      (fun (parentnanme, parent_inh) ->
        (parentnanme, inhinh_nonfamily parent_inh fname ~postpone_exhaustiveness_checking:false ~inpty));
        fname 
    
(* Check  *)
let add_inherited_fields_until_not_including (fname : name) : unit =
  assert_current_has_open_judgement();
  let (_, (((constructed_input, _), _) , _)) = peek inhcontentref in
    assert_cerror ~einfo:"Fields either already in the context or not inheritable"
      (fun _ ->
        (check_if_field_in_basis fname (peek inhbasestack))
      && ((List.assoc_opt fname (snd constructed_input) = None)));
  let rec repeat_inherits (fname: name) :unit =
    match top_uninherited_field () with 
    | None -> cerror ~einfo:__LOC__ () 
    | Some (fname2, _) ->
      if (fname = fname2) 
      then () 
      else let _ = add_one_inherited_field () in repeat_inherits fname in 
  repeat_inherits fname

let add_inherited_fields_until_and_including (fname : name) : unit = 
  add_inherited_fields_until_not_including fname;
  let _ = add_one_inherited_field () in ()

let inherits_all_remained () : unit =
  assert_current_has_open_judgement();
  let rec repeat_inherits () :unit =
    match top_uninherited_field () with 
    | None -> ()
    | _ -> let _ = add_one_inherited_field () in repeat_inherits () in
  repeat_inherits()


(* This is checking the opposite of the above
    what's more, it will also handles inheritance 
  i.e. if fname exists and not yet extended, then this will inherit until that point *)
let if_allow_extend_field (fname : name) : unit = 
  let errormsg = (Names.Id.to_string fname)^( " hasn't been declared yet (in the parent family), cannot be extended. ")^( __LOC__) in  
  assert_cerror_forced ~einfo:errormsg (fun _ -> not (if_fieldname_totally_new fname));
  let errormsg = (Names.Id.to_string fname)^( " has been defined already, cannot be redefined. ")^( __LOC__) in  
  assert_cerror_forced ~einfo:errormsg (fun _ -> (if_fieldsname_not_defined_yet fname));
  add_inherited_fields_until_not_including fname
