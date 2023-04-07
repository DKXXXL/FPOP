
open Utils
open Ltac_plugin
open FamTyID




open CoqIndSigUtil






let pr_fam_name (n, id) = 
  let open Pp in 
  (Names.Id.print n) ++ (str "[") ++ pr_famtyid id ++ (str "]")

(* Family type will include all the definition
    and our compilation is type-guided so it is fine *)
type family_type_or_coq_type = 
  FamTy of family_type * (Set_Fieldpath.t typed)
  (* the second term intends to be about the ov_exposed
      i.e. the exposed overrifable former terms
      for the current family
     but our famtm_to_mod doesn't need it anymore
      because our famtm_to_mod will directly expose all the overridable definition to compile
     semantically this should be useful when inheriting
      a family with overridability chain from inside to outside
       -- since doing such inheritance will require all dependencies to be inherited (instead of overriden)   
  *)
  | SealedFamTy of {orig : family_type ; sealed : family_type}
  (* This is Legacy code, we will soon remvoe SealedFam *)
  | CoqTy of coqtype
  (* CoqTy is the legacy now  *)
  | CoqTyWithTerm of {tm : coqtype}
  (* CoqTyWithTerm records both definition and type in the context *)
  | OvCoqTyWithTerm of {
      ty : coqtype; 
      (* the type embedded in module type
          also in the form of Parameter (a : T) *)
      tytm : coqtermwN;
      (* the type definition embedded in module
         also in the form of Definition T := .. *)
      tm : coqtype; 
      (* the concrete definition *)
      dependencies : pins_dependencies typed;
      (* it can 
        either store relative path, 
          this should be segment tree but we omit good data structure first 
        or just depends on everything before it (Closing Fact will use this semantic) 
          *)
      isopaque : bool;
      (* if a given term if opaque or not
          if it is opaque (qed'd), then we don't allow other overridable term to depend on it
           *)
      default_retry : rawterm_or_tactics option
      (* 
        during inheritance of a Overriding Term, there will be a failure
          due to the fact the dependencies are overriden
          in those case, the untyped term might be useful for doing "untyped inheritance"   
      *)
      }
  | MetaDataTy of coqtype
  (* Metadata in Coq, can only be inherited, cannot override anything*)

  (* IndCoqTy will introduce a bunch of family type altogether
      (the type and its constructors)
     When overriding, they have to be overrided together
  *)
  | CoqIndTy of 
    { 
      indsigs_from_org_ctx : coq_ind_sigs typed;
      (* original definition *)
      allnames : name list;
      (* all the identifier *)


      (* the compiled abstract interface *)
      compiled_inddefty : coqtype;
      (* the compiled concrete definition *)
      compiled_inddef : coqtype;
      registered_prec : name option ref;
      }
    
  (* Eliminator and Recursor *)
  | RecTy of {
              recursordef : fieldpath; 
              inductivedef : fieldpath;
              (* definitions, a reference pointing to the correct path *)
              postfix : string;
              (* definition : what is the using eliminator *)
              motive : coqterm typed;
              (* compiled definition : include the type of motive *)

              recty : coqtype typed; 
              (* Above info is enough to calculate famtype
                  i.e. staged RecTy info 
                  Following info is used during inheritance *)


              rawrecdef : (family_ctxtype -> rawterm) typed;

              }

  (* computational axiom for recursor 
      it is 2D because it is about 2nd demensional stuff *)
  | Rec2DTy of { recursordef  : fieldpath typed;      
                 inductivedef : fieldpath ; 
                 (* definition : the recursor and inductive definitions *)
                 compiledtype : coqtype typed; 
                 compiledterm : coqterm }
  (* Partial Recursor for a given inductive type
        with only certain number of constructors *)
  | PRecTy  of { inductivedef : fieldpath typed; 
                 cstrs : name list; 
                 precrawty : rawterm typed;
                 (* TODO: use coqtermwN instead so that 
                      we can have automatic weakening for sure *)
                 precty : coqtype;
                 prectm : coqtype }
  | ClosingFactTy of { ty : coqtype; 
                       tytm : coqterm}

  | FTheoremTy of 
      { 
        (* definitions : *)
        indref : fieldpath typed; 
        (* relative path to the inductive type *)
        postfix : string;
        (* the compiled motive *)
        motive : coqtype;



        (* the implemented handlers *)
        all_handlers : name list ;
        (* The final type *)
        recty : coqtype typed;  
      }


  
  
(*          {ty : coqtype; ctx : family_ctxtype} *)
(* Corresponding to vR. {...}; this first name is self_name *)
and family_type = fam_name * ((name * (family_type_or_coq_type)) list) 
(* Each family has a list of field and their type *)


(* We need to record the term and the type *)
and family_ctxtype     = FamCtx of (name * family_type) list 

(* Typed Term/Type is tracking the context where the term/type is well-typed
    make it intrinsic style
  
*)
and 'a typed = 'a * family_ctxtype







(* Pretty Print Functionality *)
let rec pr_family_type_or_coq_type (t :family_type_or_coq_type) : Pp.t =
  let open Pp in 
  match t with 
  | FamTy (ft, _) -> str " { " ++ pr_family_type ft ++ str " }"
  | SealedFamTy {sealed = ft; _} ->  str " Sealed{ " ++ pr_family_type ft ++ str " }"
  | MetaDataTy (ModType t) -> str "MetaData " ++ Libnames.pr_qualid t 
  | CoqTy (ModType t) -> str "CoqTy " ++ Libnames.pr_qualid t  (*Printmod.print_modtype (Nametab.locate_modtype t)*)
  | CoqTyWithTerm {tm = (ModType t); _} -> str "Final-CoqTy " ++ Libnames.pr_qualid t 
  | OvCoqTyWithTerm {ty = (ModType t); _} -> str "NonFinal-CoqTy " ++ Libnames.pr_qualid t  (*Printmod.print_modtype (Nametab.locate_modtype t)*)
  | CoqIndTy {indsigs_from_org_ctx = (t,_); _} -> 
      str @@ "Inductive Defs :[" 
              ^ (List.fold_left (fun h t -> h ^ " , " ^ Names.Id.to_string t) "" (extract_all_ident t)) ^ "]"
  | RecTy {recursordef; _} -> (str "Recursor :") ++ Libnames.pr_qualid recursordef
  (* | FakeRecTy {recursordef; _} -> (str "Not Completed Recursor :") ++ Libnames.pr_qualid recursordef *)

  | Rec2DTy {recursordef; _} -> (str "Computational Axiom for Recursor :") ++ Libnames.pr_qualid (fst recursordef)
  | PRecTy {inductivedef; _} -> (str "Partial Recursor for Inductive Type :") ++ Libnames.pr_qualid (fst inductivedef)
  | ClosingFactTy {ty = (ModType t); _} ->  str "Axiom " ++ Libnames.pr_qualid t
  | FTheoremTy {recty = (ModType t , _); _} -> str "FTheorem " ++   Libnames.pr_qualid t
and pr_family_field ((n, f) : name * (family_type_or_coq_type)) : Pp.t =
  let open Pp in 
  let namep = Names.Id.print n in 
  let fieldp = pr_family_type_or_coq_type f in 
  (* let fctxp = pr_family_ctxtype fctx in  *)
  namep 
  ++ str " = " ++ fieldp 
  (* ++ str " -| " ++ fctxp  *)
and pr_family_field_typed ((n, (f, fctx)) : name * (family_type_or_coq_type typed)) : Pp.t =
  let open Pp in 
  let namep = Names.Id.print n in 
  let fieldp = pr_family_type_or_coq_type f in 
  (* let fctxp = pr_family_ctxtype fctx in  *)
  namep 
  ++ str " = " ++ fieldp 
  (* ++ str " -| " ++ fctxp  *)
and pr_family_type ((fname, t) : family_type) : Pp.t =
  let open Pp in 
  let each_fieldp = List.map pr_family_field t in 
  pr_fam_name fname ++ (str ".{") ++ (List.fold_left Pp.(++) (str " , ") each_fieldp) ++ (str "}")

and pr_family_list (l : (name * family_type) list) : Pp.t =
  let open Pp in 
  let each_print ((n, f) : name * family_type) = 
    Names.Id.print n 
    (* ++ str " := { "
    ++ pr_family_type f 
    ++ str " }"  *)
    ++ str ","
  in 
  let prints = (List.map each_print l) in 
  List.fold_left Pp.(++) (str "") prints
and pr_family_ctxtype (FamCtx f : family_ctxtype) : Pp.t =  
  let open Pp in 
  str "{" ++ pr_family_list f ++ str "}"
and pr_family_type_unfold ( (fname, t) : (fam_name * ((name * (family_type_or_coq_type typed)) list))) : Pp.t = 
  let open Pp in 
  let each_fieldp = List.map pr_family_field_typed t in 
  pr_fam_name fname ++ (str ".") ++ List.fold_left Pp.(++) (str ",") each_fieldp

let pr_list_name l = 
  let open Pp in 
  List.fold_left (fun a b -> a ++ (str ",") ++ b ) (str "") @@ (List.map Names.Id.print) l
  
let unfold_typed_family_type (t : family_type typed) : (fam_name * ((name * (family_type_or_coq_type typed)) list)) typed = 
  let rec unfold_typed_family_type_ (((famname, content), FamCtx ctx) : family_type typed) : (fam_name * ((name * (family_type_or_coq_type typed)) list)) =
  match content with 
  | [] -> ((famname, []))
  | (fdname, fd)::tail -> 
    let fdctx = FamCtx ((fst famname, (famname, tail))::ctx) in 
    let _, tail' = unfold_typed_family_type_ ((famname, tail), FamCtx ctx) in 
    (famname, (fdname, (fd, fdctx))::tail') in 
  let result = unfold_typed_family_type_ t, (snd t) in 
  (* let _ = 
    let open Pp in 
    Utils.msg_notice @@ (pr_family_type (fst t)) ++ (str " unfold -> ") ++ (pr_family_type_unfold (fst result))
  in  *)
  result
    

let fold_typed_family_type ((fname, content) : (fam_name * ((name * (family_type_or_coq_type typed)) list))) : family_type = 
  (fname, List.map (fun (x,(y, z)) -> (x, y)) content)







let famty_ext_ (fty: family_type typed) (fname : name) (t : family_type_or_coq_type) : family_type typed =
  let ftyty, FamCtx ftyctx = fty in
  let famname = fst ftyty in 
  (* let newctx = FamCtx (((fst famname) , ftyty)::ftyctx) in *)
  (famname, ((fname, t)::(snd ftyty))), FamCtx ftyctx


let famty_ext_fam (fty: family_type typed) ov_exposed (fname : name) (t : family_type typed) : family_type typed =
  let tty, FamCtx tctx = t in
  (* TODO: Sanity Check about linkage shape *)
  famty_ext_ fty fname (FamTy (tty, (ov_exposed, FamCtx tctx)))
  (* ((fname, (FamTy tty , FamCtx tctx))::ftyty), ftyctx *)









(* key to implement dynamic binding
    Currently only supporting pointing to top level family   
*)
type family_ref = 
  ToplevelRef of name * ((family_term * family_type) typed) 
  (* {
      famname : name; 
      standaloneftm : family_term typed;
      standalonefty : family_term typed;
     } *)
  (* Points to someone in the top level*)
  (* | RelativeRef of (fieldpath * (family_type_or_coq_type typed))  typed *)
  (* Points to someone in a given context*)

(* Families and Inheritances *)
and family_term_or_coq_term = 
  FamTm of family_term 
  | CompiledDef of coqterm
  | RecDef of (rawterm typed) * coqterm typed
  | ClosingFactProof of coqtype * coqterm * rawterm_or_tactics 
  | FTheoremTm of 
      {
       motive_in_coqtm : coqterm typed;
       (* inductivedef : fieldpath;  *)
       (* relative path to the inductive type *)
       handlers_in_mod : coqterm typed; (* Include all the handlers here *)
       indref : fieldpath typed; (* Store the path reference to the inductive type *)
       raw_recursor_constr : fieldpath option -> name -> name list -> rawterm;
       all_handlers : name list;
      }

  (* any other term is belong to this one
      because those terms doesn't require special treatment *)
  (* | CoqTm of {tm : coqterm; ctx : family_ctxtype} *)
(*          {tm : coqterm; ctx : family_ctxtype} *)
and family_term = (name * (family_term_or_coq_term typed)) list 
(* Each family has a list of field and their type *)
(* For Inheritance Judgement 
    There are three cases -- 
      inheritance,
      override,
      extension
*)
and inh_ty = (family_type * family_type) typed 
(* indicating some kinds of mapping from family_type -> Family_type *)
and inh_op =    CInhInherit  

              (* Extension, 
                 name must be an in-existent name 
                 Field := ..    
              *)
              | CInhNew    of  coqterm typed
              | CInhOverride  of coqterm typed
              
              (* Adding computational axiom 
                  together with the proof that this axiom is correct *)
              | CInhNewAxiom of rawterm_or_tactics
              (* we make rawterm_or_tactics at term level instead of family type level
                  in case future we want to *)


              | CInhNewFam of (family_ref option) * inh
              (* Adding Brandnew Family
                 name must be an non-existent name
                Family ... .   
                The Family might still be inheriting some stuff, but
                it is not using inh+inh judgement, but only inh-ext
                just family version of the above
                Currently only support single Inheritance
              *)
              | CInhExtendInh of  inh
              (* Adding a nested inheritance operation,
                 invoke another inheritance construction interaction
                 name must be an existent name 
                Extended Family ... .
                the family_ref is used to support (dynamic) extending
                Currently only support single Inheritance
                *) 


              (* We will not make the information of the following two fthm related
                  lifted to the family_type
                  they are special because they are the only definition not
                    lifted to the family_type
                  Thus they are not possible to be overridable  *)
              | CInhFThm of {
                  kind : [`New | `Extend ] ;
                  motive : coqterm typed; 
                  compiled_handlers : coqterm typed;
                  rec_cstr : (fieldpath option -> name -> name list -> rawterm); 
                  all_handlers : name list
              }
                  (* the first coqterm typed is the information for motive
                      the second coqterm typed is the information for all the handeler in one module
    
                      this (name -> rawterm) is a raw recursor that
                      parametric on the module name *)
              (* | CInhNewFThm of [`New | `Extend ] * coqterm typed * coqterm typed * (fieldpath option -> name -> name list -> rawterm) * (name list) *)
              (* the first coqterm typed is the information for motive
                  the second coqterm typed is the information for all the handeler in one module

                  this (name -> rawterm) is a raw recursor that
                  parametric on the module name *)
              (* | CInhExtendFThm of coqterm typed * coqterm typed * (fieldpath option -> name -> name list -> rawterm) * (name list)
              (* the first coqterm typed is the information for motive
                  the second coqterm typed is the information for all the handeler in one module *) *)

              
              | CInhExtendInd of coq_ind_sigs typed * coq_ind_sig typed
              (* The first coq_ind_sigs typed includes all the inductive definition
                  the second only include the newly added constructor (like a difference n
                  between current and parent) *)
              (* Add new constructor to an existent inductive type *)

              (* Following is legacy *)
              | CInhOverrideFamily of inh
              (* only allow override family term for a sealed family 
              *)

and inh =   inh_ty * ((name * inh_op) list)
(* An Invariant of inh -- a well typed stuff in 
    (ctx, inp) will also be well-typed in (ctx, oup) *)

(* 
Next we define standalone family as another type
where accept things for FamTm and CoqTm, 
  and a new "InhFamTm of (fam_ref list) * Inh"
        this is indicate dynamic binding, where only when projection happen, the fam_ref's will
          be analyzed and applied to Inh
Each FamilyObject will apply to an Inh to get a new FamilyObject
Only when FamilyObject being translated into Record, then each InhFamTm and FamTm will be analyzed into record
    and CoqTm will still be normal CoqTm
FamilyObject is only for standalone Family
  1. `Family ... (extends ...)` is an Inh judgement
  1.5 once `Family ... (extends ...)` is closed at top level, it will become a FamilyObject data
          so that it can finally correctly be translated into Record 
  2. Record is Coq's Record

The difference between FamilyObject and Inh judgement is that, FamilyObject is 
    an "accumulation" of Inh Judgement, so it doesn't have inhinh, and all the information
    is accumulated.


Further binding is also implementable -- we only consider "small diamond", for example

Family A {
  Family B {..}
}

Family A1 extends A { Family B {..} }
Family A2 extends A { Family B extends A1.B {..}} //  <--- this here is small diamond,
      this means A1.B <: A.B, and A2.B can extends A1.B only when A1.B's DIRECT parent is A.B
      this simplification of further bind makes things easier to implement
      (though it won't be very hard to do INDIRECT parent, but actually I don't see further binding currently used)
*)


let pr_inh_op (i : inh_op) : Pp.t =
  let open Pp in 
  let j = 
      match i with 
      | CInhNew _ ->  "CInhNew"
      (* | CInhNewRec _ ->  "CInhNewRec" *)
      | CInhInherit ->  "CInhInherit"
      (* | CInhInheritRec _ ->  "CInhInheritRec" *)
      | CInhNewFam _ ->  "CInhNewFam"
      | CInhNewAxiom _ -> "CInhNewAxiom"

      (* | CInhNewFThm _ -> "CInhNewFThm" *)
      | CInhExtendInd _ -> "CInhExtendInd"
      | CInhExtendInh _ -> "CInhExtendInh"
      (* | CInhExtendFThm _ -> "CInhExtendFThm" *)
      | CInhFThm {kind = `New; _} -> "CInhNewFThm"
      | CInhFThm {kind = `Extend; _} -> "CInhExtendFThm"
      | CInhOverride _ -> "CInhOverride" 
      | CInhOverrideFamily _ -> "CInhOverrideFamily"
  in str j 

(* let pr_inh (i : inh) : Pp.t = 
  let ((inp, oup), ctx), inhop = i in  *)

let _CACHE_SIZE_ = 64


let rec find_path_in_ctx (famname : fam_name) (newctx : (name * family_type) list) : fieldpath option = 
  match newctx with 
  | [] -> None 
  |  (f, c)::tail -> 
    if famname = (fst c) 
    then (* we found it *) Some (Libnames.qualid_of_ident f)  
    else (* no it is not, we try to dive into this family_type*)
    match find_path_in_famty famname (snd c) with 
    | None -> find_path_in_ctx famname tail 
    | Some tail' -> Some (_point_qualid_ f tail') 
and find_path_in_famty (famname : fam_name) (content : (name * family_type_or_coq_type) list) : fieldpath option = 
    match content with 
    | [] -> None 
    | (n, (FamTy (t, ov_exposed)))::tail -> 
     ( match find_path_in_famty famname (snd t) with 
      | Some tail' -> Some (_point_qualid_ n tail')
      | None -> find_path_in_famty famname tail)
    | (_, _):: tail -> find_path_in_famty famname tail
  



module Dict_Name = Map.Make(Names.Id)

(* Weakening things accross inheritance *)
let wkinh_generic ((t, FamCtx oldctx) : 'a typed) (FamCtx newctx : family_ctxtype) : 'a typed = 
  assert_cerror_forced ~einfo:"Not Expected" (fun _ ->List.length oldctx = List.length newctx);
  (t, FamCtx newctx)
let rec wkinh_family_type_or_coq_type 
(t : family_type_or_coq_type typed) (newctx : family_ctxtype) : family_type_or_coq_type typed = 
  (* TODO: Not necessarily correct...Check it *)
  wkinh_generic t newctx
and wkinh_family_type
  ((t, oldctx) : family_type typed) (newctx : family_ctxtype) : family_type typed = 
  (* TODO: Not necessarily correct...Check it *)
  wkinh_generic (t, oldctx) newctx
and wkinh_coq_module_ref 
(t : modtyperef typed) 
(newctx : family_ctxtype) : modtyperef typed =  wkinh_generic t newctx
and wkinh_coq_type 
(t : coqtype typed) (newctx : family_ctxtype) : coqtype typed =  wkinh_generic t newctx

and wkinh_coq_term
(t : coqterm typed) (newctx : family_ctxtype) : coqterm typed =  wkinh_generic t newctx

and wkinh_path ((q, FamCtx oldctx) : fieldpath typed) (FamCtx newctx : family_ctxtype) 
(* (oldfamname : fam_name) (newfamname : fam_name)  *)
= 
  (* let _ = 
    let open Pp in 
    Utils.msg_notice @@ (str "Finding  ") ++ Libnames.pr_qualid q;
    Utils.msg_notice @@ (str "     in  ") ++ pr_family_ctxtype (FamCtx oldctx);
    Utils.msg_notice @@ (str "     corr  ") ++ pr_family_ctxtype (FamCtx newctx)
  in  *)
  if Libnames.qualid_is_ident q 
    then (q, FamCtx newctx)
    else 
      let ctx_mapping =
        let open Pp in 
        let oldnames = List.map fst oldctx in 
        let newnames = List.map fst newctx in
        let oldnames_with_self = List.map (Nameops.add_prefix "self__") oldnames in
        let newnames_with_self = List.map (Nameops.add_prefix "self__") newnames in  
        let _ = Utils.msg_notice @@ (str "oldnames : ") ++ pr_list_name oldnames in 
        let _ = Utils.msg_notice @@ (str "newnames : ") ++ pr_list_name newnames in
        smap_construct oldnames_with_self newnames_with_self in 
      let head, tail = to_name_qualid q in 
      let einfo =
        let open Pp in 
        Pp.string_of_ppcmds @@ (str " Cannot Find ") ++ (Names.Id.print head) ++ (str " in ") ++ (pr_list_name @@ List.map fst ctx_mapping)
      in
      let newhead = smap_assoc ~einfo:(__LOC__^einfo) head ctx_mapping in 
      let newq = _point_qualid_ newhead tail in 
      let _ = 
        let open Pp in 
        Utils.msg_notice @@ (Libnames.pr_qualid q) ++ (str "  wk->  ") ++ (Libnames.pr_qualid newq)
      in
      (newq, FamCtx newctx)

and wkinh_inh (i : inh) (newctx : family_ctxtype) : inh = 
  let ((inp, oup), ctx),content = i in 
  let inp, _ = wkinh_family_type (inp, ctx) newctx in 
  let oup, _ = wkinh_family_type (oup, ctx) newctx in 
  ((inp, oup), newctx), content

and wkinh_paths ((dependencies, ctx) : Set_Fieldpath.t typed) (newctx : family_ctxtype) =
Set_Fieldpath.map (fun p -> fst (wkinh_path (p, ctx) newctx)) dependencies, newctx

and wkinh_dependencies ((dependencies, ctx) : pins_dependencies typed) (newctx : family_ctxtype) = 
  match dependencies with 
  | PinsEverything -> (PinsEverything, newctx)
  | Pins dep -> let k, newctx = wkinh_paths (dep, ctx) newctx in (Pins k, newctx)


let self_version_name (n : name) =
  Names.Id.of_string ("self__" ^ (Names.Id.to_string n))


(* THis is replacing path root
   which is always trying to replace self__XX to self__YY 
   thus to make things simple, it is not yet capture-avoiding subst
   TODO: fix it to become capture avoiding subst *)
let replace_qualid_root ctx_mapping =
  let open Constrexpr_ops in 
  let open Constrexpr in 
  let open Libnames in 
  let take_root_of_path (t : qualid) : Names.Id.t =
    fst (to_name_qualid t) in
  let replace_root_of_path (t : qualid) (nr : Names.Id.t) : qualid =
    let _, tail = to_name_qualid t in 
    _point_qualid_ nr tail in
  (* Copy and paste from repla ce_vars_constr_expr
      repla ce_vars_constr_expr doesn't seem to have good  *)
  let rec replace_qualid_path _ r =
    match r with
    | { CAst.loc; v = CRef (qid,us) } as x when (not (qualid_is_ident qid))  ->
        (* rename the  *)
      (match Dict_Name.find_opt (take_root_of_path qid) ctx_mapping with 
      | Some new_root -> 
          let qid = replace_root_of_path qid new_root in 
            CAst.make (CRef (qid, us))
      | None -> x
      )
    | cn -> map_constr_expr_with_binders (fun _ _ -> ()) replace_qualid_path () cn in 
  replace_qualid_path ()

let rename_ind_cstr_ctx 
      (((coer, (id, t)), FamCtx ctx) : Vernacexpr.constructor_expr typed) (FamCtx nctx : family_ctxtype) 
      : Vernacexpr.constructor_expr typed =
  assert_cerror ~einfo:"Context Doesn't Match!" (fun _ ->List.length ctx = List.length nctx);
  let ctx_mapping = 
    smap_construct (List.map fst ctx) (List.map fst nctx) in
  let ctx_mapping =
    List.fold_left 
      (fun d (k,v) ->
          Dict_Name.add (self_version_name k) (self_version_name v) d
        ) Dict_Name.empty ctx_mapping in 
  ( (coer, (id, replace_qualid_root ctx_mapping t)) , FamCtx nctx)

let rename_ind_cstrs_ctx  
  ((t, ctx) : Vernacexpr.constructor_expr list typed) (nctx : family_ctxtype) 
  : Vernacexpr.constructor_expr list typed =
  let t_s = List.map (fun x -> rename_ind_cstr_ctx (x, ctx) nctx) t in 
  (List.map fst t_s, nctx)
(* Note : it only change the first level *)
let wkinh_indsigs ((parent_ind_trace, FamCtx oldctx) : coq_ind_sigs typed) (FamCtx newctx : family_ctxtype) : coq_ind_sigs typed
 =  
 let parent_ind =   List.hd parent_ind_trace in
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> List.length parent_ind = 1);
    (* No mutual inductive type *)
    let parent_ind = List.hd parent_ind in 
    (* don't allow notation *)
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> snd parent_ind = []);
    (* sanity check on newcstrs *)
    let ((wtc, (old_name, univinfo)), oldparams, oldty, oldcstrs) = fst parent_ind in 
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> oldparams = ([],None));
    let newcstrs = 
      match oldcstrs with 
      | Vernacexpr.Constructors a -> 
        let a, _ = rename_ind_cstrs_ctx (a, FamCtx oldctx) (FamCtx newctx) in
        Vernacexpr.Constructors a
      | _-> cerror ~einfo:("Expect Inductive Constructor!"^__LOC__) () 
    in 
    let ctx_mapping = 
      let ctx_mapping = 
        smap_construct (List.map fst oldctx) (List.map fst newctx) in
      let ctx_mapping =
        List.fold_left 
          (fun d (k,v) ->
              Dict_Name.add (self_version_name k) (self_version_name v) d
            ) Dict_Name.empty ctx_mapping in  ctx_mapping in
    let newty = Option.map (replace_qualid_root ctx_mapping) oldty
    in
    (* type of child_ind = type of (fst parent_ind) *)
    let child_ind = ((wtc, (old_name, univinfo)), oldparams, newty, newcstrs) in 
    let child_ind_def = ([(child_ind, [])]) in 
    (child_ind_def::List.tl parent_ind_trace, (FamCtx newctx))
    
let wkinh_indsig (a,ctx : coq_ind_sig typed) (b : family_ctxtype) : coq_ind_sig typed = 
  match (wkinh_indsigs ([a], ctx) b) with 
  | t::[], ctx -> (t, ctx)
  | _ -> cerror ~einfo:__LOC__ ()

let wkinh_rawterm ((t, FamCtx oldctx) : rawterm typed) (FamCtx newctx : family_ctxtype) : rawterm typed = 
  let ctx_mapping =
    let oldnames = List.map fst oldctx in 
    let newnames = List.map fst newctx in
    let oldnames_with_self = List.map (Nameops.add_prefix "self__") oldnames in
    let newnames_with_self = List.map (Nameops.add_prefix "self__") newnames in  
    smap_construct oldnames_with_self newnames_with_self in 
  let ctx_mapping =
    List.fold_left 
      (fun d (k,v) ->
          Dict_Name.add k v d
        ) Dict_Name.empty ctx_mapping
  in 
  replace_qualid_root ctx_mapping t, FamCtx newctx

  

(* Real Constructor at below -- maintaining typed information *)
let empty_inh (basename : fam_name) (famname : fam_name) (ctx: family_ctxtype) : inh =
  (((basename, []), (famname, [])), ctx), []


let seal_famty ((famname, content) : family_type) : family_type =
  let _seal_famty (content : (name * (family_type_or_coq_type))) = 
    match content with 
    | fname, CoqTy h -> (fname, CoqTy h)
    | _ -> cerror ~einfo:("Don't Support Other Than Field "^__LOC__) () in 
  (famname, List.map _seal_famty content)



(* Checking if t is typed in
    Γ, 𝓜σ ⊢ t : ...
  where Γ = ctxfctx, σ = fty
  by directly looking the context it resides
*)

(* 
*********************************   
Following are inheritance helper 
*********************************
*)



let inhinhgeneric  
  ?(oupty = (None : family_type_or_coq_type typed option))
  (i : inh) (fname : name)
  ~(inpty : family_type_or_coq_type typed) 
  : inh = 
  (* let (t, tctx) = inpty in  *)
  let ((inp, oup), FamCtx ctx), inhs = i in 
  (* TODO: Sanity Check about linkage shape *)
  let newinhs = (fname, CInhInherit)  :: inhs in 
  let (newinp, _) = famty_ext_  (inp, FamCtx ctx) fname (fst inpty) in 
  (* let outctx = FamCtx (((fst (fst oup)), oup) :: ctx) in  *)
  (* It is just weakened in some *)
  let fst_oupty = 
    match oupty with 
    | None -> fst inpty 
    | Some k -> fst k 
  in
  let (newoup, _) = famty_ext_  (oup, FamCtx ctx) fname fst_oupty in
  ((newinp, newoup), FamCtx ctx), newinhs



let inh_internal
  ?(inpty = (None : family_type_or_coq_type typed option))
  ~(oupty : family_type_or_coq_type)
  (i : inh) (fname : name) (iop : inh_op)
  : inh = 
  (* let (t, tctx) = inpty in  *)
  let ((inp, oup), FamCtx ctx), inhs = i in 
  (* deal with inputty first *)
  let newinp = 
    match inpty with 
    | None -> inp 
    | Some inpty -> 
      (* TODO: Sanity Check about linkage shape *)
      let (newinp, _) = famty_ext_  (inp, FamCtx ctx) fname (fst inpty) in newinp
  in 
  let (newoup, _) = famty_ext_  (oup, FamCtx ctx) fname (oupty) in
  let newinhs = (fname, iop)  :: inhs in 
  ((newinp, newoup), FamCtx ctx), newinhs


(* let inhinhfthm (i : inh) (fname : name) motive indref all_handlers postfix recty : inh =
  let ((inp, oup), FamCtx ctx), inhs = i in 
  (* let oldctx = FamCtx ((fname, inp)::ctx) in  *)
  let newctx = FamCtx (((fst (fst oup)), oup)::ctx) in  
  (* TODO : make context correct for motive, indref, recty *)
  let newinhs = (fname, CInhInherit)  :: inhs in 
  let theftm = FTheoremTy {motive; indref; all_handlers; postfix; recty} in
  let newftm = 
    (* let motive = wkinh_coq_type  motive newctx in  *)
    let indref = wkinh_path indref newctx in
    let recty  = wkinh_coq_type  recty newctx in 
    FTheoremTy {motive; indref; all_handlers; postfix; recty} in
  let (newinp, ctxa) = famty_ext_  (inp, FamCtx ctx) fname theftm in 
  (* TODO : Check it is well-typed *)
  let (newoup, ctxb) = famty_ext_ (oup, FamCtx ctx) fname newftm in
  ((newinp, newoup), FamCtx ctx), newinhs  *)



(* Extend the output with a new term
    this term will need to be typed in the output
*)
let inhnew_or_extend_fthm (i : inh) (fname : name) 
  (parent_type : family_type_or_coq_type typed option)
  rec_constr
  (handlers_in_one_mod : coqterm typed) 
  (motive : coqtype)
  indref ?(postfix="_ind_comp") recty all_handlers 
  (motive_in_coqtm : coqterm typed)
  : inh = 
  (* let (_, tctx) = handlers_in_one_mod          in  *)
  (* let (_, tctx_) = motive         in  *)
  (* assert_cerror ~einfo:"Type and its term unmatched" (fun _ ->tctx = tctx_); *)
  (* TODO: check t is really of type tT *)
  let ((inp, oup), ctx), inhs = i in 
  (* TODO: Sanity Check about linkage shape *)
  let newinhs = 
      let has_parent = 
        match parent_type with 
        | None -> `New 
        | Some _ -> `Extend in 
      let cinh_info = 
        CInhFThm {kind = has_parent; 
                  motive = motive_in_coqtm; 
                  compiled_handlers = handlers_in_one_mod;
                  rec_cstr = rec_constr;  all_handlers;} in 
      (fname , cinh_info) :: inhs in
  let newinp= 
        match parent_type with 
        | None -> inp
        | Some (p, _) ->  fst @@  famty_ext_ (inp, ctx) fname p in  
  let (newoup, ctxb) = famty_ext_  (oup, ctx) fname (FTheoremTy {motive; indref; all_handlers; postfix; recty}) in 

  assert_cerror ~einfo:"Context Should not change" (fun _ ->ctx = ctxb); 
  ((newinp, newoup), ctx), newinhs
  



(* extend nested inheritance
    First Check that inner is in the ctx of
    i's context and i's input

    precondition -- orgbase is the original form of the inner's base (input type)
    we can weaken the orgbase to get inner's base(input type)
Recall the rule for inh+inh
  -- inh+inh :
  --   → (h : Inh Γ σ₁ σ₂) 
  --   {→ (τ₁ : Sig (Γ, 𝓛σ₁') T₁) → (τ₂ : Sig (Γ, 𝓛σ₂') T₂)}
  --   → Inh (Γ, 𝓛σ₂') (τ₁[(p₁, ⇡s)]) τ₂  <--- this one will shift/weaken τ₁
  --   → Inh Γ (v+ σ₁ (𝓛 τ₁) s) (v+ σ₂ (𝓛 τ₂) s)
      τ₁ is org base; τ₁[(p₁, ⇡s)] is lifted version
    *)
let inhextendinh  (i : inh) (fname : name) (orgbase : family_type typed) ?(ov_exposed = (Set_Fieldpath.empty)) (inner : inh) : inh =
  let (((inneri, innero), FamCtx innerctx), inner_s) = inner in 
  (* inner : Inh innerctx inneri innero *)
  let (((ii, io), FamCtx i_ctx), i_s) = i in

  (* assert_cerror ~einfo:"Incorrect inner context"  *)
  (* TODO: Sanity Check about linkage shape *)
  (* TODO: weakening! *)
  let newii, _ = famty_ext_fam (ii, FamCtx i_ctx) ov_exposed fname orgbase in 
  let newio, _ = famty_ext_ (io, FamCtx i_ctx) fname (FamTy (innero,(ov_exposed, FamCtx i_ctx))) in 
  let newinhs = (fname, CInhExtendInh ( inner))::i_s in 
  ((newii, newio), FamCtx i_ctx), newinhs



(* Currently only supports standalone family *)
let inhnewfam (i : inh) (fname : name) ?(is_sealing = false) ?(ov_exposed = (Set_Fieldpath.empty)) (inner : inh) : inh =
  let (((inneri, innero), FamCtx innerctx), inner_s) = inner in 
  (* inner : Inh innerctx inneri innero *)
  assert_cerror ~einfo:"NonNested Family Needs empty inneri" (fun _ -> snd inneri = []);
  (* Not Necessary in the future, we can have standalone *)
  
  let (((ii, io), FamCtx i_ctx), i_s) = i in

  (* assert_cerror ~einfo:"Incorrect inner context"  *)
  (* TODO: Sanity Check about linkage shape *)
  let newii    = ii in 
  let innero = 
    if is_sealing then 
      let sealed = seal_famty innero in
      SealedFamTy {orig = innero; sealed} 
    else FamTy (innero, (ov_exposed, FamCtx i_ctx)) 
  in 
  let newio, _ = famty_ext_ (io, FamCtx i_ctx) fname innero in 
  let newinhs = (fname, CInhNewFam (None, inner))::i_s in 
  ((newii, newio), FamCtx i_ctx), newinhs


let inhoverridefam (i : inh) (fname : name) (inner : inh) (orgbase : family_type typed)  ?(ov_exposed = (Set_Fieldpath.empty))(sealed : family_type) : inh =
  let (((inneri, innero), FamCtx innerctx), inner_s) = inner in 
  (* inner : Inh innerctx inneri innero *)
  assert_cerror ~einfo:"NonNested Family Needs empty inneri" (fun _ -> snd inneri = []);
  (* Not Necessary in the future, we can have standalone *)
  
  let (((ii, io), FamCtx i_ctx), i_s) = i in

  (* assert_cerror ~einfo:"Incorrect inner context"  *)
  (* TODO: Sanity Check about linkage shape *)
  let newii, _ = famty_ext_fam (ii, FamCtx i_ctx) ov_exposed fname orgbase in 
  let newio, _ = famty_ext_ (io, FamCtx i_ctx) fname (SealedFamTy {orig = innero; sealed}) in 
  let newinhs = (fname, CInhOverrideFamily ( inner))::i_s in 
  ((newii, newio), FamCtx i_ctx), newinhs

let inhnew  (i : inh) (fname : name) 
  ~(newinhop : inh_op) ~(newoupty : family_type_or_coq_type typed) = 
  let ((inp, oup), ctx), inhs = i in 
  (* TODO: Sanity Check about linkage shape *)
  let newinhs = (fname , newinhop) :: inhs in 
  let (newoup, ctxb) = famty_ext_ (oup, ctx) fname (fst newoupty) in 
  assert_cerror ~einfo:"Context Should not change" (fun _ ->ctx = ctxb); 
  ((inp, newoup), ctx), newinhs



let inhoverride (i : inh) (fname : name) (typedt : coqterm typed) (tytm : coqtermwN) ~(inptm : coqtype) ~(inpty : coqtype) ~dependencies ~new_dependencies ~isopaque ~inp_default_retry ~default_retry : inh =
  let ((inp, oup), FamCtx ctx), inhs = i in 
  let (ModTerm t, tctx) = typedt          in 
  (* TODO: check t is really of type tT *)

  (* assert_cerror ~einfo:"Incorrect typedt context"  *)
  (* TODO: Sanity Check about linkage shape *)
  let newinhs = (fname, CInhOverride (ModTerm t, tctx)) :: inhs in
  let (newinp, _) = famty_ext_  (inp, FamCtx ctx) fname (OvCoqTyWithTerm {tm = inptm; ty = inpty; dependencies; isopaque; default_retry = inp_default_retry; tytm }) in 
  let (newoup, ctxb) = famty_ext_ (oup, FamCtx ctx) fname (OvCoqTyWithTerm {tm = (ModType t); ty = inpty; dependencies = new_dependencies; isopaque; default_retry; tytm}) in 
  ((newinp, newoup), FamCtx ctx), newinhs
  (* nonimplement ~moreinfo:__LOC__ () *)
(* 

We need a "type checking" algorithm to 
    verify a given inh = inh_ty * inh_op is valid
1. check_inh_valid

We need an interactive procedure to construct inh in general, 
thus we need several data structure.
We decided to construct Inh all the time, because
 a standalone family is just Inh without input family of empty type
2. 


We need a function that can transform a given Inh and a Family
into the inherited family
3. apply_inh : inh -> family_term -> family_term


*)




type family_contenttype = (name * family_term) list

(* let familyctxref = Summary.ref ~name:"FamCtx" ([] : family_ctxtype) *)
let familycontentref = Summary.ref ~name:"FamContent" ([] : family_contenttype)




(* There are three ways to add new family
    NonNested corresponds to use inhnewfam (directly adding a family nested in an exsitent family, but the added family is not children of any)
    
    Nested corresponds to extending existent family (inside a family) (using inh extendinh)

    InitialInhBase corresponding adding a new standalone family, may still has parent

    InitialOnMixedInh stands for an inheritance based on a mixin inheritance judgement,
  Check close_current_inh_judgement for details

*)
type nested_or_not_inhbase = 
      | NonNested of family_ref option * (Set_Fieldpath.t typed)
      | InitialOnMixedInh of inh * family_ref * fam_name
      (* family_ref is the parent family of inh *)
      | InitialInhBase of family_ref option
(* Only supports single inheritance now *)
      | Nested of  {shifted : (family_type typed); orig : (family_type typed); ov_exposed : Set_Fieldpath.t typed}

      (* : ({shifttype : family_type, originaltype : familytype} list) *)
      | OverrideBase of { expected_final : family_type typed ; orig : (family_type typed)}
      (* Used for overriding a family, and seal as a interface, final is the expected resulting type 
        note this expected_final is the output type in output ctx
          (already wkinh_...)   
      *)


(* This reference records 
1. the base type that the current inheritance judgement is based on
2. Also the original, unweakened base

Recall the rule for inh+inh
  -- inh+inh :
  --   {(σ₁ : Sigₙ Γ S₁) → (σ₂ : Sigₙ Γ S₂) }
  --   → (h : Inh Γ σ₁ σ₂) 
  --   {→ (τ₁ : Sig (Γ, 𝓛σ₁') T₁) → (τ₂ : Sig (Γ, 𝓛σ₂') T₂)}
  --   → (⇡s : Tms (Γ,(𝓛 σ₂')) (𝓛 σ₁')[p₁])
  --   → Inh (Γ, 𝓛σ₂') (τ₁[(p₁, ⇡s)]) τ₂  <--- this one will shift/weaken τ₁
  --   {→ s ∉ S₁ → s ∉ S₂}
  --   → Inh Γ (v+ σ₁ (𝓛 τ₁) s) (v+ σ₂ (𝓛 τ₂) s)

basically shifted = τ₁[(p₁, ⇡s)]; original = τ₁ 
*)




(* A switch to control if flatten or not
  when compile to Coq, if no flatten, then recursor cannot
    locate at the different level of nested family as the target
    inductive type, but it does have better/nested hierachy

  *)
let default_compile_flatten = false
let is_rec_handler s = 
  (* TODO: we use adhocly a name to decide if it is a handler
      and we don't faltten handlers *)
  (String.ends_with ~suffix:"handler" s) ||
  (String.ends_with ~suffix:"cases" s) ||
  (String.ends_with ~suffix:"internal" s)

let check_if_flattern (fname : name) = 
  let fname = Names.Id.to_string fname in 

  (not (is_rec_handler fname)) && default_compile_flatten

let empty_path : fieldpath = Libnames.qualid_of_ident (Names.Id.of_string "_____") (* 5 blanks*)

(* Filter out from the set of paths that not starting from prefix
    and remove the prefix and get a new set  *)
let filter_prefix (prefix : name) (paths : Set_Fieldpath.t) =
  let paths = 
    Set_Fieldpath.map (fun path -> 
      let (prefix_path, remained_path) = to_name_optionqualid path
      in let remained_path = match remained_path with None -> empty_path | Some x -> x  in 
      if (Names.Id.compare prefix_path prefix) = 0 then 
      remained_path else empty_path   
      ) paths in 
  Set_Fieldpath.remove empty_path paths


(* each family type requiring famctx will be 
    a functor
  a parametrized module type 
  ov_exposed must be absolute path
  *)
  
let famty_to_modsig_open_rec 
  famty_to_modsig
  famctx_to_parameters
  ((ov_exposed, current_path, all_exposed, ftyctx) : Set_Fieldpath.t * fieldpath * bool * (family_type typed))  
  : modtyperef = 
  let famctx_to_parameters_selfprefix ov_exposed all_exposed (FamCtx f : family_ctxtype)  : (name * module_expr) list = 
      let _ = 
        let open Pp in 
        let s = Set_Fieldpath.fold (fun p s -> ((Libnames.pr_qualid p))++(str ";")++ s) ov_exposed (str "")  in 
        Utils.msg_notice s 
      in 
      let f = 
        let prefixit n = Names.Id.of_string @@ "self__" ^ (Names.Id.to_string n) in
        List.map (fun (n,m) -> (prefixit n, m)) f in
      famctx_to_parameters (ov_exposed,all_exposed,(FamCtx f)) in 
  let famty_to_modsig_constr ((fty, fctx) : family_type typed) : modtyperef = 
    let fty, fctx = unfold_typed_family_type  (fty, fctx) in 
    let open CoqVernacUtils in 
    match fty with
    | _, [] -> let parameters = famctx_to_parameters (ov_exposed,all_exposed, fctx) in 
            runVernac @@ 
              define_moduletype (fresh_name ~prefix:"EmptySig" ()) parameters (fun _ -> return () )
    | selfname, (fname, (h, hctx))::t -> 
      let newmodname = freshen_name ~prefix:fname () in
      (* let this_field_path = _qualid_point_ (Some current_path) fname in  *)
      let former_sig = 
        famty_to_modsig (ov_exposed, current_path, all_exposed, ( (fold_typed_family_type (selfname, t)), fctx)) in
      (* we use the ability of include "self"
            from the include command
            i.e. non-instantiated parameter in the functor by include
              will directly be instantiated by the current defining module
        *)
      match h with
      | FamTy (innerfty, _) 
      | SealedFamTy {sealed = innerfty; _} ->
        let inner_sig = 
          (* let ov_exposed = filter_prefix fname ov_exposed in  *)
          let current_path = _qualid_point_ (Some current_path) fname  in
          famty_to_modsig (ov_exposed,current_path,all_exposed,(innerfty, hctx)) in 
        let parameters = famctx_to_parameters (ov_exposed,all_exposed,fctx) in 
        let vernac = 
          if check_if_flattern fname then 
            define_moduletype newmodname parameters 
              (fun ctx ->
                let applied_prior = apply_mods (pure former_sig) ctx in 
                let* _ = include_mod applied_prior in 
                let applied_inner_sig = apply_mods (pure inner_sig) ctx in 
                let* res = include_mod applied_inner_sig in 
                  return res
              )
          else 
            let inner_sig_parameters = famctx_to_parameters (ov_exposed,all_exposed, hctx) in 
            let* wrapped_inner_sig = wrap_modtype_into_module_modtype fname inner_sig inner_sig_parameters in 
            define_moduletype newmodname parameters 
            (fun ctx ->
              let applied_prior = apply_mods (pure former_sig) ctx in 
              let* _ = include_mod applied_prior in 
              let applied_inner_sig = apply_mods (pure wrapped_inner_sig) ctx in 
              let* res = include_mod applied_inner_sig in 
                return res
            ) in 
          let res = runVernac vernac in 
          res

      (* | CoqIndTy {compiled_inddef = termty; _}  *)
      | ClosingFactTy {ty = (termty); _}
      | Rec2DTy { compiledtype = termty, _; _ }
      | MetaDataTy termty 
      | FTheoremTy {recty = (termty, _); _} 
      | CoqTyWithTerm {tm = termty; _}
      | CoqTy termty ->
        let ModType tymodref = termty in 
        let parameters = famctx_to_parameters (ov_exposed,all_exposed, fctx) in 
        let res = 
          runVernac @@ 
          define_moduletype newmodname parameters 
          (fun ctx ->
            let applied_prior = apply_mods (pure former_sig) ctx in 
            let* _ = include_mod applied_prior in 
            let applied_current_field = apply_mods (pure tymodref) (ctx) in 
            let* _ = include_mod applied_current_field in  
              return ()
          ) in res    

      | CoqIndTy {compiled_inddefty = ty; compiled_inddef = termty; _} 
      | PRecTy {precty = ty; prectm = termty; _}
      | OvCoqTyWithTerm {tm = termty; ty ; _} ->
        (* compile using two ways -- 
            if current path is in ov_exposed then use termty
            o/w using ty *)
        let ModType tymodref = 
          let current_path = _qualid_point_ (Some current_path) fname in 
          let _ = 
            let open Pp in 
            let s = Set_Fieldpath.fold (fun p s -> ((Libnames.pr_qualid p))++(str ";")++ s) ov_exposed (str "")  in
            
            Utils.msg_notice @@ (str "current_path: ") ++ Libnames.pr_qualid current_path;
            Utils.msg_notice @@ (str "ov_exposed: ") ++ s;
            let ModType k = termty in 
            Utils.msg_notice @@ (str "termty is ") ++ Libnames.pr_qualid k;
          in 
          match Set_Fieldpath.find_opt current_path ov_exposed with 
          | _ when all_exposed -> termty
          | None ->  
            let _ = 
              let open Pp in 
              Utils.msg_notice @@ (str "Cannot find current_path in ov_exposed");
            in 
            ty 
          | Some _ -> termty in 
        let parameters = famctx_to_parameters (ov_exposed,all_exposed, fctx) in 
        let res = 
          runVernac @@ 
          define_moduletype newmodname parameters 
          (fun ctx ->
            let applied_prior = apply_mods (pure former_sig) ctx in 
            let* _ = include_mod applied_prior in 
            let applied_current_field = apply_mods (pure tymodref) (ctx) in 
            let* _ = include_mod applied_current_field in  
              return ()
          ) in res 
      (* This following legacy code was for the intermediate state of recursor during mixin *)
      (* | FakeRecTy {recty = ((ModType tymodref), _); _} ->
          let exposed_def = 
            let current_path = _qualid_point_ (Some current_path) fname in 
            match Set_Fieldpath.find_opt current_path ov_exposed with 
            | _ when all_exposed -> true
            | None ->  false 
            | Some _ -> true in  
          assert_cerror_forced ~einfo:("Currently not supporting exposed recty"^__LOC__) (fun _ -> not exposed_def);
          let parameters = famctx_to_parameters ~ov_exposed ~all_exposed fctx in 
          (* we need to compile rawterm in the ctx first *)
          let res = 
            runVernac @@ 
            define_moduletype newmodname parameters 
            (fun ctx ->
              let applied_prior = apply_mods (pure former_sig) ctx in 
              let* _ = include_mod applied_prior in 
              let content_mod = tymodref in 
              let applied_current_field = apply_mods (pure content_mod) (ctx) in 
              let* _ = include_mod applied_current_field in  
                return ()
            ) in res     *)
      | RecTy {recty = ((ModType tymodref), _); motive = (ModTerm motive), _; rawrecdef; _} -> 
        let exposed_def = 
          let current_path = _qualid_point_ (Some current_path) fname in 
          match Set_Fieldpath.find_opt current_path ov_exposed with 
          | _ when all_exposed -> true
          | None ->  false 
          | Some _ -> true in  
        let newmodname2 = freshen_name ~prefix:fname () in
        let typed_recdef () = 
          let rawterm, rawsctx = rawrecdef in 
          let itsparameter = famctx_to_parameters_selfprefix ov_exposed all_exposed rawsctx in
          runVernac @@ 
          define_module (newmodname2) itsparameter 
          (fun ctx ->
            (let applied_motive = 
              apply_mods (pure motive) ctx in 
            let* _ = include_mod applied_motive in 
            let* _ = define_term fname (rawterm rawsctx) in  
              return ())
            )
        in 
        let typed_recdef = 
          (* evaluate typed_recdef based on exposed_def *)
          if exposed_def then 
            let res = typed_recdef () in fun () -> res 
          else fun () -> cerror ~einfo:("NOT_SUPPOSED_TO_HAPPEN"^__LOC__) () in
        let parameters = famctx_to_parameters (ov_exposed,all_exposed, fctx) in 
        (* we need to compile rawterm in the ctx first *)
        let res = 
          runVernac @@ 
          define_moduletype newmodname parameters 
          (fun ctx ->
            let applied_prior = apply_mods (pure former_sig) ctx in 
            let* _ = include_mod applied_prior in 
            let content_mod = 
              if exposed_def then typed_recdef () else tymodref in 
            let applied_current_field = apply_mods (pure content_mod) (ctx) in 
            let* _ = include_mod applied_current_field in  
              return ()
          ) in res    
      (* | _ -> nonimplement ~moreinfo:__LOC__ () *)
    in 
    let newv = famty_to_modsig_constr ftyctx in 
      newv

(* 
      every ctx has to be standalone telescope
  all_exposed = true will expose all the 
*)
let famctx_to_parameters_open_rec
famty_to_modsig
famctx_to_parameters
((ov_exposed, all_exposed, fctx) : Set_Fieldpath.t * bool * family_ctxtype)
  : (name * module_expr) list = 
    let famctx_to_parameters_constr (FamCtx fctx : (family_ctxtype))  : (name * module_expr) list = 
      match fctx with 
      | [] -> []
      | (fname, h)::t ->
        
        let prior = famctx_to_parameters (ov_exposed, all_exposed, (FamCtx t)) in 
        let current_family = 
          (* we need to go in one level *)
          (* let ov_exposed = filter_prefix fname ov_exposed in  *)
          let current_path = Libnames.qualid_of_ident fname in 
          famty_to_modsig (ov_exposed, current_path, all_exposed, (h, FamCtx t)) in 
        let all_prior_parameters = 
          List.map (fun (n, _) -> Libnames.qualid_of_ident n) prior in 
          prior @ [(fname, apply_mods (pure current_family) all_prior_parameters)] in 
  let newv = famctx_to_parameters_constr fctx in 
    newv


let (famty_to_modsig, famctx_to_parameters) = 
  let open CCCache in 
  let ty2mod2sig, ctx2param = CCCache.with_cache_rec2 (lru ~eq:(fun a b -> (Stdlib.compare a b) = 0)  (_CACHE_SIZE_*2)) famty_to_modsig_open_rec famctx_to_parameters_open_rec in 
  let famty_to_modsig 
    ?(ov_exposed = (Set_Fieldpath.empty : Set_Fieldpath.t)) 
    ?(current_path = (empty_path : fieldpath)) 
    ?(all_exposed = false)
    (ftyctx : family_type typed) 
    = ty2mod2sig (ov_exposed,current_path,all_exposed, ftyctx) in 
  let famctx_to_parameters
      ?(ov_exposed = (Set_Fieldpath.empty : Set_Fieldpath.t)) 
      ?(all_exposed = false)
      (fctx : family_ctxtype) = ctx2param (ov_exposed, all_exposed, fctx) in 
  famty_to_modsig, famctx_to_parameters



(* 
      every ctx has to be standalone telescope
*)


  


let famctx_to_parameters_selfprefix ?(ov_exposed = (Set_Fieldpath.empty : Set_Fieldpath.t)) ?(all_exposed=false) (FamCtx f : family_ctxtype)  : (name * module_expr) list = 
  let _ = 
    let open Pp in 
    let s = Set_Fieldpath.fold (fun p s -> ((Libnames.pr_qualid p))++(str ";")++ s) ov_exposed (str "")  in 
    Utils.msg_notice s 
  in 
  let f = 
    let prefixit n = Names.Id.of_string @@ "self__" ^ (Names.Id.to_string n) in
    List.map (fun (n,m) -> (prefixit n, m)) f in
  famctx_to_parameters ~ov_exposed ~all_exposed (FamCtx f)


let famctx_to_parameters_selfprefix2 (ov_exposed : pins_dependencies option) (FamCtx f : family_ctxtype)  : (name * module_expr) list = 
  match ov_exposed with 
  | None -> famctx_to_parameters_selfprefix (FamCtx f)
  | Some (Pins ov_exposed) ->
    famctx_to_parameters_selfprefix ~ov_exposed (FamCtx f) 
  | Some PinsEverything -> famctx_to_parameters_selfprefix ~all_exposed:true (FamCtx f) 

let construct_term_using_rawterm_or_proof (fname : name) (rawproof : rawterm_or_tactics) (type_dec : rawterm) () : unit CoqVernacUtils.vernacWriter =
  let open CoqVernacUtils in 
  match rawproof with 
  | RawTerm rawproof -> define_term fname ~eT:(Some type_dec) rawproof
  | ProofScript {script = pfs; opacity = opaque; starting_plain = is_starting_plain} -> 
    let interppfs = Tacinterp.interp pfs in 
    (* Construct proof for it *)
    let env = Global.env () in
    let evd = Evd.from_env env in
    let (evd, type_checked_goal) = Constrintern.interp_constr_evars env evd type_dec in 
    let _ = 
      let open Pp in 
      Utils.msg_notice @@ (str "(* Closing Fact : ") ++ 
      Names.Id.print fname ++ (str " : ") ++
      pr_econstr type_checked_goal ++ (str "  *)")
    in
    let info = Declare.Info.make () in
    let cinfo =
      Declare.CInfo.make ~name:fname ~typ:type_checked_goal () in 
    let proof = Declare.Proof.start ~info ~cinfo evd in 
    let proof =
       (* apply unfold if not starting_plain  *)
        if is_starting_plain then proof else 
        let unfold_all_definition = 
            let open Tacexpr in 
            let open Genredexpr in 
            let open Locus in 
            let tac = TacAtom (TacReduce (Cbv (Redops.make_red_flag [FDeltaBut []]) , {onhyps = None; concl_occs = AllOccurrences })) in 
            let intp_tac = Tacinterp.interp (CAst.make tac) in 
            intp_tac
          in 
          let (unfolded_proof, _) = Declare.Proof.by unfold_all_definition proof in 
        unfolded_proof
    in 
    let (proof, _ ) = Declare.Proof.by interppfs proof in 
    (* let opaque = Vernacexpr.Opaque in  *)
    let _ = Declare.Proof.save_regular ~proof ~opaque ~idopt:None in
    return ()


(* each family term requiring famctx will be 
    a functor
    a parametrized module 
  we will return such parametrized module
  *)
let famterm_to_mod_open_rec famterm_to_mod  (famtyped : family_term typed)  : modtermref = 
  let _, FamCtx ctx = famtyped in 
  let open CoqVernacUtils in 
  let rec famterm_internal_include ((fam, fctx) : family_term typed) : modtyperef list -> unit vernacWriter = 
    match fam with 
    | [] -> fun _ -> return ()
    | (fname, (h, hctx))::t -> 
      (match h with 
      | FamTm (innerftm) -> 
        if check_if_flattern fname 
        then 
          (* then we don't recurse but directly go inside and compile stuff *)
          fun ctx -> 
            let* _ = famterm_internal_include (t, fctx) ctx in 
            let* _ = famterm_internal_include (innerftm, hctx) ctx in 
            return ()
        else 
          let inner_mod = famterm_to_mod (innerftm, hctx) in 
          let inner_mod = runVernac @@ wrap_inner_mod fname inner_mod (famctx_to_parameters ~all_exposed:true hctx) in 
          fun ctx -> 
            let* _ = famterm_internal_include (t, fctx) ctx in 
            let applied_inner  = apply_mods (pure inner_mod) ctx in 
            let* _ = include_mod applied_inner in 
            return ()
      | CompiledDef termmod ->
        let ModTerm tmmodref = termmod in
        fun ctx ->
          let* _ = famterm_internal_include (t, fctx) ctx in 
          let applied_current_field = apply_mods (pure tmmodref) ctx in 
          let* _ = include_mod applied_current_field in  
          return ()
      | RecDef (typedrawterm, ((ModTerm motive), _)) ->
        let typed_recdef = 
          let rawterm, rawsctx = typedrawterm in 
          let itsparameter = famctx_to_parameters_selfprefix ~all_exposed:true rawsctx in
          runVernac @@ 
          define_module (freshen_name ~prefix:fname ()) itsparameter 
          (fun ctx ->
            (let applied_motive = 
              apply_mods (pure motive) ctx in 
            let* _ = include_mod applied_motive in 
            let* _ = define_term fname rawterm in  
              return ())
            )
        in
        fun ctx ->
          let* _ = famterm_internal_include (t, fctx) ctx in 
          let applied_rec = apply_mods (pure typed_recdef) ctx in 
          let* _ = include_mod applied_rec in 
          (* let* _ = define_term fname rawterm in   *)
            return ()
      | FTheoremTm {motive_in_coqtm; handlers_in_mod; raw_recursor_constr; all_handlers; indref } ->
        let ModTerm handlers_in_mod, thectx = handlers_in_mod in 
        let ModTerm motive_in_coqtm, _ = motive_in_coqtm in 
        let (_, modname) = to_qualid_name handlers_in_mod in
        let modname = freshen_name ~prefix:modname () in
        (* wrap the handlers *)
        let wrapped_handlers = 
          runVernac @@
          wrap_inner_mod modname handlers_in_mod (famctx_to_parameters_selfprefix thectx) in 
        let newmodname2 = freshen_name ~prefix:fname () in
        (* compiled untyped recursor *)
        let typechecked_rec = 
          let indrec_prepath, _ = to_qualid_name (fst indref) in 
          let rawrec = raw_recursor_constr indrec_prepath modname all_handlers in 
          (* weaken the rawrec *)
          let itsparameter = famctx_to_parameters_selfprefix ~all_exposed:true hctx in 
          runVernac @@
          define_module newmodname2 itsparameter 
          (fun ctx ->
            let applied_motive_mod = apply_mods (pure motive_in_coqtm) ctx in 
            let* _ = include_mod applied_motive_mod in 
            let applied_handlers = apply_mods (pure wrapped_handlers) ctx in 
            let* _ = include_mod applied_handlers in 
            let* _ = define_term fname rawrec in return ()
            )
        in 
        fun ctx ->
          let* _ = famterm_internal_include (t, fctx) ctx in 
          let* _ = include_mod (apply_mods (pure typechecked_rec) ctx) in 
            return ()
      | ClosingFactProof (tty, (ModTerm rawterm_type), rawproof) -> 
        fun ctx ->
          let* _ = famterm_internal_include (t, fctx) ctx in 
          let applied_type_decoration = apply_mods (pure rawterm_type) ctx in
          let* _ = include_mod applied_type_decoration in 
          let type_dec = Constrexpr_ops.mkIdentC (Nameops.add_suffix fname "__type") in
          let* () = thunk (construct_term_using_rawterm_or_proof fname rawproof type_dec)  in
          return ()
      ) in 
let famterm_to_mod_constr ((fam, fctx) : family_term typed) : modtermref = 
(* TODO: check existence in the cache! *)
  let content_interpreted = famterm_internal_include (fam, fctx) in 
  let parameters = famctx_to_parameters ~all_exposed:true fctx in 
  runVernac @@ 
  define_module (fresh_name ()) parameters content_interpreted  in
    let newv = famterm_to_mod_constr famtyped in 
      newv
let famterm_to_mod = 
  let open CCCache in 
  with_cache_rec (lru ~eq:(fun a b -> (Stdlib.compare a b) = 0)  _CACHE_SIZE_) famterm_to_mod_open_rec 




let standalone_famterm_to_mod (ftmtyped : family_term typed)  : modtermref =
  let _, FamCtx ctx = ftmtyped in 
  assert_cerror ~einfo:"Only Support Standalone Family Now" 
    (fun _ ->ctx = []);
  famterm_to_mod ftmtyped




(* TODO: Implement it! *)
(* fam_rename is when constructing inh judgement, we are using different name
    for parent and children *)
(* TODO: Compared to wkinh_path, what is the difference? *)
let rec wk_coq_module_ref 
  ((t, FamCtx oldctx) : modtyperef typed) 
  (FamCtx newctx : family_ctxtype) 
  (* ( fam_rename : (fam_name, fam_name) smap) *)
  : modtyperef typed =
  (* we walk through each used family inside oldctx
    then recover their path inside new_ctx
    List.rev is used because out context is reversed    
  *)
  (* (t, FamCtx newctx) *)
  (* let fam_rename = Dict_FamName.add_seq (List.to_seq fam_rename) Dict_FamName.empty in  *)
  let each_using_famnames = List.map (fun x -> fst (snd x)) @@ List.rev oldctx in 
  (* self__.. might be renamed in children *)
  (* let each_using_famnames = 
    List.map (fun x -> 
      match Dict_FamName.find_opt x fam_rename with 
      | None -> x 
      | Some y -> y 
      ) each_using_famnames in  *)
  (* let _ = 
    (* let open Pp in  *)
    Utils.msg_notice @@ pr_family_ctxtype (FamCtx oldctx);
    Utils.msg_notice @@ pr_family_ctxtype (FamCtx newctx);
  in  *)
  let each_using_paths = List.map (fun x -> 
    match find_path_in_ctx x newctx with 
    | None -> 
      let open Pp in 
      let ctxinfo = List.fold_left (++) (str "") @@ List.map (fun (_, (n, _)) ->  (pr_fam_name n)) newctx in 
      let dbginfo = (str "Couldn't Find ") ++ (pr_fam_name x) ++ (str " in ") ++ ctxinfo ++ (str "  ") ++ (str __LOC__)  in
      cerror ~einfo:(Pp.string_of_ppcmds dbginfo) ()
    | Some j -> j) each_using_famnames in 
  let each_using_paths_with_self = 
    List.map (fun x -> 
        let head, tail = to_name_optionqualid x in
        let newhead = (Nameops.add_prefix "self__") head in 
        match tail with 
        | None -> Libnames.qualid_of_ident newhead
        | Some tail -> _point_qualid_ newhead tail 
        ) each_using_paths in 
  (* Now we can construct the module *)
  let newt = 
    let newbasename = freshen_name ~prefix:(Libnames.qualid_basename t) () in 
    let parameters = famctx_to_parameters_selfprefix (FamCtx newctx) in
    let open CoqVernacUtils in 
    runVernac @@ 
    define_module newbasename parameters 
    (fun ctx -> 
      let applied_mods = apply_mods (pure t) each_using_paths_with_self in 
      include_mod applied_mods
      )  in 
  (newt , FamCtx newctx)
and wk_coq_type 
 (((ModType t), oldctx) : coqtype typed) (newctx : family_ctxtype) 
 (* ( fam_rename : (fam_name, fam_name) smap) *)
 : coqtype typed = 
    let (t, newctx) = wk_coq_module_ref (t,oldctx) newctx  in 
    (ModType t, newctx)
  
and wk_coq_term
 ((ModTerm t, oldctx) : coqterm typed) (newctx : family_ctxtype)
 (* ( fam_rename : (fam_name, fam_name) smap)  *)
 : coqterm typed = 
  let (t, newctx) = wk_coq_module_ref (t,oldctx) newctx  in 
  (ModTerm t, newctx)


(* BUG : this following is simply broken *)
and wk_path 
  ((q, FamCtx oldctx) : fieldpath typed) (FamCtx newctx : family_ctxtype) : fieldpath typed = 
  (* Now we go through each famname to find their qualid *)
    let _ = 
      let open Pp in 
      Utils.msg_notice @@ (str " Weakening") ++ (Libnames.pr_qualid q);
      Utils.msg_notice @@ (str "  From ") ++ (pr_family_ctxtype (FamCtx oldctx));
      Utils.msg_notice @@ (str "  To ") ++(pr_family_ctxtype (FamCtx newctx))
    in 
  if Libnames.qualid_is_ident q 
  then (q, FamCtx newctx)
  else 
    let head, tail = to_name_qualid q in 
    (* head has self as front *)
    let head = 
      assert_cerror ~einfo:"Path Should Start With self__" (fun _ ->String.starts_with ~prefix:"self__" (Names.Id.to_string head));
      let beginning = Names.Id.to_string head in 
      let newbeginning = String.sub beginning (String.length "self__") ((String.length beginning) - (String.length "self__")) in 
      Names.Id.of_string newbeginning 
    in

    let headfamname, _ = smap_assoc ~einfo:__LOC__ head oldctx in 
    let newpath_without_self = 
    match find_path_in_ctx headfamname newctx with 
    | None -> cerror ~einfo:("Unexpected Error! Unfound Path") () 
    | Some newhead -> (_qualid_qualid_ newhead tail) in 
    let newpath_with_self =
      let head, tail = to_name_qualid newpath_without_self in 
      let head = Nameops.add_prefix "self__" head in 
      _point_qualid_ head tail in 
    (newpath_with_self, FamCtx newctx)

   

let get_family_ty_in_famref (fref : family_ref) : family_type typed =
  match fref with
  | ToplevelRef (_, ((_, fty), ctx)) -> (fty, ctx)
  (* | RelativeCtx (_,res) -> res *)

(* an inh base is just a family type
   but we have different format of inh base
   so we need this function to return the formatted family type *)
let get_family_ty_in_inhbase (famname : fam_name) ((basis, ectx) : nested_or_not_inhbase typed) : family_type typed =
  match basis with
  | NonNested ((Some fref), _) ->  (get_family_ty_in_famref fref)
  | InitialInhBase (Some fref) ->  (get_family_ty_in_famref fref)
  | InitialOnMixedInh (i, _, _)   ->  
    let (((_, outty), ctx) , _) = i in
    outty, ctx
  | Nested {shifted = res; _} -> res
  | OverrideBase _ -> nonimplement ~moreinfo:__LOC__ ()
  | _ -> ((famname, []), ectx)
  (* this final one includes non-parental stuff *)
 
  (* | _ -> ((famname, []), ectx) *)


let inhbasestack = 
    Summary.ref 
    ~name:"InhBaseStack" 
    ([] : nested_or_not_inhbase list)
(* let ctx_assumption_enabled = Summary.ref ~name:"CtxAssumptions" (false : bool) *)

(* let family_ctx_section_name = "family_ctx_section" *)






(* This function will translate a recursor type to the product of its recursor handlers 
  For example
  (P : K -> Prop) -> (a1 : ... -> P k1) -> (a2 : ... -> P k2) -> (a3 : ... -> P k3) .. -> P k 
  transform into 
  a dictionary 
  { a1 : fun (P : K -> Prop) -> (a1 : ... -> P k1);
    a2 : fun (P : K -> Prop) -> (a2 : ... -> P k2); ..
  }
  fun (P : K -> Prop) -> (a1 : ... -> P k1) x (a2 : ... -> P k2) x (a3 : ... -> P k3) ... (no (P k))
*)
let from_recursor_type_to_subcase_handlers_constructor (cstname : name list) (recursor : rawterm) 
    : (name, rawterm) smap =  
  let open Constrexpr in 
  let open Constrexpr_ops in 
  let isDepProd {CAst.v = t; _} = match t with | CProdN _ -> true | _ -> false in
  let isArrow {CAst.v = t; _} = match t with | CNotation (_, (_, "_ -> _"), _) -> true | _ -> false in
  let destDepProd {CAst.v = t; _} = 
    match t with 
    | CProdN (al, b) -> assert_cerror (fun _ ->List.length al = 1); (al, b)
    | _ -> cerror () in 
  let destArrow {CAst.v = t; _} = 
    match t with 
    | CNotation (_ ,(_, "_ -> _"), ([domain; codomain], _, _, _)) -> (domain, codomain) 
    | _ -> cerror ~einfo:__LOC__ () in
  assert_cerror (fun _ ->isDepProd recursor);
  let _inputP, _body = destDepProd recursor in 
  let rec collect_handler (cstname : name list) (f : rawterm) : rawterm * (rawterm list) =
    match cstname, f with 
    | h :: t, f when (isArrow f) -> 
        let currentT, remained_f = destArrow f in
        let ret, otherparts = collect_handler t remained_f in 
        ret, (currentT :: otherparts)
    | [], f -> f, []
    | _, _ -> cerror ~einfo:__LOC__ ()
    in 
  let _, all_recursor_handlers = collect_handler cstname _body in 
  let cst_name_corresponding_recursor_handlers_sig =
    smap_construct cstname 
      (* decorate each ai case with a _inputP *)
      (List.map (fun body -> mkLambdaCN _inputP body) all_recursor_handlers) in 
  cst_name_corresponding_recursor_handlers_sig

type local_binder_expr_assume = Names.lname list * Constrexpr.binder_kind * rawterm

(* return a list of 
    1. arguments/parameters
    2. the rawterm representing each argument/parameter 
*)
let collect_argument_and_ret_of_lambda (f : rawterm) : (((local_binder_expr_assume) * rawterm) list) * rawterm =
  let open Constrexpr in 
  let open Constrexpr_ops in 
  let isLambda {CAst.v = t; _} = match t with | CLambdaN _ -> true | _ -> false in
  (* let isArrow {CAst.v = t; _} = match t with | CNotation (_, (_, "_ -> _"), _) -> true | _ -> false in *)
  let destLambda {CAst.v = t; _} = 
    match t with 
    | CLambdaN (al, b) -> assert_cerror (fun _ ->List.length al = 1); (al, b)
    | _ -> cerror () in 
  let give_name ({CAst.v = n; _} : Names.lname) : name =
    match n with 
    | Names.Anonymous -> fresh_name ~prefix:"arg" ()
    | Names.Name n -> n in 
  let local_binders_to_list_of_local_binder 
    (e : local_binder_expr) : (local_binder_expr_assume * rawterm) list  = 
    match e with 
    | CLocalAssum (l, k, b) -> 
      List.map (fun x -> 
                  let x = give_name x in 
                    ([CAst.make (Names.Name x)], k, b), 
                    mkRefC (Libnames.qualid_of_ident x) ) l  
    | _ -> cerror ~einfo:__LOC__ () 
    in
  let ret : rawterm option ref = ref None in 
  let rec collect_argument (f : rawterm) : (((local_binder_expr_assume) * rawterm) list) =
    match f with 
    | f when (isLambda f) ->
      let parameters, body = destLambda f in 
      let all_parameters = List.map local_binders_to_list_of_local_binder parameters in 
      let all_parameters = List.flatten all_parameters in 
      all_parameters @ (collect_argument body)
    | x -> 
      ret := (Some x);
      []
    in 
  let res = collect_argument f in 
  match !ret with 
  | None -> cerror ~einfo:("UNEXPECTED"^__LOC__) ()
  | Some res2 -> (res, res2)

  let collect_argument_and_ret_of_type (f : rawterm) : (((local_binder_expr_assume) * rawterm) list) * rawterm =
    let open Constrexpr in 
    let open Constrexpr_ops in 
    let isDepProd {CAst.v = t; _} = match t with | CProdN _ -> true | _ -> false in
    let isArrow {CAst.v = t; _} = match t with | CNotation (_, (_, "_ -> _"), _) -> true | _ -> false in
    let destDepProd {CAst.v = t; _} = 
      match t with 
      | CProdN (al, b) -> assert_cerror (fun _ ->List.length al = 1); (al, b)
      | _ -> cerror () in 
    let destArrow {CAst.v = t; _} = 
      match t with 
      | CNotation (_ ,(_, "_ -> _"), ([domain; codomain], _, _, _)) -> (domain, codomain) 
      | _ -> cerror ~einfo:__LOC__ () in
    let give_name ({CAst.v = n; _} : Names.lname) : name =
      match n with 
      | Names.Anonymous -> fresh_name ~prefix:"arg" ()
      | Names.Name n -> n in 
    let local_binders_to_list_of_local_binder 
      (e : local_binder_expr) : (local_binder_expr_assume * rawterm) list  = 
      match e with 
      | CLocalAssum (l, k, b) -> 
        List.map (fun x -> 
                    let x = give_name x in 
                      ([CAst.make (Names.Name x)], k, b), 
                      mkRefC (Libnames.qualid_of_ident x) ) l  
      | _ -> cerror ~einfo:__LOC__ () 
      in
    let ret : rawterm option ref = ref None in 
    let rec collect_argument (f : rawterm) : (((local_binder_expr_assume) * rawterm) list) =
      match f with 
      | f when (isDepProd f) ->
        let parameters, body = destDepProd f in 
        let all_parameters = List.map local_binders_to_list_of_local_binder parameters in 
        let all_parameters = List.flatten all_parameters in 
        all_parameters @ (collect_argument body)
      | f when (isArrow f) -> 
        let domain, codomain = destArrow f in 
        let newname = fresh_name ~prefix:"arg" () in 
        let binder = (([CAst.make (Names.Name newname)], Default Glob_term.Explicit, domain)) in 
        (binder, mkRefC (Libnames.qualid_of_ident newname))::collect_argument codomain 
      | x -> 
        ret := (Some x);
        []
      in 
    let res = collect_argument f in 
    match !ret with 
    | None -> cerror ~einfo:("UNEXPECTED"^__LOC__) ()
    | Some res2 -> (res, res2)
  
(* a functional r will be lead to 
    forall ..., (r ..) = (r ..)
    and do type check
  then we return 
  [forall ...] and [r ..]
*)
let fully_applied (r : rawterm) : (((local_binder_expr_assume) * rawterm) list) * rawterm =
  (* let open Constrexpr in  *)
  let open Constrexpr_ops in 
  let typeofr = reflect_safeterm @@ type_check r in 
  let all_binders_and_args = fst @@ collect_argument_and_ret_of_type typeofr in
  let all_args = List.map snd all_binders_and_args in 
  (* let eq_cstr = Coqlib.lib_ref "core.eq.refl" in *)
  let fully_applied_r = mkAppC (r, all_args) in 
  let _ = 
    (* sanity type checking *)
    (* Now we construct (r ...) = (r ...) and wrap with universal quanitifer *)
    let eq_cstr = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "eq" in 
    let id_on_fully_applied_r =  mkAppC (eq_cstr, [fully_applied_r;fully_applied_r]) in  
    let all_binders = List.map fst all_binders_and_args in 
    let res = List.fold_right (fun (a, b, c) body -> mkProdC (a,b,c, body)) all_binders id_on_fully_applied_r in 
    type_check res in 
  (all_binders_and_args, fully_applied_r)
  





let internal_version_name (n : name) =
  Nameops.add_prefix "__internal_" n

let uninternal_version_name (n : name) =
  let nstr = Names.Id.to_string n in 
  let prefix = "__internal_" in 
  assert_cerror_forced ~einfo:__LOC__ (fun _ -> String.starts_with ~prefix nstr);
  let newnstr = String.sub nstr (String.length prefix) (String.length nstr - String.length prefix)  in 
  Names.Id.of_string newnstr


(* This is only used in one place where we make every recursor handler has 
    to have an appropriate path refer to it
    we haven'y encounter problem but it is not yet capturea-avoiding subst
    TODO: fix it into capture avoiding subst
    *)
let replace_var_with_rawterm_in_constr ctx_mapping = 
  let open Constrexpr_ops in 
  let open Constrexpr in 
  let open Libnames in 
  let rec replace dict r =
    match r with
    | { CAst.loc; CAst.v = CRef (qid,us) } as x when (qualid_is_ident qid)  ->
        (* rename the  *)
      let _, key = repr_qualid qid in 
      (match Dict_Name.find_opt key dict with 
      | Some found -> 
          found
      | None -> x
      )
    | cn -> map_constr_expr_with_binders (fun n dict -> Dict_Name.remove n dict ) replace dict cn in  
  replace ctx_mapping

(* given a constructor, we calculate the injection proposition for it *)
let compute_cstr_injection_prop (r : rawterm) : rawterm = 
  let open Constrexpr_ops in 
  let params1, applied_r1 = fully_applied r in 
  let args1 = List.map snd params1 in 
  let second_name x = (Nameops.add_suffix x "2") in 
  let params1 = List.map fst params1 in 
  (* get variable (name) from params *)
  let get_vars (l : local_binder_expr_assume list) = 
    List.map (fun (t,_,_) -> 
      assert_cerror_forced ~einfo:("Unexpected"^__LOC__) (fun _ -> List.length t = 1);
      let t = List.hd t in (* We are sure*)
      match t.CAst.v with 
      | Names.Anonymous -> cerror ~einfo:("Unexpected Error, not supposed to be anonymous "^__LOC__) ()
      | Names.Name x -> x
      ) l
  in 
  (* we do substitution *)
  let subst_mapping = 
    let paramvars = get_vars params1 in 
    let newnames = List.map (fun x -> 
      mkRefC @@ Libnames.qualid_of_ident (second_name x)) paramvars in 
    let mapping = 
      let zipped = List.combine paramvars newnames in 
      Dict_Name.add_seq (List.to_seq zipped) Dict_Name.empty in 
    mapping
  in 
  let applied_r2 = replace_var_with_rawterm_in_constr subst_mapping applied_r1  in 
  (* make implicit *)
  let params1 = 
    let for_each ((n, _, ty) : local_binder_expr_assume) : local_binder_expr_assume = 
      (n, Default Glob_term.MaxImplicit, ty) in 
      List.map for_each params1 in
  let params2 = 
    let for_each ((n, _, ty) : local_binder_expr_assume) : local_binder_expr_assume = 
      let n = List.map (fun x -> 
        let x = match x.CAst.v with 
        | Names.Anonymous -> Names.Anonymous
        | Names.Name x -> Names.Name (second_name x) in 
        CAst.make x 
        ) n in 
      let ty = replace_var_with_rawterm_in_constr subst_mapping ty in 
    (n, Default Glob_term.MaxImplicit, ty) in 
    List.map for_each params1 in 
  (* we wrap params2 to get args2 *)
  let args2 = 
    List.map (fun (t,_,_) -> 
      assert_cerror_forced ~einfo:("Unexpected"^__LOC__) (fun _ -> List.length t = 1);
      let t = List.hd t in (* We are sure*)
      match t.CAst.v with 
      | Names.Anonymous -> cerror ~einfo:("Unexpected Error, not supposed to be anonymous "^__LOC__) ()
      | Names.Name x -> mkRefC @@ Libnames.qualid_of_ident x
      ) params2 in 
  (* now we construct equalities between applies*)
  let eq_cstr x1 x2 = 
    let eqterm =  mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "eq" in 
    mkAppC (eqterm, [x1;x2]) in 
  let applied_r12 = eq_cstr applied_r1 applied_r2 in 
  let args12 = List.map2 (fun x1 x2 -> eq_cstr x1 x2) args1 args2 in 
  (* now we fold args12 into a bunch of conjunction *)
  let conj l r = 
    mkAppC (mkIdentC (Names.Id.of_string "and"), [l; r])
  in 
  let __True = mkIdentC (Names.Id.of_string "True") in
  let args12 = List.fold_right conj args12 __True  in 
  (* then we construct applied_r12 -> args12  *)
  let applied_r12_args12 = 
    mkProdC ([CAst.make (Names.Anonymous)] , Default Glob_term.Explicit, applied_r12, args12) in 
  let all_binders = params1 @ params2 in 
  let res = List.fold_right (fun (a, b, c) body -> mkProdC (a,b,c, body)) all_binders applied_r12_args12 in 
  res

(* generate injection prop signature
    only be used in the context *)
let generate_injection_propsig 
  all_cstr_name : unit CoqVernacUtils.vernacWriter = 
  (* setup the context, and well-know the explicit definition of indref *)
  let open CoqVernacUtils in 
  let for_each cstr_name = 
    let cstr_path = 
      Libnames.qualid_of_ident cstr_name in 
    let defname = Nameops.add_suffix cstr_name "__injective" in 
    let cstr_term = Constrexpr_ops.mkRefC cstr_path in 
      let cstr_ty = compute_cstr_injection_prop cstr_term in 
      assume_parameter defname cstr_ty
  in 
  thunk @@ fun () -> flatmap (List.map for_each all_cstr_name)

let is_sort (t : rawterm) : bool =
  match t.v with 
  | Constrexpr.CSort _ -> true 
  | _ -> false 


let inductive_to_famtype =
  
  let inductive_to_famtype (typed_indsigs : coq_ind_sigs typed) : modtyperef =
  (* we only use the complete inherited indsig in this function *)
  let constr_inductive_to_famtype_toplevel ((indsig, ctx) : coq_ind_sig typed) : modtyperef =
    let indcstrs = List.map (fun (x,_) -> extract_type_and_cstrs x) indsig in 
    (* Collect all their name and their types *)
    let remove_option ( ((x,y) ,csts) : ((name * rawterm option) * ((name * rawterm) list))) = 
      (x, Option.get y), csts in 

    let indcstrs = List.map remove_option indcstrs in 
    let typedecls = List.map fst indcstrs in 
    (* currently only when mutual inductive type (not type family)  *)
    let if_generate_injprop : bool = 
      List.for_all (
        fun ((_, t)) -> 
          match t.CAst.v with 
          | Constrexpr.CSort _ -> true 
          | _ -> false 
      ) typedecls in 
    let modname = freshen_name ~prefix:(fst @@ List.hd typedecls) () in
    let cstsdecls = List.concat_map snd indcstrs in 
    let open CoqVernacUtils in 
    let declare_typedecls = List.map (fun (x,y) -> assume_parameter x y) typedecls in 
    let declare_csts_decls = List.map (fun (x,y) -> assume_parameter x y) cstsdecls in 
    let all_decls = declare_typedecls @ declare_csts_decls in 
    runVernac @@ 
      define_moduletype modname (famctx_to_parameters_selfprefix ctx)
        (fun _ -> 
          let* () =  flatmap all_decls in 
          let* () = 
            if if_generate_injprop then
            generate_injection_propsig (List.map fst cstsdecls) 
            else return () in 
          return ()
        )
        (* TODO, also add the partial recursor *)
  
  in 
  let top_typed_ind_sig = (List.hd (fst typed_indsigs), snd typed_indsigs) in 
  constr_inductive_to_famtype_toplevel top_typed_ind_sig 

  (* TODO : add the precursor inside *)
  in
  let open CCCache in 
  with_cache (lru ~eq:(fun a b -> (Stdlib.compare a b) = 0)  _CACHE_SIZE_) inductive_to_famtype 




let replace_in_rawterm pred replacingf = 
  let open Constrexpr_ops in 
  (* let open Constrexpr in  *)
  (* let open Libnames in  *)
  let rec replace _ r =
    match r with
    |  x when (pred x)  ->
        (* rename the  *)
        replacingf x
    | cn -> map_constr_expr_with_binders (fun _ _ -> ()) replace () cn in  
  replace ()


(* given an inductive type, we will use generate_cstr_injection_term on each of its constructor
    and compiled into a module 
  currently this function is used together with   
  *)
let generate_injection_prooftms 
  all_cstr_name : unit CoqVernacUtils.vernacWriter = 
  (* first get the inductive type itself *)
  (* setup the context, and well-know the explicit definition of indref *)
  let postulate = 
    let script : Tacexpr.raw_tactic_expr = 
      (CAst.make (Tacexpr.TacArg (Tacexpr.TacCall (CAst.make ( Libnames.qualid_of_ident (Names.Id.of_string "__cheat") ,[]))) )) in 
    ProofScript {script; starting_plain = false; opacity = Vernacexpr.Opaque} in 
  let open CoqVernacUtils in  
  let for_each cstr_name = 
    let cstr_path = 
      Libnames.qualid_of_ident cstr_name in 
    let defname = Nameops.add_suffix cstr_name "__injective" in 
    let cstr_term = Constrexpr_ops.mkRefC cstr_path in 
      let cstr_ty = compute_cstr_injection_prop cstr_term in 
      construct_term_using_rawterm_or_proof defname postulate cstr_ty () 
  in 
  thunk @@ fun () -> flatmap (List.map for_each all_cstr_name)


(* Construct inductive type wrapped in module
    then record the recursor type --
    but record the sub-goals of recursor type, 
    TODO: also generate recursor for each sort 
  return compiled recursor and recursor handler as well    
*)

let inductive_to_famterm_and_recursor_type =
let inductive_to_famterm_and_recursor_type (typed_indsigs : coq_ind_sigs typed) : 
    modtermref * ((string, (coqterm typed * ( (name, coqterm typed) smap ))) smap)  = 
  (* we only use the complete inherited indsig in this function *)
  (* 1. Collect all the name and add a "internal" in front of it *)
  let generated_recursor_type : (string, rawterm) smap ref = ref [] in
  let collect_recursor_in_current_coqenvironment (inddefname : name) () : unit CoqVernacUtils.vernacWriter = 
    let possible_suffix = ["_ind"; "_ind_comp"; "_rec"; "_rect"] in 

    let for_each_suffix suf = 
      let recursor_name = Nameops.add_suffix (internal_version_name inddefname) suf in 
      
      match Constrintern.is_global recursor_name with 
      | false -> ()
      | true ->
        let recursor_name = Libnames.qualid_of_ident recursor_name in 
        let the_recursor = Constrexpr_ops.mkRefC recursor_name in 
        let the_typ =  type_check the_recursor in 
        let the_typ = reflect_safeterm the_typ in 
        (* rename the internal_... back to normal name *)
        let all_names = extract_all_ident (fst typed_indsigs) in 
        let all_newnames = List.map internal_version_name all_names in 
        (* 2. Construct map and corresponding substitution for it *)
        let assoc_newname_oldname = smap_construct all_newnames all_names in
        let map_newname_oldname = List.fold_right (fun (k,v) map -> Names.Id.Map.add k v map) assoc_newname_oldname Names.Id.Map.empty in 
        let the_typ = Constrexpr_ops.replace_vars_constr_expr map_newname_oldname the_typ in 
        generated_recursor_type := (suf, the_typ)::(!generated_recursor_type)
      (* then we check if this recursor name is in the environment *)
    in 
    let _ = List.map for_each_suffix possible_suffix in 
    CoqVernacUtils.return () in
  let indcstrs = List.map (fun (x,_) -> extract_type_and_cstrs x) @@ List.hd @@ fst typed_indsigs in 
    (* 1. Collect all the name and add a "internal" in front of it *) 
  let all_cstrnames = List.concat_map (fun (_, y) -> List.map fst y) indcstrs in

  let constr_inductive_to_famterm_toplevel ((indsig, ctx) : coq_ind_sig typed)  = 
    let indcstrs = List.map (fun (x,_) -> extract_type_and_cstrs x) indsig in 
    let if_generate_injprop : bool = 
      let type_decl_sort = List.map (fun ((_, t), _) -> Option.get t) indcstrs in 
      List.for_all (
        fun t -> 
          match t.CAst.v with 
          | Constrexpr.CSort _ -> true 
          | _ -> false 
      ) type_decl_sort in 
    (* 1. Collect all the name and add a "internal" in front of it *)
    let all_original_type_names = List.map (fun ((x,_),_) -> x) indcstrs in 
    let typename = List.hd all_original_type_names in 
    let all_names = List.map (fun ((x,_),y) -> x :: (List.map fst y)) indcstrs in 
    let all_names = List.concat all_names in 
    let indsigname = List.hd all_names in  
    let all_newnames = List.map internal_version_name all_names in 
    (* 2. Construct map and corresponding substitution for it *)
    let associated_name_newname = smap_construct all_names all_newnames in 
    let map_name_newname = List.fold_right (fun (k,v) map -> Names.Id.Map.add k v map) associated_name_newname Names.Id.Map.empty in 
    let subst = Constrexpr_ops.replace_vars_constr_expr map_name_newname in 
    (* 3. Apply subst to corresponding places, and renaming all the constructors and types *)
    let open Vernacexpr in 
    let each_apply_subst ((((a1, (a21,a22)), b, c,d), y) : inductive_expr * decl_notation list) : inductive_expr * decl_notation list =
      let a21 = CAst.map internal_version_name a21 in 
      let c = Option.map subst c in 
      match d with 
      | Constructors csts ->
        let csts = List.map (fun (z,(x, y)) -> (z, (CAst.map internal_version_name x, subst y))) csts in 
        let d = Constructors csts in 
        (((a1, (a21,a22)), b, c,d), y)
      | _ -> cerror ~einfo:"Expect Constructors" () 

    in 
    let modified_indcstrs =  List.map each_apply_subst indsig in 
    (* 4. construct export mapping, for example, 
            tm : Set := __internal_tm *)
    let allname_typedecl = List.concat_map (fun ((x,y),z) -> (x, Option.get y) :: z) indcstrs in 
    let alias_all_name_term_type_decl = 
        List.map 
          (fun (n, ty) -> 
              (n, Constrexpr_ops.mkIdentC (internal_version_name n) , ty)) 
          allname_typedecl in
          (* Now construct the module for it *)
    let modname = freshen_name ~prefix:indsigname () in
    let open CoqVernacUtils in 
    let construct_module_for_ind =
      define_module modname (famctx_to_parameters_selfprefix ctx) 
      (fun _ ->
        (* First Define the Inductive Type itself *)
        let* _ = vernac_ (VernacInductive (Inductive_kw , modified_indcstrs)) in 
        (* Then we fix Propositional Induction principle *)
        let defined_typename = internal_version_name typename in 
        let decorated_typename = CAst.make @@ Constrexpr.AN (Libnames.qualid_of_ident defined_typename) in 
        let defining_ind_name = CAst.make @@ Nameops.add_suffix defined_typename "_ind_comp" in 
        let* _ = vernac_ (VernacScheme [(Some defining_ind_name, InductionScheme(true, decorated_typename, Sorts.InProp) )]) in 
        (* Adhocly extract the recursor type for each recursor
            TODO: support other type as well, currently only support _ind   
        *)
        let* _ = thunk (collect_recursor_in_current_coqenvironment typename) in 
        (* Then export the inductive type, consistent with the interface type *)
        let alias_all = List.map (fun (n,tm, eT) -> define_term n ~eT:(Some eT) tm) alias_all_name_term_type_decl in 
        let* _ =  flatmap alias_all  in
        let* _ = if if_generate_injprop then 
          generate_injection_prooftms all_cstrnames else return () in 
          return ()
        ) in 
      
    let compiled_inddef = runVernac construct_module_for_ind in 
    let compiled_inddefty = inductive_to_famtype typed_indsigs in 
    (* 5. compile the recursor and its handlers *)
    let __recursor_context =
        let FamCtx indctx = snd typed_indsigs in 
        let ctx_of_topoup, selfname, topoup = 
          (match indctx with 
          | (selfname, oup)::ctx_of_parent_ind -> ctx_of_parent_ind, selfname, oup 
          | _  -> cerror ~einfo:__LOC__ ()) in 
        let newoup, _ =  
          famty_ext_  
            (topoup, FamCtx ctx_of_topoup) typename 
            (CoqIndTy ({allnames = all_names; indsigs_from_org_ctx = typed_indsigs ; 
                        compiled_inddefty = ModType compiled_inddefty; 
                        compiled_inddef = ModType compiled_inddef;
                        registered_prec = Summary.ref ~name:(Utils.fresh_string ~prefix:"registered_prec" ()) None
                        })) in 
        FamCtx ((selfname, (newoup))::ctx_of_topoup) in
    let compile_each_recursor_and_recursor_handler (suffix : string) (recursor : rawterm) = 
        let recursor_context = __recursor_context in 
        let recursor_name = (Nameops.add_suffix typename suffix) in 
        let parameters = famctx_to_parameters_selfprefix recursor_context in 
        let last_param, _ = List.hd @@ List.rev parameters in
        let attach_self (f : name) = 
          Constrexpr_ops.mkRefC @@ Libnames.make_qualid (Names.DirPath.make [last_param]) f in 
        let all_newname = List.map attach_self all_names in 
        let assoc_name_newname = smap_construct all_names all_newname in 
        let map_name_newname = List.fold_right (fun (k,v) map -> Dict_Name.add k v map) assoc_name_newname Dict_Name.empty in 
        let recursor = replace_var_with_rawterm_in_constr map_name_newname recursor in 
        let rec_handler = from_recursor_type_to_subcase_handlers_constructor all_cstrnames recursor in 
        (* we need to attach self_last_param everywhere *)
        let open CoqVernacUtils in 
        let typed_compiled_handlers = 
          List.map 
          (fun (case_name, raw_ty) -> 
            let handler_type_name = Nameops.add_prefix ("__handler_type_") case_name in 
            let type_handler_type_name = Nameops.add_prefix (Names.Id.to_string typename) handler_type_name in 
            let compiled_mod = runVernac @@ 
            define_module (freshen_name ~prefix:type_handler_type_name ()) parameters
            (fun ctx -> define_term handler_type_name raw_ty ) in 
            (case_name, (ModTerm compiled_mod, recursor_context)))
          rec_handler in 
        let compiled_recursor = 
          runVernac @@ 
          define_module (freshen_name ~prefix:recursor_name ())
                        parameters  
          (fun ctx -> 
              define_term (Nameops.add_prefix "__recursor_type_" recursor_name) recursor)
          in
        let typed_compiled_recursor =
          ModTerm compiled_recursor, recursor_context in 
        (typed_compiled_recursor, typed_compiled_handlers) in 
    let all_compiled_recursor_related = 
        List.map 
          (fun (suffix, recursor) ->  
              suffix, 
              compile_each_recursor_and_recursor_handler 
                suffix 
                recursor)
          !generated_recursor_type in 
    (compiled_inddef, all_compiled_recursor_related)
          
  in 
  let top_typed_ind_sig = (List.hd (fst typed_indsigs), snd typed_indsigs) in 
  constr_inductive_to_famterm_toplevel top_typed_ind_sig in 
  let open CCCache in 
  with_cache (lru ~eq:(fun a b -> (Stdlib.compare a b) = 0)  _CACHE_SIZE_) inductive_to_famterm_and_recursor_type 



let dictionary_of_inh (i : inh) = 
    (* let inh_dict = Dict_Name.add_seq (List.to_seq (snd i)) Dict_Name.empty in  *)
    let inh_info = snd i in 
    let ((_, outinfo), thectx), _ = i in 
    let (_, outinfo), _ = unfold_typed_family_type (outinfo, thectx) in 
    assert_cerror_forced ~einfo:("Unexpected Inh Judgement, the output type should have same length as input"^__LOC__) (fun _ -> List.length inh_info = List.length outinfo);
    let inh_out_info = smap_construct inh_info outinfo in 
    let inh_out_info = List.map (fun ((n1, h), (n2, o)) -> 
      assert_cerror_forced ~einfo:__LOC__ (fun _ -> n1 = n2);
      (n1, (h, o))
      ) inh_out_info in 
    Dict_Name.add_seq (List.to_seq inh_out_info) Dict_Name.empty


let dictionary_of_famty (f : family_type typed) = 
    let (_, f), _ = unfold_typed_family_type f in 
    Dict_Name.add_seq (List.to_seq f) Dict_Name.empty

let dictionary_of_inh_ty (i : inh_ty) = 
    (* let inh_dict = Dict_Name.add_seq (List.to_seq (snd i)) Dict_Name.empty in  *)
    (* let inh_info = snd i in  *)
    let ((_, outinfo), thectx) = i in 
    let (_, outinfo), _ = unfold_typed_family_type (outinfo, thectx) in 
    let inh_out_info = outinfo in 
    Dict_Name.add_seq (List.to_seq inh_out_info) Dict_Name.empty


(* apply inheritance to a (standalone) family term can lead to another family term
    two kinds of application
    1. there is existent stuff, 
          like inheritance and override -- handled by inhop_apply
    2. adding new stuff, 
          like extending -- handled by inhop_standalone
*)
let rec inh_apply_ (i : inh) (t : family_term) : family_term typed =
  let (((iin, iou), i_ctx), i_s) = i in 
  let dict_of_iou = dictionary_of_inh i in 
  let inhop_apply (i : inh_op) (exp_field_type, exp_field_type_ctx : family_type_or_coq_type typed) ((tm, tmctx) : family_term_or_coq_term typed) : family_term_or_coq_term typed =
      match i, tm, exp_field_type with 
      | CInhInherit, (FTheoremTm ({indref = _; _} as ftminfo)), FTheoremTy {indref = newindref; _} -> ((FTheoremTm {ftminfo with indref = newindref}), exp_field_type_ctx) 
      (* TODO : remove it and refactor famterm_to_mod into type-guided*)
      | CInhInherit, _, Rec2DTy {compiledterm; _} -> (CompiledDef compiledterm, exp_field_type_ctx) 
      | CInhInherit, _, PRecTy {prectm = ModType prectm; _} -> (CompiledDef (ModTerm prectm), exp_field_type_ctx) 
      | CInhInherit , _, RecTy { rawrecdef = (rtm, tmctx); motive ; _ } -> ( RecDef ((rtm tmctx, tmctx), motive) , exp_field_type_ctx)
      | CInhInherit, _, _ -> (tm, exp_field_type_ctx) 
      (* We don't do error checking here *)
      (* | CInhInheritFam , (FamTm _) -> (tm, tmctx) *)
      (* | CInhInherit , (CoqIndDef _) -> (tm, tmctx) *)
      (* | CInhInherit, _ -> (tm, tmctx) *)

      (* | CInhInherit , (ClosingFactProof _) -> (tm, tmctx)  *)
      | CInhExtendInh inner, FamTm (ftm), (FamTy (_, dependencies)) -> 
          let ftm, _ = inh_apply inner (ftm, tmctx) in 
          (FamTm (ftm), exp_field_type_ctx)
      | CInhExtendInh _, _, _ -> cerror ~einfo:"Cannot Extend a Non-Family Field" ()
      | CInhFThm {kind = `Extend; motive = motive_in_coqtm; compiled_handlers =  handlers_in_mod_new; rec_cstr = raw_recursor_constr; all_handlers} , FTheoremTm {handlers_in_mod = handlers_in_mod_old; _}, FTheoremTy {indref ; _} ->
        let modname, ctx = 
          let ModTerm newmodname, ctx = handlers_in_mod_new in 
          let _, prefix = to_qualid_name newmodname in 
          freshen_name ~prefix (), ctx in 
        let ModTerm newmod = (fst handlers_in_mod_new) in 
        let ModTerm oldmod = fst handlers_in_mod_old in 
        (* let ModTerm goal_in_mod =  (fst motive_in_coqtm) in  *)
        let combined_mod = 
          let open CoqVernacUtils in 
          runVernac @@ 
          (define_module modname (famctx_to_parameters_selfprefix ctx)
            (fun ctx ->  
              let* _ = include_mod (apply_mods (pure oldmod) ctx) in 
              let* _ = include_mod (apply_mods (pure newmod) ctx) in 
              return ())) in
        let typed_combined_mod = ModTerm combined_mod, ctx in 
        (FTheoremTm ({motive_in_coqtm; handlers_in_mod = typed_combined_mod; raw_recursor_constr; all_handlers; indref}), exp_field_type_ctx)
      | CInhExtendInd (_, _) , _, CoqIndTy {indsigs_from_org_ctx = new_combined_def; _} -> 
        let inddef', _ = inductive_to_famterm_and_recursor_type new_combined_def in 
        (CompiledDef (ModTerm inddef') , exp_field_type_ctx)
      | CInhExtendInd _ , _, _ -> cerror ~einfo:"Cannot Extend a Non-Inductive Type" ()
      | CInhOverride (newt, newtctx), _, _ -> (CompiledDef newt, newtctx)
      | CInhOverrideFamily inhinfo, FamTm _, _ -> 
        let (_, ctx), _ = inhinfo in 
        let res, ctx = (inh_apply inhinfo (([]), ctx)) in 
        (FamTm (res), ctx)
      | _ -> 
        let info = Pp.string_of_ppcmds @@ pr_inh_op i in 
        nonimplement ~moreinfo:(info ^"   "^ __LOC__) ()
    in 

  let inhop_standalone (i : inh_op) (exp_field_type, exp_field_type_ctx : family_type_or_coq_type typed) : family_term_or_coq_term typed =
    match i, exp_field_type with 
    | CInhNew _, RecTy { rawrecdef = (rtm, tmctx); motive ; _ } -> (RecDef ((rtm exp_field_type_ctx, exp_field_type_ctx),motive) , exp_field_type_ctx)
    | CInhNew (t, ctx), Rec2DTy {compiledterm; _} -> (CompiledDef compiledterm, exp_field_type_ctx)
    | CInhNew (t, ctx), _ -> (CompiledDef t, exp_field_type_ctx)
    | CInhNewFam (class_list, inner), (FamTy _) ->
      let (_, ctx),_ = inner in  
      if class_list = None 
      then let res, _ = (inh_apply inner ([], ctx)) in (FamTm (res), exp_field_type_ctx)
      else  nonimplement ~moreinfo:__LOC__()
    (* | CInhNew _, CoqIndTy {indsigs_from_org_ctx = (inddefs, ctx); _} ->
      let inddef = List.hd inddefs in  
      let inddef', _ = inductive_to_famterm_and_recursor_type ([inddef], ctx) in 
      (CompiledDef (ModTerm inddef') , exp_field_type_ctx) *)
    | CInhNewAxiom t, ClosingFactTy {ty = (tty); tytm = rawterm; _} -> (ClosingFactProof (tty, rawterm, t), exp_field_type_ctx)
    | CInhExtendInd _, _  -> cerror ~einfo:"Unexpected, Shouldn't be extend ind" ()

    | CInhFThm {kind = `New; motive = motive_in_coqtm; compiled_handlers =  handlers_in_mod; rec_cstr = raw_recursor_constr; all_handlers}, FTheoremTy {indref; _} -> FTheoremTm {motive_in_coqtm; handlers_in_mod; raw_recursor_constr; all_handlers; indref}, (snd handlers_in_mod)
    | _ -> 
      let info = Pp.string_of_ppcmds @@ pr_inh_op i in 
      nonimplement ~moreinfo:(info ^"   "^ __LOC__) ()

  in 

  let rec combine (inher : (name * inh_op) list) (fam : family_term) : family_term =
    match inher, fam with 
    | [], [] ->  []
    | [], _ -> assert_cerror ~einfo:"Mismatch!" (fun _ ->t = []); t
    | ((fname1, hinherop)::tinher),
      ((fname2, current_field)::latert) ->
        let open Pp in 
        let _ = 
          Utils.msg_notice ((str "(* Inheriting ") ++ Names.Id.print fname1 ++ (str " ... *)")) in 
        let exp_field_type = snd (Dict_Name.find fname1 dict_of_iou) in 
        if ( fname1 = fname2) (* *)
        then 

          let newfield = (inhop_apply hinherop exp_field_type current_field ) in 
          (fname1, newfield)::(combine tinher latert)
        else 
          let newfield = (inhop_standalone  hinherop exp_field_type) in 
          (fname1, newfield)::(combine tinher fam)
    | ((fname1, hinherop)::tinher),
      [] ->
      let exp_field_type = snd (Dict_Name.find fname1 dict_of_iou) in 
      let newfield = (inhop_standalone hinherop exp_field_type) in 
      (fname1, newfield)::(combine tinher fam) in 
  (combine i_s t), i_ctx
  

and inh_apply (i : inh) (t : family_term typed) : family_term typed =
  let (term, termctx) = t in 
  (* TODO : Error Checking *)

  (* TODO: check term is of type iin *)
  inh_apply_ i term


(* inh apply to family ref, when fref = None
      we assume empty family is applied
*)
let inh_apply_famref (i : inh) (fref : family_ref option) : family_term_or_coq_term typed =
  let (_, current_ctx),_ = i in 
  match fref with 
  | None -> let ft, _ =  inh_apply i ([], current_ctx) in (FamTm (ft), current_ctx)
  | Some (ToplevelRef (_, ((tm, _), ctx))) -> let ft,ctx = inh_apply i (tm, ctx) in (FamTm (ft), ctx)
  (* | Some (RelativeCtx (_, _)) -> InhTm (fref, i), current_ctx *)



(* Embed a term in a certain family context
    into a parameterized module 
*)
let embed_tterm (fname : name) ?eT:(eT = None) (e : Constrexpr.constr_expr) ?(ov_exposed = (None : pins_dependencies option))  (FamCtx f : family_ctxtype)  : modtermref CoqVernacUtils.vernacWriter = 
  let eT : Constrexpr.constr_expr option = eT in 
  let parameters = 
    match ov_exposed with 
    | None -> famctx_to_parameters_selfprefix (FamCtx f)
    | Some (Pins ov_exposed) ->
      famctx_to_parameters_selfprefix ~ov_exposed (FamCtx f) 
    | Some PinsEverything -> famctx_to_parameters_selfprefix ~all_exposed:true (FamCtx f) in
  (* Fix the name *)
  let open CoqVernacUtils in  
  define_module (freshen_name ~prefix:fname ()) parameters 
  (fun ctx -> 
    define_term fname ~eT e)

let embed_rawterm_or_proof (fname : name) eT (e : rawterm_or_tactics) ?(ov_exposed = (None : pins_dependencies option))  (FamCtx f : family_ctxtype)  : modtermref CoqVernacUtils.vernacWriter = 
  let parameters = 
    match ov_exposed with 
    | None -> famctx_to_parameters_selfprefix (FamCtx f)
    | Some (Pins ov_exposed) ->
      famctx_to_parameters_selfprefix ~ov_exposed (FamCtx f) 
    | Some PinsEverything -> famctx_to_parameters_selfprefix ~all_exposed:true (FamCtx f) in
  (* Fix the name *)
  let open CoqVernacUtils in  
  define_module (freshen_name ~prefix:fname ()) parameters 
  (fun ctx -> 
    thunk (construct_term_using_rawterm_or_proof fname e eT) 
    )

let embed_ty (fname : name) (eT : Constrexpr.constr_expr) (FamCtx f : family_ctxtype) : modtyperef CoqVernacUtils.vernacWriter = 
  let parameters = famctx_to_parameters_selfprefix (FamCtx f) in 
  let open CoqVernacUtils in  
  define_moduletype (freshen_name ~prefix:fname()) parameters 
  (fun ctx -> 
    assume_parameter fname eT)


(* from the given embedded_tm T,
    we construct the e with type T *)
let embed_tm_using_embedded_tytm (fname : name) (eT : coqtermwN) 
      (e : rawterm_or_tactics) ?(ov_exposed = (None : pins_dependencies option))  (FamCtx f : family_ctxtype)
      : modtermref CoqVernacUtils.vernacWriter =
  let parameters = 
    match ov_exposed with 
    | None -> famctx_to_parameters_selfprefix (FamCtx f)
    | Some (Pins ov_exposed) ->
      famctx_to_parameters_selfprefix ~ov_exposed (FamCtx f) 
    | Some PinsEverything -> famctx_to_parameters_selfprefix ~all_exposed:true (FamCtx f) in
  (* Fix the name *)
  let open CoqVernacUtils in  
  define_module (freshen_name ~prefix:fname ()) parameters 
  (fun ctx -> 
    let (ModTerm eTmod, fieldname) = eT in 
    let typeModname = (Nameops.add_prefix "__typeof" fname) in  
    let* _ = let_mod typeModname (apply_mods (pure eTmod) ctx) in  
    let eT = Constrexpr_ops.mkRefC (_qualid_point_ (Some (Libnames.qualid_of_ident typeModname)) fieldname) in 
    let* () = thunk (construct_term_using_rawterm_or_proof fname e eT)  in
    return ()
    )
(* 
    TODO:
      This one will act as an inference that calculuate the
      module signature of a given module
      and create a module type w.r.t. it.
    But we currently have a hard time to really know Coq's Module Facility to do it

*)
let extract_modtype (q : modtermref) : modtyperef CoqVernacUtils.vernacWriter = 
  (* 
  Note : the following idea might not work

  let modulebody = Global.lookup_module analyzedq in 
  let modulebodysig = Modops.module_type_of_module in 
  let ?? = Global.add_modtype ??  
  
  Because see `Declaremods.declare_modtype`, before `add_modtype`, 
      there are a bunch of work on universe solving
  *)
  nonimplement ~moreinfo:__LOC__ ()




let famty_ext_ind (fty: family_type typed) (fname : name) (fieldnames : name list) (t : coq_ind_sigs typed) registered_prec : family_type typed  =
  (* let ftyty, ftyctx = fty in  *)
  (* let indsigs, FamCtx tctx = t in *)
  let tty = inductive_to_famtype t in 
  let ttm = fst @@ inductive_to_famterm_and_recursor_type t in 
  (* (assert_check_of_famctx t ftyctx ftyty); *)
  famty_ext_ fty fname ((CoqIndTy ({allnames = fieldnames; indsigs_from_org_ctx = t; 
                                   compiled_inddefty = ModType tty; compiled_inddef = ModType ttm;
                                   registered_prec = Summary.ref ~name:(Utils.fresh_string ~prefix:"register_prec" ()) registered_prec
                                   })))





let rec locate_in_fam_type 
  (ctx : (name * (family_type_or_coq_type)) list ) (path : name list) : family_type_or_coq_type = 
  match path with 
  | [] -> cerror ~einfo:"Path Cannot be empty!" ()
  | e :: [] -> 
    (match List.assoc_opt e ctx with 
    | Some t -> t
    | None -> cerror ~einfo:"Path Unfound" ())
  | h :: t -> 
    let field = (match List.assoc_opt h ctx with 
    | Some t -> t
    | None -> cerror ~einfo:"Path Unfound" ()) in 
    match field with 
    | (FamTy ((famname, fam), _)) -> 
      locate_in_fam_type fam t 
    | _ -> cerror ~einfo:"Path Incorrect!" ()


(* make a family ctx into a family type
    the essence is to have ctx everywhere 
  
    *)


(* Helper function .. 
  Note that the path includes self__ at the very beginning
    but the ctx doesn't *)
let locate_in_fam_type_withself
  (FamCtx ctx : family_ctxtype) (path : fieldpath) : family_type_or_coq_type  = 
  (* There is a non-alignment that path will start with self__.. but ctx won't  *)
  let head, tail = to_name_qualid path in 
  let newhead = 
    let beginning = Names.Id.to_string head in 
    assert_cerror ~einfo:"Path Should Start With self__" (fun _ ->String.starts_with ~prefix:"self__" (Names.Id.to_string head));
    let newbeginning = String.sub beginning (String.length "self__") ((String.length beginning) - (String.length "self__")) in 
    Names.Id.of_string newbeginning in 
    
  (* let correct_path = _point_qualid_ newhead tail in *)
  (* make it into name list *)
  let _ = 
    let open Pp in  
    Utils.msg_notice @@ (str " Finding :") ++ (Names.Id.print newhead) ++ (str "in") ++ (pr_family_ctxtype (FamCtx ctx))
  in
  let (_, one_level_deep) = smap_assoc ~einfo:(Names.Id.to_string newhead ^ "   " ^ __LOC__) newhead ctx in 
  let rest_path = 
    let part1, base = Libnames.repr_qualid tail in 
    let part1 = Names.DirPath.repr part1 in 
    (List.rev part1) @ [base] in 
  locate_in_fam_type one_level_deep rest_path

  

let remove_latebinding (path : fieldpath) : fieldpath = 
  (* remove the self__... sth at the very front *)
  snd (to_name_qualid path)




(* The following functions will check if a rec_mod has all the correct
    recursor handler for indtype 
    if so, 
      they will return the rawterm that is used to define
      a concrete recursor in the module
      and the rec
*)
(* let get_rawtm_for_recursor
    ?(postpone_typechecking = false)
    (fname : name)
    (ctx : family_ctxtype)  
    ((rec_modpath, ctx1) : fieldpath typed) 
    ((ModTerm motive, ctx2) : coqterm typed)
    ((indtype, ctx3) : fieldpath typed)
    (postfix : string) : rawterm = 
    (* TODO: Add caching mechanism *)
  (* currently we only support *)
  (* assert_cerror (fun _ ->ctx = ctx1);
  assert_cerror (fun _ ->ctx = ctx2); *)
  let rec_modpath, ctx1 = wkinh_path (rec_modpath, ctx1) ctx in 
  let indtype,ctx3 = wkinh_path (indtype, ctx3) ctx in 
  (* assert_cerror (fun _ ->ctx = ctx3); *)
  let indtypesigs =  
    match locate_in_fam_type_withself ctx indtype with 
    | CoqIndTy {indsigs_from_org_ctx = x, ctx4; _} -> 
      (* generally speaking (ctx =/= ctx4); 
        because inductive type can be defined in another family
        inside a big family
      *)
      x, ctx4
    | _ -> cerror ~einfo:__LOC__ () in 
  let _, recursor_related = inductive_to_famterm_and_recursor_type indtypesigs in 
  assert_cerror ~einfo:"Recursor Not Found!" (fun _ ->List.assoc_opt postfix recursor_related <> None);
  let compiled_recursor = smap_assoc ~einfo:__LOC__ postfix @@ map_smap fst recursor_related in 
  let (ModTerm weakened_compiled_recursor, _) = wk_coq_term compiled_recursor ctx in 
  let indtypesig = List.hd (fst indtypesigs), snd indtypesigs in 
  (* extract the constructors name
      and we construct the recursor in rawterm
      and we test the construction by constructing it
      in prescence of inductive type
  *)
  (* Following will construct two recursor rawterm
      one for type checking (suffix with _test)
      the other one is the real construction *)
  (* TODO: Currently only supporting single inductive type *)
  assert_cerror ~einfo:"Currently Recursor Only Support Single Inductive Type" 
    (fun _ ->List.length (fst indtypesig) = 1);
  let ((_,({CAst.v = indtypename; _}, _)),_,_, all_cst), _ =  List.hd (fst indtypesig) in 
  let recursor_name = Nameops.add_suffix (internal_version_name indtypename) postfix in 
  let name_of_type_of_recursor = Nameops.add_prefix "__recursor_type_" (Nameops.add_suffix indtypename postfix) in 
  let recursor_path = 
    let open Libnames in 
    let (prefix_of_path, _) = repr_qualid indtype in
    make_qualid prefix_of_path recursor_name in
  let all_cst = 
    match all_cst with 
    | Vernacexpr.Constructors csts -> csts 
    | _ -> cerror ~einfo:__LOC__ () in 
  let all_cst = List.map (fun (x,(y, z)) -> CAst.with_val (fun x -> x) y) all_cst in 
  let all_projection_test = List.map (fun z -> _qualid_point_ (Some rec_modpath) z) all_cst in
  (* let all_projection = List.map remove_latebinding all_projection_test in  *)
  let recursor_construction  =
    let open Constrexpr_ops in 
    (* let recursor = mkRefC (remove_latebinding recursor_path) in *)
    let recursor = mkRefC recursor_path in
    (* raw term of recursor construction will have the motive in the context *)
    let motiveName = mkIdentC @@ Nameops.add_prefix "__motiveT" fname  in
    let recur_handlers =  List.map mkRefC all_projection_test in 
    let all_args = motiveName :: recur_handlers in 
    let applied_rec = mkAppC (recursor, all_args) in 
    applied_rec in 
  let recursor_construction_for_typechecking recursor =
    let open Constrexpr_ops in 
    (* raw term of recursor construction will have the motive in the context *)
    let motiveName = mkIdentC @@ Nameops.add_prefix "__motiveT" fname  in
    let recur_handlers =  List.map mkRefC all_projection_test in 
    let all_args = motiveName :: recur_handlers in 
    let applied_rec = mkAppC (recursor, all_args) in 
    applied_rec in 

  (* Now we do type checking for this recursive construction 
      is working, by translation *)
  let _ = 
  if postpone_typechecking 
  then () else 
    let _ = 
      let open Pp in
      Utils.msg_notice (str "(* Here Start Doing Type Checking .. *)");
      let open CoqVernacUtils in 
      let open Constrexpr_ops in 
      let parameters = famctx_to_parameters_selfprefix ctx in 
      let _ = 
      runVernac @@
      define_module (freshen_name ~prefix:(freshen_name ()) ()) parameters 
      (fun ctx -> 
        let applied_motive = apply_mods (pure motive) ctx in 
        let* _ = include_mod applied_motive in 
        let applied_recursor_mod = apply_mods (pure weakened_compiled_recursor) ctx in 
        let* _ = include_mod applied_recursor_mod in 
        let recursor_type = mkRefC (Libnames.qualid_of_ident name_of_type_of_recursor) in 
        let recursor = (Names.Id.of_string "recursor_for_type_checking") in 
        let* _ = assume_parameter recursor recursor_type in 
        let* _ = define_term (Names.Id.of_string "term_for_type_checking") 
                      (recursor_construction_for_typechecking (mkIdentC recursor)) in 
        return ()
        ) in 
      Utils.msg_notice (str "(* Here Ends Doing Type Checking .. *)")
      in 
    () in 
  (* we take out the recursor *)
  recursor_construction  *)


(* return a term constructor and a term type checker *)
let get_rawtm_for_recursor
    (fname : name)
    (ctx : family_ctxtype)  
    ((rec_modpath, ctx1) : fieldpath typed) 
    ((ModTerm motive, ctx2) : coqterm typed)
    ((indtype, ctx3) : fieldpath typed)
    (postfix : string) : (family_ctxtype -> rawterm) * (family_ctxtype -> unit) = 
    (* TODO: Add caching mechanism *)
  (* currently we only support *)
  (* assert_cerror (fun _ ->ctx = ctx1);
  assert_cerror (fun _ ->ctx = ctx2); *)
  let term_constructor_type_checker ctx = 
  let rec_modpath, ctx1 = wkinh_path (rec_modpath, ctx1) ctx in 
  let indtype,ctx3 = wkinh_path (indtype, ctx3) ctx in 
  (* assert_cerror (fun _ ->ctx = ctx3); *)
  let indtypesigs =  
    match locate_in_fam_type_withself ctx indtype with 
    | CoqIndTy {indsigs_from_org_ctx = x, ctx4; _} -> 
      (* generally speaking (ctx =/= ctx4); 
        because inductive type can be defined in another family
        inside a big family
      *)
      x, ctx4
    | _ -> cerror ~einfo:__LOC__ () in 
  let _, recursor_related = inductive_to_famterm_and_recursor_type indtypesigs in 
  assert_cerror ~einfo:"Recursor Not Found!" (fun _ ->List.assoc_opt postfix recursor_related <> None);
  let compiled_recursor = smap_assoc ~einfo:__LOC__ postfix @@ map_smap fst recursor_related in 
  let (ModTerm weakened_compiled_recursor, _) = wk_coq_term compiled_recursor ctx in 
  let indtypesig = List.hd (fst indtypesigs), snd indtypesigs in 
  (* extract the constructors name
      and we construct the recursor in rawterm
      and we test the construction by constructing it
      in prescence of inductive type
  *)
  (* Following will construct two recursor rawterm
      one for type checking (suffix with _test)
      the other one is the real construction *)
  (* TODO: Currently only supporting single inductive type *)
  assert_cerror ~einfo:"Currently Recursor Only Support Single Inductive Type" 
    (fun _ ->List.length (fst indtypesig) = 1);
  let ((_,({CAst.v = indtypename; _}, _)),_,_, all_cst), _ =  List.hd (fst indtypesig) in 
  let recursor_name = Nameops.add_suffix (internal_version_name indtypename) postfix in 
  let name_of_type_of_recursor = Nameops.add_prefix "__recursor_type_" (Nameops.add_suffix indtypename postfix) in 
  let recursor_path = 
    let open Libnames in 
    let (prefix_of_path, _) = repr_qualid indtype in
    make_qualid prefix_of_path recursor_name in
  let all_cst = 
    match all_cst with 
    | Vernacexpr.Constructors csts -> csts 
    | _ -> cerror ~einfo:__LOC__ () in 
  let all_cst = List.map (fun (x,(y, z)) -> CAst.with_val (fun x -> x) y) all_cst in 
  let all_projection_test = List.map (fun z -> _qualid_point_ (Some rec_modpath) z) all_cst in
  (* let all_projection = List.map remove_latebinding all_projection_test in  *)
  let recursor_construction  =
    let open Constrexpr_ops in 
    (* let recursor = mkRefC (remove_latebinding recursor_path) in *)
    let recursor = mkRefC recursor_path in
    (* raw term of recursor construction will have the motive in the context *)
    let motiveName = mkIdentC @@ Nameops.add_prefix "__motiveT" fname  in
    let recur_handlers =  List.map mkRefC all_projection_test in 
    let all_args = motiveName :: recur_handlers in 
    let applied_rec = mkAppC (recursor, all_args) in 
    applied_rec in 
  let recursor_construction_for_typechecking recursor =
    let open Constrexpr_ops in 
    (* raw term of recursor construction will have the motive in the context *)
    let motiveName = mkIdentC @@ Nameops.add_prefix "__motiveT" fname  in
    let recur_handlers =  List.map mkRefC all_projection_test in 
    let all_args = motiveName :: recur_handlers in 
    let applied_rec = mkAppC (recursor, all_args) in 
    applied_rec in 

  (* Now we do type checking for this recursive construction 
      is working, by translation *)
  let type_checker () = 
    let _ = 
      let open Pp in
      Utils.msg_notice (str "(* Here Start Doing Type Checking .. *)");
      let open CoqVernacUtils in 
      let open Constrexpr_ops in 
      let parameters = famctx_to_parameters_selfprefix ctx in 
      let _ = 
      runVernac @@
      define_module (freshen_name ~prefix:(freshen_name ()) ()) parameters 
      (fun ctx -> 
        let applied_motive = apply_mods (pure motive) ctx in 
        let* _ = include_mod applied_motive in 
        let applied_recursor_mod = apply_mods (pure weakened_compiled_recursor) ctx in 
        let* _ = include_mod applied_recursor_mod in 
        let recursor_type = mkRefC (Libnames.qualid_of_ident name_of_type_of_recursor) in 
        let recursor = (Names.Id.of_string "recursor_for_type_checking") in 
        let* _ = assume_parameter recursor recursor_type in 
        let* _ = define_term (Names.Id.of_string "term_for_type_checking") 
                      (recursor_construction_for_typechecking (mkIdentC recursor)) in 
        return ()
        ) in 
      Utils.msg_notice (str "(* Here Ends Doing Type Checking .. *)")
      in () in 
  (* we take out the recursor *)
  recursor_construction, type_checker in 
  let term_cstr ctx = fst (term_constructor_type_checker ctx) in 
  let type_checker ctx = snd (term_constructor_type_checker ctx) () in 
  (term_cstr, type_checker)





let check_recursor_validity 
  (fname : name)
  (ctx : family_ctxtype)  
  (rec_mod : fieldpath typed) 
  (motive : coqterm typed)
  (indtype : fieldpath typed)
  (postfix : string) : unit =
  let _ = get_rawtm_for_recursor fname ctx rec_mod motive indtype postfix in ()


(* if a motive has type P = (fun x -> P x)
    then the final recursor will have type (forall x, P(x))

  we also have some quirks here, we allow the compiled motiveT
  *)
let get_recty_from_motive fname 
  ?(motiveTpathprefix = (None : fieldpath option))
  ((motive, ctx) : coqterm typed)
   =
  let parameters = famctx_to_parameters_selfprefix ctx in 
  let rec get_parameter_number_of_product (t : Constr.constr) : int =
    let open Constr in 
    if isProd t then 
      let _, _, body = destProd t in 
      1 + (get_parameter_number_of_product body) 
    else 0 in
  let open CoqVernacUtils in 
  ModType (runVernac @@ 
          define_moduletype (freshen_name ~prefix:fname ()) parameters 
          (fun ctx ->
            (* Given Motive P here *)
            (* Construct Parameter fname : forall ..., P .. *)
            (* The challenge here is to check how many parameter P has *)
            let open Constrexpr_ops in 
            let open Constrexpr in 
            let ModTerm motive = motive in 
            let applied_motive = apply_mods (pure motive) ctx in 
            let* _ = include_mod applied_motive in 
            let motiveT =  (Nameops.add_prefix "__motiveT" fname) in 
            (* Attach prefix if specified *)
            let motiveT =
              let full_path = 
              match motiveTpathprefix with 
              | None -> Libnames.qualid_of_ident motiveT 
              | Some prefix -> _qualid_point_ motiveTpathprefix motiveT
              in 
              mkRefC full_path
            in
            thunk 
            (* We have to wrap the following into a thunk 
              because the following must be evaluated inside 
              the constructed module
              *)
            (fun () ->
              let parameter_number = get_parameter_number_of_product @@ type_check motiveT in 
              let vars = 
                List.map (fun x -> 
                            Names.Id.of_string @@
                            "v" ^ string_of_int x) @@
                List.init parameter_number (fun x -> x + 1) in
              let binders = 
                List.map (fun x ->
                            CAst.make @@ Names.Name.mk_name x) vars in 
              let binders = 
                List.map 
                (fun x -> 
                    CLocalAssum ([x], Default Glob_term.Explicit, 
                      CAst.make @@ CHole (None, Namegen.IntroAnonymous, None))) binders in 
              let funcbody = mkAppC (motiveT,(List.map mkIdentC vars)) in 
              let prodtype = mkProdCN binders funcbody in 
              assume_parameter fname prodtype
            ) 
            (* Then we include computational axiom *)

    )), ctx

let get_coqty_for_recursor
  (fname : name)
  (ctx : family_ctxtype)
  (rec_mod : fieldpath typed) 
  ((motive, ctx2) : coqterm typed)
  (indtype : fieldpath typed) 
  (postfix : string): coqtype typed = 
  (* TODO: Add caching mechanism *)
  check_recursor_validity fname ctx rec_mod (motive,ctx) indtype postfix; 
  get_recty_from_motive fname (motive, ctx)


(* this will return the "abstracted" recursor type 
    because the original one will have "__internal_" all around
*)
let get_recursor_type_for_indref 
  (ctx : family_ctxtype) 
  ?(suffix = ("_rect" : string))
  (indref : fieldpath) : rawterm = 
  let open Constrexpr_ops in 
  let open CoqVernacUtils in 
  let ind_rect_ref =     
    let path, ind = to_qualid_name indref in 
    let indrec = Nameops.add_suffix ind suffix in 
    let indrec = Nameops.add_prefix "__recursor_type_" indrec in 
    mkRefC @@ Libnames.qualid_of_ident @@ indrec in
  (* then we get the content of ind_rect_ref 
      but we need to include the calculated type from "__recursor_type_"
    *)
  let indsig =     
    let t = locate_in_fam_type_withself ctx indref in 
      match t with 
      | CoqIndTy {indsigs_from_org_ctx; _}-> indsigs_from_org_ctx
      | _ -> cerror ~einfo:"Should refer to an inductive type!" () in
  let original_rect_recursor = 
    let _, recursors = inductive_to_famterm_and_recursor_type indsig in 
    let (ModTerm rect_recursor, _), _ = smap_assoc ~einfo:__LOC__ suffix recursors in 
    rect_recursor
  in 
  let original_ind_rect_type = 
    let result = ref None in 
    (* let ov_exposed = Set_Fieldpath.add indref @@ Set_Fieldpath.empty in  *)
    (* let exposed_parameters = famctx_to_parameters_selfprefix ~ov_exposed ctx in  *)
    let parameters = famctx_to_parameters_selfprefix ctx in
    let _ = 
      runVernac @@ 
      define_module (freshen_name ()) parameters 
      (fun ctx -> 
        let* _ = include_mod (apply_mods (pure original_rect_recursor) ctx) in 
        thunk (
          fun () ->
            let ind_rect_term = reflect_safeterm @@ Utils.cbv_all ind_rect_ref in
            result := Some ind_rect_term;
            return ()
        )) in 
    match !result with 
    | None -> cerror ~einfo:__LOC__ ()
    | Some x -> x in
  original_ind_rect_type
  
(* Prerequsite: this function can only be runned in the correct
   environment where recursorref indref constrref are accessible 
   
   also only support non-indexed inductive type now
   *)
let calculate_computational_axiom_for_rec_constructor 
    ~(recursorref : fieldpath)
    ~(indref : fieldpath)
    ~(constrref : fieldpath) : (name * rawterm) = 
  (* we enter the module to get the environment *)
  let open Constrexpr_ops in 
  let open Constrexpr in 
  (* let open CoqVernacUtils in  *)
  let (params, fully_applied_constr) = 
      fully_applied (mkRefC constrref) in 
  (* now we have (constrref ?v1 ...) *) 


  (* we also need to make recursor fully applied later, so we collect the parameter type of recursor and remove the first parameter *)
  
  let recursor_parameter, _ =            
      collect_argument_and_ret_of_type @@ 
      reflect_safeterm @@
      type_check (mkRefC recursorref) in 
  let recursor_parameter_wo_first = 
      List.tl recursor_parameter in 
  let recursor_remained_arguments = 
      List.map snd recursor_parameter_wo_first in
  (* add those parameters from recursor *)
  let params = 
    params@recursor_parameter_wo_first 
  in 
  (* then we make the parameter *)
  (* Note that, we want to construct
     recursorref (constrref ?v1 ?v2 ...) *)
  let recursor_applied = mkAppC ((mkRefC recursorref),fully_applied_constr::recursor_remained_arguments) in 
  (* then we need second fully applied, to make sure recursor doesn't need more argument *)
          
  let eq_cstr = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "eq" in 
  let id_on_fully_applied_r =  mkAppC (eq_cstr, [recursor_applied;recursor_applied]) in  
  (* and we close it and normalize it to get the final result *)
  let closed_recursor_applied = 
    List.fold_right (fun (a, b, c) body -> mkProdC (a,b,c, body)) (List.map fst params) id_on_fully_applied_r  in
   (*Then we internalize it for sanity and normalize it *)

  let res = 
    let reflected = reflect_safeterm (cbn_term closed_recursor_applied) in 

    (* let reflected = reflect_safeterm (Utils.cbv_beta closed_recursor_applied) in  *)
     (* then we extract the body *)
    let _, body = collect_argument_and_ret_of_type reflected in 
    let _ = 
      let open Pp in 
      Utils.msg_notice @@ (str __LOC__ ) ++ pr_constr_expr reflected 
    in 
    let isEq {CAst.v = t; _} = match t with | CNotation (_, (_, "_ = _"), _) -> true | _ -> false in
    assert_cerror_forced ~einfo:__LOC__ 
    (fun _ -> isEq body); 
    let destEq {CAst.v = t; _} = 
      match t with 
      | CNotation (_ ,(_, "_ = _"), ([lhs; rhs], _, _, _)) -> (lhs, rhs) 
      | _ -> cerror ~einfo:__LOC__ () in
    let normalized, _ = destEq body in 
    let id_on_applied_and_normalized = 
      mkAppC (eq_cstr, [recursor_applied;normalized]) in 
    List.fold_right (fun (a, b, c) body -> mkProdC (a,b,c, body)) (List.map fst params) id_on_applied_and_normalized in 
  let eq_name = 
    let _, recname = to_qualid_name recursorref in  
    let _, cstrname = to_qualid_name constrref in 
    let eq_name =
      let cstrname = Names.Id.to_string cstrname in
      Nameops.add_suffix recname ("_on_" ^ cstrname) in 
    eq_name in 
  eq_name, res 


(* return the name and the type 
  for one recursor and the constructor  *)
let generate_computational_axiom_for_rec_constructor 
  (ctx : family_ctxtype) 
  ~(recursorref : fieldpath)
  ~(indref : fieldpath)
  (constrrefs : fieldpath list) : (name * rawterm) list = 
  let parameters = 
    let ov_exposed = 
      Set_Fieldpath.add recursorref @@
      Set_Fieldpath.add indref @@ Set_Fieldpath.empty in 
    famctx_to_parameters_selfprefix ~ov_exposed ctx in
  (* we enter the module to get the environment *)
  (* let open Constrexpr_ops in  *)
  (* let rawconstrref = mkRefC constrref in  *)
  let open CoqVernacUtils in 
  let final_result = ref [] in 
  let for_each_constrref (constrref : fieldpath) =
    let name, equation = 
      calculate_computational_axiom_for_rec_constructor ~recursorref ~indref ~constrref in 
    final_result := (name, equation)::(!final_result);
    return ()
  in
  let _ = 
  runVernac @@
  define_module (fresh_name ()) parameters
  (fun ctx -> 
    let for_all_constrref () = 
      let allcommnds = List.map for_each_constrref constrrefs in 
      CoqVernacUtils.flatmap allcommnds in 
    thunk for_all_constrref
    ) in 
  ! final_result

let clear_up_internal_version_prefix (t : rawterm) : rawterm = 
  let open Constrexpr in 
  (* let open Constrexpr_ops in  *)
  let remove_possible_internal_prefix (q : fieldpath) = 
    let pathprefix, base = to_qualid_name q in 
    let basestr = Names.Id.to_string base in 
    let is_starting_with_internal = 
      let prefix = "__internal_" in 
      String.starts_with ~prefix basestr in 
    if is_starting_with_internal 
      then _qualid_point_ pathprefix (uninternal_version_name base)
      else q in  
  let isCRef ({CAst.v = t; _} : rawterm) = 
    match t with 
    | CRef _ -> true 
    | _ -> false 
  in 
  let replacingF ({CAst.v = t; CAst.loc = loc} : rawterm) = 
    match t with 
    | CRef (q, r) -> CAst.make @@ CRef (remove_possible_internal_prefix q, r)
    | _ -> cerror ~einfo:__LOC__ () 
  in 
  replace_in_rawterm isCRef replacingF t 

(* 
generate equational rule for partial recursor   
*)

let generate_computational_axiom_for_prec 
(ctx : family_ctxtype) 
~(precref : fieldpath)
~(indref : fieldpath)
(valid_cstrs : int) : (name * rawterm) list = 
let open Constrexpr in 
let open Constrexpr_ops in 
let open CoqVernacUtils in 
  (* we first extract the definition of _rect from indref *)
  (* then we go into the definition, which will be a fix and pattern match
    then for the first valid_cstrs number of pattern cases, 
    we generate equation
      *)
  (* let all_cstrs = nonimplement () in *)
  let rect_def : rawterm = 
    let internal_rect_ref = 
      let pathprefix, base = to_qualid_name indref in 
      let base = Nameops.add_suffix (internal_version_name base) "_rect" in 
      _qualid_point_ pathprefix base 
    in 
    (* we get the definition of the recursor *)
    let ov_exposed = Set_Fieldpath.add indref Set_Fieldpath.empty in 
    let exposed_parameters = famctx_to_parameters_selfprefix ~ov_exposed ctx in 
    let result = ref None in 
    let _ = 
      runVernac @@ 
      define_module (freshen_name ()) exposed_parameters 
      (fun ctx -> 
        thunk (
          fun () ->
          let internal_rect = mkRefC internal_rect_ref in 
          result := Some (reflect_safeterm (Utils.cbv_unfold_def internal_rect));
          return () 
        )) in 
      match !result with 
      | None -> cerror ~einfo:__LOC__ ()
      | Some x -> x in 
  (* we use this parameter because later
     we will use clear_up_internal_version
     to clean up all the __internal_ prefix *)
  let params, body = collect_argument_and_ret_of_lambda rect_def in
  (* only deal with non-indexed inductive type
     and only leave with the first valid_cstrs + 1 number of parameters
     because the remaining ones are handlers not presenting in the partial recursor
     *)
  let params = 
    let (thep, _, _), _ = List.hd params in
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> List.length thep = 1);
    let thep = Names.Id.to_string @@
      match List.hd thep with
      | {CAst.v = Names.Name thep; _} -> thep 
      | {CAst.v = Names.Anonymous; _} -> cerror ~einfo:__LOC__ () in   
    let is_P ({CAst.v = t; _} : rawterm) : bool = 
      match t with 
      | CRef (q, _) when Libnames.qualid_is_ident q -> 
        (Names.Id.to_string @@ Libnames.qualid_basename q) = thep
      | _ -> false 
    in 
    let is_P_applying ({CAst.v = t; _} : rawterm) : bool =
      match t with 
      | CApp (f, _) when is_P f -> true 
      | _ -> false 
    in  
    let _option = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "option" in 
    let replacingf (t : rawterm) : rawterm = 
      mkAppC (_option, [t])
    in
    (* preprocess : only leave with valid parameters *)
    let validparams = List.filteri (fun i _ -> i < valid_cstrs + 1) params in
    (* decorate P with option *)
    let withoption = replace_in_rawterm is_P_applying replacingf in 
    List.map (fun ((a,b,c), d) -> (a,b, withoption c), d) validparams
  in
  (* we extract parameter from the abstracted version of the recursor
     because this version doesn't have __internal_ *)

  (* 
  let params = 
    let rect_ty = get_recursor_type_for_indref ctx indref in
    let params, _ = collect_argument_and_ret_of_type rect_ty in 
    (* remove the last parameter *)
    let params = List.filteri (fun i _ -> i < List.length params - 1) params in 
    params in  *)
  let isFix {CAst.v = t; _} = match t with | CFix _ -> true | _ -> false in
  let isMatch {CAst.v = t; _} = match t with | CCases ( Constr.RegularStyle , _, _, _) -> true | _ -> false in
  (* 
  https://coq.github.io/doc/v8.9/refman/language/gallina-specification-language.html#grammar-token-fix_body

  return ident, binder, type, body *)
  let destFixs {CAst.v = t; _} = 
    match t with 
    | CFix (_, ls) -> List.map (fun (a,b,c,d, e) -> (a,c,d,e)) ls
    | _ -> cerror ~einfo:__LOC__ () in 
  (* return a list of pattern and branches *)
  let destMatch {CAst.v = t; _} = 
    match t with 
    | CCases (_, _, _, branches) -> 
      (* each branch must only have one pattern and one return clause *)
      let for_each_branch ({CAst.v = (patterns, return_clause); _} : branch_expr) = 
        assert_cerror_forced ~einfo:"Single Pattern Expected"
        (fun _ -> List.length patterns = 1 && List.length (List.hd patterns) = 1);
        (List.hd (List.hd patterns), return_clause)
      in List.map for_each_branch branches 
    | _ -> cerror ~einfo:__LOC__ () in
  (* return the transformed rawterm and the variables in it *)
  let pattern_to_rawterm : cases_pattern_expr -> rawterm * Set_Name.t * fieldpath = 
    let vars = ref Set_Name.empty in 
    let rec pattern_to_rawterm_ ({CAst.v = t; _} : cases_pattern_expr) : rawterm = 
      match t with 
      | CPatPrim p -> CAst.make @@ CPrim p
      | CPatAtom q ->
          begin match q with 
          | Some q when Libnames.qualid_is_ident q -> 
            vars := Set_Name.add (Libnames.qualid_basename q) !vars;
            mkRefC q
          | Some q -> mkRefC q
          | None -> 
            let newvar = fresh_name ~prefix:"_arg" () in 
            vars := Set_Name.add newvar !vars;
            mkRefC (Libnames.qualid_of_ident newvar)
          end  
      | CPatCstr (f, None, args) -> 
        let f = mkRefC f in 
        let args = List.map pattern_to_rawterm_ args in 
        mkAppC (f, args)
      | _ -> cerror ~einfo:__LOC__ () in 
    let cstr_name ({CAst.v = t; _} : cases_pattern_expr) = 
      match t with 
      | CPatAtom (Some q) -> q 
      | CPatCstr (f, _, _) -> f 
      | _ -> cerror ~einfo:__LOC__ () 
    in 
    let final_f t = 
      vars := Set_Name.empty;
      let x = pattern_to_rawterm_ t in 
      (x, !vars, cstr_name t) in 
    final_f
  in 
  
  (* not necessarily a recursive function
      especially when it is not a recursive type *)
  (* assert_cerror_forced ~einfo:"Expect to be a Fix term" 
    (fun _ -> isFix body); *)
  
  (* assert_cerror_forced ~einfo:"Expect to be single fix body" 
    (fun _ -> List.length fixterm = 1); *)
  let fixfname, matchbody = 
    if (isFix body) 
      then (* it is a recursive function *)
        begin 
        let fixterm = destFixs body in  
        let fixfname, _,_,matchbody = (List.hd fixterm) in fixfname, matchbody 
        end
      else (* it is not *)
        (CAst.make (Names.Id.of_string "_"), body)
     in 
  assert_cerror_forced ~einfo:"Fix body should be a Match" 
    (fun _ -> isMatch matchbody);
  (* now we construct rawterm -> rawterm
    s.t. t |-> tm_prec t P f f0 f1 f2 ...   
  *)
  let use_prec_on  : rawterm -> rawterm =
    let other_args = List.map snd params in
    let prec = mkRefC  precref in 
    let prec_mapping (t : rawterm) : rawterm = 
      mkAppC (prec, t::other_args) in 
    prec_mapping
  in
  let branches = destMatch matchbody in 
  (* 
    main logic : do things for each branch, with valid cosntructor 
  *)
  let for_each_branch ((pattern, ret), valid : (cases_pattern_expr * rawterm) * [`ValidCstr | `NonValidCstr]) : name * rawterm = 
    let input, newvars, cstname = pattern_to_rawterm pattern in 
    let _, cstname = to_qualid_name cstname in 
    let lhs = use_prec_on input in 
    (* Now we need replace `fixfname` in ret with use_prec_on
       and becomes the rhs  *)
    let rhs = 
      match valid with 
      | `ValidCstr -> 
          begin let equals_fixfname ({CAst.v = t; _} : rawterm) = 
            match t with 
            | CRef (q, _) -> 
              let {CAst.v = fixfname; _} = fixfname in
              (Libnames.qualid_is_ident q)
              && (
                let q = Names.Id.to_string @@ Libnames.qualid_basename q in 
                let fixfname = Names.Id.to_string fixfname in 
                q = fixfname 
              )  
            | _ -> false in 
          let isAppF ({CAst.v = t; _} : rawterm) = 
            match t with 
            | CApp (f, [(_, _)]) when (equals_fixfname f) -> true 
            | CApp (f, _) when (equals_fixfname f) -> cerror ~einfo:__LOC__ ()
            | _ -> false  
          in
          let replacingF ({CAst.v = t; _} : rawterm) = 
            match t with 
            | CApp (_, [(arg, _)]) -> use_prec_on arg 
            | _ -> cerror ~einfo:__LOC__ ()  
          in 
          replace_in_rawterm isAppF replacingF ret 
        end 
    | `NonValidCstr -> mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "None" 
    in 
    let eq = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "eq" in 
    let equation = mkAppC (eq, [lhs; rhs]) in 
    (* newparams are from the newvars *)
    let newparams : (local_binder_expr_assume) list = 
      let newvars = List.of_seq (Set_Name.to_seq newvars) in 
      List.map (fun s -> 
        ([ CAst.make @@ Names.Name s ], 
          Default Glob_term.Explicit, 
          CAst.make (CHole (None, Namegen.IntroAnonymous, None)))
        ) newvars in
    let all_params = (List.map fst params)@newparams in  
    let res = List.fold_right (fun (a, b, c) body -> mkProdC (a,b,c, body)) all_params equation  in
    (* we also need to remove __internal_ prefix in equation, actually from anywhere  *)
    let res = clear_up_internal_version_prefix res in 
    let equname = 
      let _, prec_name = to_qualid_name precref in
      let cstname = if String.starts_with ~prefix:"__internal_" (Names.Id.to_string cstname) then uninternal_version_name cstname else cstname in 
      let cstname = Names.Id.to_string cstname in   
      Nameops.add_suffix prec_name ("_on_"^cstname)
      in 
    (equname, res)
  in
  let branches = List.mapi (fun i x -> if i < valid_cstrs then (x, `ValidCstr) else (x, `NonValidCstr)) branches in 
  List.map for_each_branch branches
(* return the module type and module term in the context ctx
  for the computational axiom of the inductive type  *)
let generate_computational_axiom_for_rec
  (ctx : family_ctxtype) 
  ~(recursorref : fieldpath)
  ~(indref : fieldpath) : coqtype * coqterm = 
  let open CoqVernacUtils in 
  let modname = 
    let _, recname = to_qualid_name recursorref in  
    let _, indname = to_qualid_name indref in 
    let indname = Names.Id.to_string indname in 
    Nameops.add_suffix recname (indname) in 
  let generate_computational_axiom_for_rec_
    (ctx : family_ctxtype) 
    ~(recursorref : fieldpath)
    ~(indref : fieldpath) : coqtype * coqterm = 
    let exposed_parameters = 
      let ov_exposed = 
        Set_Fieldpath.add recursorref @@
        Set_Fieldpath.add indref @@ Set_Fieldpath.empty in 
      famctx_to_parameters_selfprefix ~ov_exposed ctx in
    let parameters = 
      famctx_to_parameters_selfprefix  ctx in
    let auto_tactic : rawterm_or_tactics = 
      let script : Tacexpr.raw_tactic_expr = 
        (CAst.make (Tacexpr.TacArg (Tacexpr.TacCall (CAst.make ( Libnames.qualid_of_ident (Names.Id.of_string "eauto") ,[]))) )) in 
      ProofScript {script; starting_plain = true; opacity = Vernacexpr.Opaque} in
    (* Detect we are about partial recursor or normal recursor 
        normal-recursor -- we use generate_computational_axiom_for_rec_constructor
        partial-recursor -- otherwise
      *)
    let is_normal_recursor : [`NormalRec | `PRec of int ] = 
      let recty = locate_in_fam_type_withself ctx recursorref in 
      match recty with 
      | RecTy _ -> `NormalRec 
      | PRecTy {cstrs; _} -> `PRec (List.length cstrs)
      | _ -> cerror ~einfo:__LOC__ ()
      in 
    let name_axiom_pairs = 
      match is_normal_recursor with 
      | `NormalRec -> 
        begin 
          let cstrrefs = 
            let indsig = 
                match locate_in_fam_type_withself ctx indref with 
                | CoqIndTy {indsigs_from_org_ctx = x; _} -> 
                  x
                | _ -> cerror ~einfo:__LOC__ () in 
            let all_cstrs_indent = extract_cstrs_ident (fst indsig) in
            let path_prefix, _ = to_qualid_name indref in  
            let all_cstr_refs = List.map (_qualid_point_ path_prefix) all_cstrs_indent in 
            all_cstr_refs in 
          generate_computational_axiom_for_rec_constructor ctx ~recursorref ~indref cstrrefs 
        end 
      | `PRec valid_parameters ->
        generate_computational_axiom_for_prec ctx ~precref:recursorref ~indref valid_parameters
    in 
    (* we first generate module type *)
    let modtype = 
      runVernac @@
      define_moduletype (freshen_name ~prefix:modname ()) parameters
      (* the we generate module term for given type *)
      (fun ctx -> 
        let for_each_pair (n, ty) =
          assume_parameter n ty in 
        flatmap (List.map for_each_pair name_axiom_pairs)) in 
    let modterm = 
      runVernac @@
      define_module (freshen_name ~prefix:modname ()) exposed_parameters
      (* the we generate module term for given type *)
      (fun ctx -> 
        let for_each_pair (n, ty) =
          thunk (construct_term_using_rawterm_or_proof n auto_tactic ty) in 
        flatmap (List.map for_each_pair name_axiom_pairs)) in 
      (ModType modtype, ModTerm modterm) in 
  generate_computational_axiom_for_rec_ ctx ~recursorref ~indref



(* return the signature for the partial recursor
      can only be called in the context 
    where indref is accessible
     We only support non-indexed inductive type for now 
  *)
let compute_partial_recursor_signature 
  precname
  (ctx : family_ctxtype) 
  (indref : fieldpath) : rawterm * coqtype = 
  let open CoqVernacUtils in 
  let open Constrexpr_ops in 
  let open Constrexpr in 
  (* we first get type for "indref"_rect *)
  (* 
  1. we extract the recursor type from the inductive definition
  2. we wrap each P t with option, so it becomes option (P t)
  3. we make the eliminated term as the first parameter, so that rec2d can work well on it
  *)
  (* then we get the content of ind_rect_ref 
      but we need to include the calculated type from "__recursor_type_"
    *)
  let original_ind_rect_type = get_recursor_type_for_indref ctx indref in 
  (* we get the first P parameter in the type
     and construct a function to check if a given rawterm 
        has the same name as the first P *)
  let is_P (c : rawterm) : bool = 
    let all_params, _ = collect_argument_and_ret_of_type original_ind_rect_type in 
    let (ps, _, _), _ = List.hd all_params in
    let {CAst.v = p; _} = List.hd ps in 
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> List.length ps = 1);
    let p = match p with | Names.Name p -> p | _ -> cerror ~einfo:__LOC__ () in 
    match c with 
    | {CAst.v = CRef (c, _); _} when (Libnames.qualid_is_ident c) -> 
      let c = Libnames.qualid_basename c in p = c
    | _ -> false in
  let _option_decoration = 
    let _option = mkRefC @@ Libnames.qualid_of_ident @@ Names.Id.of_string "option" in
    fun t -> mkAppC (_option, [t])
  in
   (* now we swap the eliminated term into the first argument  *)
  let flipped_indrec_type = 
    let all_params, ret = collect_argument_and_ret_of_type original_ind_rect_type in 
    (* make the last parameter into the front *)
    let rec heads_tail (l) = 
      match l with 
      | [] -> cerror ~einfo:__LOC__ () 
      | h :: [] -> ([], h) 
      | h :: t -> let th, tt = heads_tail t in (h::th, tt) in 
    let heads_param, tail_param = heads_tail all_params in 
    let all_params = List.map fst @@ tail_param :: heads_param in 
    let res = List.fold_right (fun (a, b, c) body -> mkProdC (a,b,c, body)) all_params ret in 
    res 
  in 
  let ind_rect_type = flipped_indrec_type in 
  (* then we flip the argument order in ind_rect_type
      s.t.  *)
  (* we replace the P t into option (P t) *)
  let replaced_ind_rect_type = 
    let rec replace_helper _ r =
      match r with
      | { CAst.v = (CApp (f, _)) ; _ } as original 
          when (is_P f)  ->
          (* rename the  *)
        (_option_decoration original)
      | cn -> map_constr_expr_with_binders (fun _ _ -> ()) replace_helper () cn in
    
    replace_helper () ind_rect_type in  
  let compiled_replaced_ind_rect_type = 
    let parameters = famctx_to_parameters_selfprefix ctx in 
    let compiled = 
      runVernac @@
      define_moduletype (freshen_name ~prefix:precname ()) parameters
      (fun ctx ->
        assume_parameter precname replaced_ind_rect_type
        ) in 
    compiled
  in 
  replaced_ind_rect_type, ModType compiled_replaced_ind_rect_type



(* return the (cached) compiled term and type
      for the partial recursor for the indref 
  valid_parameter_number refers to the number of parameters 
      that is considered for partial recursor
  i.e. 

  how many parameters in the signature of the partial recursor
      *)
let generate_partial_recursor_tm_legacy
  precname
  (ctx : family_ctxtype) 
  (indref : fieldpath) 
  (indprec_ty : rawterm)
  (valid_parameter_number : int) : coqterm = 
  let open CoqVernacUtils in 
  let open Constrexpr_ops in 
  let open Constrexpr in 
  (* let fname = 
    let _, indname = to_qualid_name indref in 
    Nameops.add_suffix indname "__prect" in  *)
  (* let indprec_ty, compiled_inddef = compute_partial_recursor_signature fname ctx indref in  *)
  (* let exposed_parameters = 
    let ov_exposed = 
      Set_Fieldpath.add indref @@ Set_Fieldpath.empty in 
    famctx_to_parameters_selfprefix ~ov_exposed ctx in *)
  let ind_sig : coq_ind_sigs =     
    match locate_in_fam_type_withself ctx indref with 
    | CoqIndTy {indsigs_from_org_ctx = x, _; _} -> x
    | _ -> cerror ~einfo:__LOC__ () in 

  (* let modtype = 
    let parameters = 
      famctx_to_parameters_selfprefix  ctx in
    runVernac @@
    define_moduletype (freshen_name ~prefix:fname ()) parameters
    (* the we generate module term for given type *)
    (fun ctx -> 
      assume_parameter fname indprec_ty) in  *)
  (* surprisingly, we have an almost fixed constructor 
      For example
        Definition tm_prect :
            ∀ P : tm → Type,
            (∀ i : ident, option (P (tm_var i)))
            → (∀ (i : ident) (t : tm), option (P t) → option (P (tm_abs i t)))
            → (∀ t : tm, option (P t) → ∀ t0 : tm, option (P t0) → option (P (tm_app t t0)))
            → option (P tm_unit) 
            → (∀ t : ident → tm, (∀ i : ident, option (P (t i))) → option (P (tm_k t)))
            → ∀ t : tm, option (P t) :=
        fun P f0 f1 f2 f3 f4 t =>
        tm_rect (fun t => option (P t)) f0 f1 f2 f3 f4 t. 
      of course, when tm_rect becomes stronger, we will need to fill with a bunch of (fun _ .. => None)

      fun P f0 f1 f2 f3 f4 t =>
        tm_rect (fun t => option (P t)) f0 f1 f2 f3 f4 (fun _ .. => None) ... (fun _ .. => None) t. 

      But we still need to know the number of arguments for each (fun _ .. => None)
      thus these number will be parameter_for_None
  *)
    (* copy and paste from Coq source code *)
  let binder_of_name expl { CAst.loc = loc; v = na } =
    CLocalAssum ([CAst.make ?loc na], Default expl,
      CAst.make ?loc @@ CHole (Some (Evar_kinds.BinderType na), Namegen.IntroAnonymous, None)) in 
  let binders_of_names l =
    List.map (binder_of_name Glob_term.Explicit) l in 
  (* string -> lname *)
  let string_to_lname s = 
    CAst.make (Names.Name (Names.Id.of_string s)) in 
  let rec repeat k q = if k = 0 then [] else q :: (repeat (k-1) q) in 
  (* using eliminator for inductive type
      to construct the partial recursor for extensible inductive type *)
  let reduction_from_prec_to_rec 
    (indrectref : fieldpath) 
    (* the field path for the recursor for the inductive type *)
    (parameters_for_None : int list) 
    (* each fun _ _ ... => None, and the number of parameters *)
    : rawterm = 
    let get_lambda_None_from_parameter_number parameter_number = 
      let _None = mkRefC (Libnames.qualid_of_ident (Names.Id.of_string "None")) in
      let emptypattern = CAst.make (Names.Anonymous) in

      let res = mkLambdaCN ((binders_of_names (repeat parameter_number emptypattern))) _None in 
      res in
    let rawterm_sketch (parameters_for_None : int list) : rawterm = 
      let _fn n =
        let _fn = (List.map (fun x -> "f"^ (string_of_int x) ) @@ List.init n (fun x -> x + 1)) in 
        (List.map string_to_lname _fn), 
        (List.map (fun t -> mkRefC (Libnames.qualid_of_ident (Names.Id.of_string t))) _fn) 
        in 
      let _fn_param, _fn_arg = _fn valid_parameter_number in 
      let _t0_P_fn_param = ((string_to_lname "t0") :: (string_to_lname "P") :: _fn_param) in 
      let _t0_P_fn_param = binders_of_names _t0_P_fn_param in 
      (* now we construct fun t => option (P t) *)
      let _P_arg = 
        let parameters = (binders_of_names [string_to_lname "t"]) in 
        let body = 
          let _option = mkRefC (Libnames.qualid_of_ident (Names.Id.of_string "option")) in 
          let _P = mkRefC (Libnames.qualid_of_ident (Names.Id.of_string "P")) in 
          let _t = mkRefC (Libnames.qualid_of_ident (Names.Id.of_string "t")) in 
          mkAppC (_option, [(mkAppC (_P, [_t]))]) in 
        mkLambdaCN parameters body  in 
      let _t0_arg = mkRefC @@ Libnames.qualid_of_ident (Names.Id.of_string "t0") in 
      let _P_fn_args = _P_arg::_fn_arg in 
      let _None_args = List.map get_lambda_None_from_parameter_number parameters_for_None in 
      let _P_fn_None_args = _P_fn_args @ _None_args in 
      let _P_fn_None_t0_args = _P_fn_None_args @ [_t0_arg] in 
      let total_body = mkAppC (mkRefC indrectref, _P_fn_None_t0_args) in 
        mkLambdaCN _t0_P_fn_param total_body in 
    rawterm_sketch parameters_for_None
  in 
  let number_of_cstrs = List.length @@ extract_cstrs_ident ind_sig in 
  let parameters_for_none : int list = 
    (* we first get all the arguments for the recursor for the current inductive type *)
    let current_ind_rec_ty = get_recursor_type_for_indref ctx indref in 
    let all_arguments, _ = collect_argument_and_ret_of_type current_ind_rec_ty in 
    (* only leave with handler argument 
        by removing the first argument, 
        and we get the number of constructors
      *)
    let all_handler_arguments = List.filteri (fun i _ -> i >= valid_parameter_number + 1 && i < number_of_cstrs + 1) all_arguments in 
    (* then calculate the number of parameters for each none *)
    let each_type_of_arguments = List.map (fun ((_, _, ty), _) -> ty) all_handler_arguments in 
    let each_argument_each_type_of_arguments = List.map (fun x -> List.length (fst (collect_argument_and_ret_of_type x))) each_type_of_arguments in 
    (* then delete the first valid stuff *)
    each_argument_each_type_of_arguments in 
  let indrec_ref = 
    let path, ind = to_qualid_name indref in 
    let indrec = Nameops.add_suffix ind "_rect" in 
    let indrec = internal_version_name indrec in 
    _qualid_point_ path indrec in 
  let modterm = 
    let ov_exposed = Set_Fieldpath.add indref @@ Set_Fieldpath.empty in 
    let exposed_parameters = famctx_to_parameters_selfprefix ~ov_exposed ctx in 
    let eT = Some indprec_ty in 
    runVernac @@
    (define_module (freshen_name ~prefix:precname ()) exposed_parameters
      (fun ctx -> 
          define_term precname ~eT (reduction_from_prec_to_rec indrec_ref parameters_for_none)))
  in 
  ModTerm modterm


(* return the (cached) compiled term and type
      for the partial recursor for the indref 
  valid_parameter_number refers to the number of parameters 
      that is considered for partial recursor
  i.e. 

  how many parameters in the signature of the partial recursor
      *)
let generate_partial_recursor_tm
  precname
  (ctx : family_ctxtype) 
  (indref : fieldpath) 
  (indprec_ty : rawterm)
  (valid_parameter_number : int) : coqterm = 
  let open CoqVernacUtils in 
  (* let open Constrexpr_ops in  *)
  let open Constrexpr in 
  (* let fname = 
    let _, indname = to_qualid_name indref in 
    Nameops.add_suffix indname "__prect" in  *)
  (* let indprec_ty, compiled_inddef = compute_partial_recursor_signature fname ctx indref in  *)
  (* let exposed_parameters = 
    let ov_exposed = 
      Set_Fieldpath.add indref @@ Set_Fieldpath.empty in 
    famctx_to_parameters_selfprefix ~ov_exposed ctx in *)
  (* let ind_sig : coq_ind_sigs =     
    match locate_in_fam_type_withself ctx indref with 
    | CoqIndTy {indsigs_from_org_ctx = x, _; _} -> x
    | _ -> cerror ~einfo:__LOC__ () in  *)

  (* let modtype = 
    let parameters = 
      famctx_to_parameters_selfprefix  ctx in
    runVernac @@
    define_moduletype (freshen_name ~prefix:fname ()) parameters
    (* the we generate module term for given type *)
    (fun ctx -> 
      assume_parameter fname indprec_ty) in  *)
  (* surprisingly, we have an almost fixed constructor 
      For example
        Definition tm_prect :
            ∀ P : tm → Type,
            (∀ i : ident, option (P (tm_var i)))
            → (∀ (i : ident) (t : tm), option (P t) → option (P (tm_abs i t)))
            → (∀ t : tm, option (P t) → ∀ t0 : tm, option (P t0) → option (P (tm_app t t0)))
            → option (P tm_unit) 
            → (∀ t : ident → tm, (∀ i : ident, option (P (t i))) → option (P (tm_k t)))
            → ∀ t : tm, option (P t) :=
        fun P f0 f1 f2 f3 f4 t =>
        tm_rect (fun t => option (P t)) f0 f1 f2 f3 f4 t. 
      of course, when tm_rect becomes stronger, we will need to fill with a bunch of (fun _ .. => None)

      fun P f0 f1 f2 f3 f4 t =>
        tm_rect (fun t => option (P t)) f0 f1 f2 f3 f4 (fun _ .. => None) ... (fun _ .. => None) t. 

      But we still need to know the number of arguments for each (fun _ .. => None)
      thus these number will be parameter_for_None

      let's try directly use 
        Definition tm_prect :.. := ltac:(intros; induction 0; eauto; eauto using None).
  *)
    (* copy and paste from Coq source code *)
  let prove_prec_tactic = 
    let tac = CAst.make (Tacexpr.TacArg (Tacexpr.TacCall (CAst.make ( Libnames.qualid_of_ident (Names.Id.of_string "prove_prec") ,[]))) ) in 
    let arg = Genarg.in_gen (Genarg.rawwit Tacarg.wit_tactic) tac in
      CAst.make @@ CHole (None, IntroAnonymous, Some arg) in 
  let modterm = 
    let ov_exposed = Set_Fieldpath.add indref @@ Set_Fieldpath.empty in 
    let exposed_parameters = famctx_to_parameters_selfprefix ~ov_exposed ctx in 
    let eT = Some indprec_ty in 
    runVernac @@
    (define_module (freshen_name ~prefix:precname ()) exposed_parameters
      (fun ctx -> 
          define_term precname ~eT (prove_prec_tactic)))
  in 
  ModTerm modterm








(* TODO:
    currently compute_partial_recursor_and_inj_signatur is invoked during FScheme PRecT

    when PRecT happens, it will impose a cstr_injective function

    but once in the inherited family we have a new constructor,
    we cannot simply/directly add new FScheme PRecT to have new injective proposition because it will lead to duplicate proposition on old constructors

*)

(* TODO:
    currently injecive proposition is implemented by postulation
    we should be able to implement a automatic tactic to solve it
*)
(* let compute_partial_recursor_and_inj_signature 
  precname
  (ctx : family_ctxtype) 
  (indref : fieldpath) : rawterm * coqtype = 

  let rawprecty, ModType precsigty = compute_partial_recursor_signature precname ctx indref in 
  let ModType injsigty = generate_injection_propsig ctx indref in 
  let prefix = Nameops.add_suffix precname "_inj_sig" in
  let combined_mod = 
    let open CoqVernacUtils in 
    let _parameters = famctx_to_parameters_selfprefix  ctx in 
    runVernac @@ 
    (define_moduletype (freshen_name ~prefix ()) _parameters
      (fun ctx ->  
        let* _ = include_mod (apply_mods (pure precsigty) ctx) in 
        let* _ = include_mod (apply_mods (pure injsigty) ctx) in 
        return ())) in
    rawprecty, ModType combined_mod *)

(* 
let generate_partial_recursor_tm_and_injprop
precname
(ctx : family_ctxtype) 
(indref : fieldpath) 
(indprec_ty : rawterm)
(valid_parameter_number : int) : coqterm = 
  let ModTerm prectm = generate_partial_recursor_tm precname ctx indref indprec_ty valid_parameter_number in 
  let ModTerm injprop = generate_injection_prooftms ctx indref in 
  let prefix = Nameops.add_suffix precname "_and_inj" in  
  (* Now we combine two module *)
  let combined_mod = 
    let open CoqVernacUtils in 
    let ov_exposed = Set_Fieldpath.add indref @@ Set_Fieldpath.empty in 
    let exposed_parameters = famctx_to_parameters_selfprefix ~ov_exposed ctx in 
    runVernac @@ 
    (define_module (freshen_name ~prefix ()) exposed_parameters
      (fun ctx ->  
        let* _ = include_mod (apply_mods (pure prectm) ctx) in 
        let* _ = include_mod (apply_mods (pure injprop) ctx) in 
        return ())) in
  ModTerm combined_mod *)


let inhnewrec (i : inh) (fname : name) 
(newctx : family_ctxtype)
((rec_mod, ctx1) : fieldpath typed) (motive : coqterm typed) ((indtype, ctx2) : fieldpath typed) (postfix : string) : inh = 
  let ((inp, oup), ctx), inhs = i in 
  (* TODO: Sanity Check about linkage shape *)
  let newtype = get_coqty_for_recursor fname newctx (rec_mod, ctx1) motive (indtype,ctx2) postfix in 
  let newrtm, newrtm_checker = get_rawtm_for_recursor fname newctx (rec_mod, ctx1) motive (indtype, ctx2) postfix in 
  newrtm_checker newctx;
  let (newoup, ctxb) = famty_ext_ (oup, ctx) fname (RecTy {recty = newtype; recursordef = rec_mod; inductivedef = indtype; motive = motive; rawrecdef = (newrtm, newctx); postfix}) in
  let dummy_field_path = Libnames.qualid_of_string "UNDEFINED" in 
  let newinhs = (fname, CInhNew ( ModTerm (dummy_field_path), ctx ))  :: inhs in 
  assert_cerror ~einfo:"Context Should not change" (fun _ ->ctx = ctxb);
  ((inp, newoup), ctx), newinhs 


let inhnewprec 
  (i : inh) (fname : name)
  indref validcstrs = 
  let ((inp, oup), FamCtx ctx), inhs = i in 
  (* let oldctx = FamCtx ((fname, inp)::ctx) in  *)
  let newctx = FamCtx (((fst (fst oup)), oup)::ctx) in  
  (* TODO : make context correct for motive, indref, recty *)
  let inductivedef = indref in 
  let cstrs = validcstrs in 
  (* we finally decide to generate inj_sig at prec2d, instead of here *)

  (* let precrawty, precty = compute_partial_recursor_and_inj_signature fname newctx inductivedef in  *)
  let precrawty, precty = compute_partial_recursor_signature fname newctx inductivedef in 
  (* let prectm = generate_partial_recursor_tm_and_injprop fname newctx inductivedef precrawty (List.length cstrs) in  *)
  let prectm = generate_partial_recursor_tm fname newctx inductivedef precrawty (List.length cstrs) in
  let newty = 
    let ModTerm prectm = prectm in 
    let prectm = ModType prectm in 
    let precty = precty in  
    let precrawty = precrawty, newctx in 
    let inductivedef = inductivedef, newctx in 
    PRecTy {inductivedef; cstrs; precrawty; prectm; precty} in 
  (* TODO : Check it is well-typed *)
  let (newoup, ctxb) = famty_ext_ (oup, FamCtx ctx) fname newty in
  let newinhs = (fname, CInhNew (prectm, newctx))  :: inhs in 
  ((inp, newoup), FamCtx ctx), newinhs 

let inhnewrec2d 
  (i : inh) (fname : name)
  recursorref indref  = 
  let ((inp, oup), FamCtx ctx), inhs = i in 
  (* let oldctx = FamCtx ((fname, inp)::ctx) in  *)
  let newctx = FamCtx (((fst (fst oup)), oup)::ctx) in  
  (* TODO : make context correct for motive, indref, recty *)

  let inductivedef = indref in 
  let recursordef = recursorref, newctx in 
  (* check if recursor is partial recursor or normal recursor *)
  let rec2dty, rec2dtm = generate_computational_axiom_for_rec newctx ~recursorref ~indref in 
  let newty = 

    let compiledtype = rec2dty, newctx in 
    let compiledterm = rec2dtm in 
    Rec2DTy {inductivedef; recursordef; compiledterm; compiledtype} in 
  (* TODO : Check it is well-typed *)
  let (newoup, ctxb) = famty_ext_ (oup, FamCtx ctx) fname newty in
  let newinhs = (fname, CInhNew (rec2dtm, newctx))  :: inhs in 
  ((inp, newoup), FamCtx ctx), newinhs 



(* Check if a given is inside a given basis  *)
let check_if_field_in_fref (fname : name) (fref : family_ref) : bool = 
  match fref with 
  | ToplevelRef (_, ((_, (_, fty)), _)) ->  
        List.assoc_opt fname fty <> None
  (* | RelativeCtx (_, ((_, fty), _)) -> 
        List.assoc_opt fname fty <> None *)


let check_if_field_in_basis (fname : name) (basis : nested_or_not_inhbase) : bool = 
  match basis with
  | NonNested ((Some fref), _) -> check_if_field_in_fref fname fref
  | InitialInhBase (Some fref) -> check_if_field_in_fref fname fref
  | Nested {shifted = ((_, fty), _); _} -> 
      List.assoc_opt fname fty <> None
  | _ -> false





let pr_familytype ((_, thefamily) : family_type) : Pp.t = 
  let open Pp in 
  let each_fieldp = List.map pr_family_field thefamily in 
    List.fold_left Pp.(++) (str "") each_fieldp

let rec pr_familyterm (fname : name) (thefamily : family_term) : Pp.t = 
  let open Pp in 
  let pr_each_familyterm (each : (name * (family_term_or_coq_term typed))) : Pp.t =
    match each with
    | (fname , (CompiledDef tm, _)) -> (Names.Id.print fname) ++ (strbrk "= Not yet printed") (* ++ (pr_econstr tm) *)
    | (fname , (FamTm (tm), _)) -> pr_familyterm fname tm
    | _ -> nonimplement ~moreinfo:__LOC__()
  in 
  let pr_all_famterm = List.rev @@ List.map pr_each_familyterm thefamily in
  (Names.Id.print fname) 
  ++ (strbrk "= {") 
  ++ (List.fold_left (fun s f -> s ++ (strbrk "\n") ++ f) (strbrk "") pr_all_famterm) 
  ++ (strbrk "\n}") 





(* Generate a functor in the ctx
    and type check it using the generated stuff coincides ith 
inductive_to_famtype 
    it will also construct the partial recursor
*)


let inhnewind (i : inh) (fname : name) ((inddef,ictx) : coq_ind_sig typed) : inh =   
  let ((inp, oup), ctx), inhs = i in 
  (* TODO: Sanity Check about linkage shape *)
  let all_fields = extract_all_ident [inddef] in 
  let indsigs_from_org_ctx =  [inddef], ictx in 
  let inddef_modtype = inductive_to_famtype indsigs_from_org_ctx in 
  let inddef_mod = fst @@ inductive_to_famterm_and_recursor_type indsigs_from_org_ctx in 
  let (newoup, ctxb) = famty_ext_ (oup, ctx) fname (CoqIndTy ({allnames = all_fields; indsigs_from_org_ctx; 
                                                               compiled_inddefty = ModType inddef_modtype; compiled_inddef = ModType inddef_mod;
                                                               registered_prec = Summary.ref ~name:(Utils.fresh_string ~prefix:"registered_prec" ()) None})) in 
  let newinhs = (fname , CInhNew (ModTerm inddef_mod, ictx)) :: inhs in

  assert_cerror ~einfo:"Context Should not change" (fun _ ->ctx = ctxb); 
  ((inp, newoup), ctx), newinhs






let inhextendind (i : inh) (fname : name) ((parentinddef, oldctx) : coq_ind_sigs typed) ((newinddef,current_ctx) : coq_ind_sig typed) (incrementpart : coq_ind_sig typed) registered_prec : inh =   
  let ((inp, oup), ctx), inhs = i in 
  (* TODO: Sanity Check about linkage shape *)
  let newinhs = (fname , CInhExtendInd ((newinddef::parentinddef, current_ctx), incrementpart) ) :: inhs in
  let all_fields = extract_all_ident (newinddef :: parentinddef) in 
  let indsigs_from_org_ctx = (newinddef::parentinddef), current_ctx in 
  let inddef_modtype = inductive_to_famtype indsigs_from_org_ctx in 
  let inddef_mod = fst @@ inductive_to_famterm_and_recursor_type indsigs_from_org_ctx in 
  let parent_ind_fields = extract_all_ident parentinddef in 
  let (newinp, ctxa) = famty_ext_ind (inp, ctx) fname parent_ind_fields (parentinddef, oldctx) registered_prec  in 
  let (newoup, ctxb) = famty_ext_ (oup, ctx) fname (CoqIndTy ({allnames = all_fields; indsigs_from_org_ctx; 
                                                               compiled_inddefty = ModType inddef_modtype; compiled_inddef = ModType inddef_mod;
                                                               registered_prec = Summary.ref ~name:(Utils.fresh_string ~prefix:"registered_prec" ()) registered_prec
                                                               })) in 
  assert_cerror ~einfo:"Context Should not change" (fun _ ->ctx = ctxb); 
  assert_cerror ~einfo:"Context Should not change" (fun _ ->ctx = ctxa); 

  ((newinp, newoup), ctx), newinhs




let check_compatible_indsig_for_newcstrs (parent_ind_trace, oldctx : coq_ind_sigs typed) ((newdef, current_ctx) : coq_ind_sig typed) : coq_ind_sig typed =     
    (* first check any name confliction -- we can also directly let
          Coq check it for us *)
    let parent_ind =   List.hd parent_ind_trace in
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> List.length parent_ind = 1);
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> List.length newdef = 1);
    (* No mutual inductive type *)
    let parent_ind = List.hd parent_ind in 
    let newinddefs = List.hd newdef in 
    (* don't allow notation *)
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> snd parent_ind = []);
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> snd newinddefs = []);
    (* sanity check on newcstrs *)
    let ((_, (old_name, univinfo)), _, _, oldcstrs) = fst parent_ind in 
    let ((wtc, (newcstrs_typename, _)), newparams, newty, newcstrs) = fst newinddefs in 
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> 
      CAst.with_val (fun x -> x) newcstrs_typename = CAst.with_val (fun x->x) old_name);
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> newparams = ([],None));
    let childcstrs = 
      match oldcstrs, newcstrs with 
      | Vernacexpr.Constructors a, Vernacexpr.Constructors b -> 
        let a, _ = rename_ind_cstrs_ctx (a, oldctx) current_ctx in
        Vernacexpr.Constructors (a @ b)
      | _, _ -> cerror ~einfo:("Expect Inductive Constructor!"^__LOC__) () 
    in 
    (* type of child_ind = type of (fst parent_ind) *)
    let child_ind = ((wtc, (newcstrs_typename, univinfo)), newparams, newty, childcstrs) in 
    let child_ind_def = ([(child_ind, [])]) in 
    (child_ind_def, current_ctx)

let combine_indsig_for_newcstrs (parent_ind, oldctx : coq_ind_sig typed) ((newdef, current_ctx) : coq_ind_sig typed) : coq_ind_sig typed =     
    (* first check any name confliction -- we can also directly let
          Coq check it for us *)
    (* let parent_ind =   List.hd parent_ind_trace in *)
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> List.length parent_ind = 1);
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> List.length newdef = 1);
    (* No mutual inductive type *)
    let parent_ind = List.hd parent_ind in 
    let newinddefs = List.hd newdef in 
    (* don't allow notation *)
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> snd parent_ind = []);
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> snd newinddefs = []);
    (* sanity check on newcstrs *)
    let ((_, (old_name, univinfo)), _, _, oldcstrs) = fst parent_ind in 
    let ((wtc, (newcstrs_typename, _)), newparams, newty, newcstrs) = fst newinddefs in 
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> 
      CAst.with_val (fun x -> x) newcstrs_typename = CAst.with_val (fun x->x) old_name);
    assert_cerror_forced ~einfo:__LOC__ (fun _ -> newparams = ([],None));
    let childcstrs = 
      match oldcstrs, newcstrs with 
      | Vernacexpr.Constructors a, Vernacexpr.Constructors b -> 
        let a, _ = rename_ind_cstrs_ctx (a, oldctx) current_ctx in
        Vernacexpr.Constructors (a @ b)
      | _, _ -> cerror ~einfo:("Expect Inductive Constructor!"^__LOC__) () 
    in 
    (* type of child_ind = type of (fst parent_ind) *)
    let child_ind = ((wtc, (newcstrs_typename, univinfo)), newparams, newty, childcstrs) in 
    let child_ind_def = ([(child_ind, [])]) in 
    (child_ind_def, current_ctx)

let inhextendind_incrementally (current_inh : inh) (fname : name) ((parent_ind, oldctx) : coq_ind_sigs typed) (incre_ind_typed : coq_ind_sig typed) registered_prec : inh =   
  
  let complete_def, current_ctx = check_compatible_indsig_for_newcstrs (parent_ind, oldctx) incre_ind_typed in
  let _ = inductive_to_famterm_and_recursor_type (complete_def :: parent_ind, current_ctx) in 
  let _ = inductive_to_famtype (complete_def :: parent_ind, current_ctx) in 
  inhextendind current_inh fname (parent_ind, oldctx) (complete_def, current_ctx) incre_ind_typed registered_prec




module Inductive_expr_order = struct
  open Vernacexpr
  open Constrexpr
  type t =   cumul_ident_decl with_coercion * inductive_params_expr * constr_expr option
  let compare : t -> t -> int = Stdlib.compare
end
module Inductive_expr_Map = Map.Make(Inductive_expr_order)


(* coq_ind_sig is actually untyped code pieces
    when inheritance happens, we need to rename the code piece

  For example, in the
*)

module String_Map = Map.Make(String)

(* The following failed and commented out because
    too costly
  Shift to debruijn if possible *)

(* This will rename the binder of a family_type
    Recall the two rules to construct 
(* *)
let family_type_rename ((oldname, flist) : family_type) (newname : fam_name) : family_type = 
  let rec family_type_rename_family_type 
  ((fname, flist) : family_type) : family_type = 
    if fname = oldname then (newname, family_type_rename_content flist) 
    else (fname, family_type_rename_content flist)
  and family_type_rename_content 
  (flist : (name * (family_type_or_coq_type)) list)  : (name * (family_type_or_coq_type)) list =
  (match flist with 
    | [] -> []
    | (fname, (t))::tail ->
      let newtail = family_type_rename_content tail  in 
      (* let newctx = family_type_rename_ctx oldctx  in  *)
      (* let _ = 
        let open Pp in 
        Utils.msg_notice @@ (str "Renaming ... ") ++ (pr_family_ctxtype oldctx) ++ (str " ") ++ (pr_family_ctxtype newctx)  
      in *)
      let newt = 
        (match t with 
        | FamTy t -> FamTy (family_type_rename_family_type t )
        | CoqTy _
        | MetaDataTy _  -> t
        | CoqIndTy ({indsigs_from_org_ctx = (ind, indctx); _} as t)-> 
          let indctx = family_type_rename_ctx indctx  in
          let indsigs_from_org_ctx =  family_type_rename_indsigs ind, indctx in 
          CoqIndTy {t with indsigs_from_org_ctx = indsigs_from_org_ctx}
        | RecTy {recty; recursordef; inductivedef; motive; postfix} ->
          let oldctx = snd recty in 
          let newctx = family_type_rename_ctx oldctx in 
          let recty = fst recty, newctx in 
          let recursordef = family_type_rename_reference recursordef in 
          let inductivedef = family_type_rename_reference inductivedef in 
          let motive = fst motive, newctx in 
          RecTy {recty; recursordef; inductivedef; motive; postfix}
        | ClosingFactTy (t, oldctx) -> 
          let newctx = family_type_rename_ctx oldctx in 
          ClosingFactTy (t, newctx) 
        | FTheoremTy ({motive; indref; recty; _} as t) ->
          let oldctx = snd recty in 
          let newctx = family_type_rename_ctx oldctx in 
          let motive = (fst motive, newctx) in 
          let indref = family_type_rename_reference (fst indref), newctx in 
          let recty = (fst recty, newctx) in 
          FTheoremTy {t with motive = motive; indref = indref; recty = recty})
      in 
      (fname , (newt)) :: newtail
      ) 
  and family_type_rename_ctx 
  (FamCtx ctx : family_ctxtype)  : family_ctxtype =
  (* assert_cerror_forced ~einfo:"Ctx should not be empty!" (fun _ -> List.length ctx > 0); *)
  (* Utils.msg_notice (pr_family_ctxtype (FamCtx ctx));  *)
  match ctx with 
  | [] -> FamCtx []
  | (h, r) :: t -> 
      if (Names.Id.compare h (fst oldname) = 0) then 
      FamCtx ((fst newname, family_type_rename_family_type r )::t) 
      else  
      let FamCtx t' = family_type_rename_ctx (FamCtx t)  in 
      FamCtx ((h, family_type_rename_family_type r)::t')
  and family_type_rename_reference
  (p : fieldpath) : fieldpath = 
    let (head, tail) =  to_name_qualid p in 
    if (Names.Id.compare head (Nameops.add_prefix "self__" (fst oldname)) = 0) 
    then _point_qualid_ (Nameops.add_prefix "self__" (fst newname)) tail 
    else p
  and family_type_rename_rawterm (rt : rawterm)  : rawterm = 
    let rec replace_head_of_qualid_path _ r =
      let open Constrexpr_ops in 
      let open Constrexpr in 
      (match r with
      | { CAst.loc ; v = CRef (qid,us) } as x when (not (Libnames.qualid_is_ident qid))  ->
          let head, tail = to_name_qualid qid in 
          (* rename the head *)
          if (Names.Id.compare head (Nameops.add_prefix "self__" (fst oldname))) = 0 
          then (mkRefC (_point_qualid_ (Nameops.add_prefix "self__" (fst newname)) tail)) 
          else x
      | cn -> map_constr_expr_with_binders (fun _ _ -> ()) replace_head_of_qualid_path () cn) in 
    let result = replace_head_of_qualid_path () rt in 
    (* let _ = 
      let open Pp in  
      Utils.msg_notice @@ (str "Currently :") ++ (pr_constr_expr result) in  *)
    result
  and family_type_rename_indsigs (indsigs : coq_ind_sigs)  : coq_ind_sigs = 
    List.map (fun x -> family_type_rename_indsig x) indsigs
  and family_type_rename_indsig (indsig : coq_ind_sig) : coq_ind_sig = 
    assert_cerror_forced ~einfo:"Only Support Single Inductive Type!" (fun _ -> List.length indsig = 1);
    let (indsig, _decl_notation) = List.hd indsig in 
    assert_cerror_forced ~einfo:"Doesn't Support Notation Yet!" (fun _ -> List.length _decl_notation = 0);
    let indname, indparam, indty, indconstrs = indsig in
    assert_cerror_forced ~einfo:"Doesn't Support Parameter Yet!" (fun _ -> indparam = ([], None) );
    let newindty = Option.map (fun x -> family_type_rename_rawterm x) indty in 
    let newindconstrs = 
      (match indconstrs with 
      | Vernacexpr.Constructors l -> 
        Vernacexpr.Constructors
        (List.map (fun (coer, (id, csty)) ->
                    (coer, (id,family_type_rename_rawterm csty))
        ) l)
      | _ -> cerror ~einfo:"Doesn't Support Special Constructors Yet!" ()
      ) in 
    ((indname, indparam, newindty, newindconstrs), _decl_notation)::[]
    in 
  let result = (newname, family_type_rename_content flist) in 
  let _ = 
    let open Pp in 
    Utils.msg_notice @@ (pr_fam_name oldname) ++ str "," ++ (pr_fam_name newname) ++ (str "Renaming ... ") ++ (pr_family_type (oldname, flist)) ++ (str "  ->  ") ++ (pr_family_type result) in 
  result *)

(* will do weakening on components
    but will signal exception when applies to famty *)
let wkinh_coqtype_deep 
fname (* This is used during precty *)
~(postpone_exhaustiveness_checking : bool) (* This is when mixin recursor but recursor is not ready *)
((f, ctx) : family_type_or_coq_type typed) 
(newctx : family_ctxtype) : family_type_or_coq_type typed = 
begin match f with 
| FamTy _ 
| SealedFamTy _ -> cerror ~einfo:("Not Expecting Family Here "^__LOC__) ()
| CoqTy _ | CoqTyWithTerm _ | MetaDataTy _ | ClosingFactTy _ -> (f, ctx)
| OvCoqTyWithTerm _ ->
  (* let dependencies = wkinh_dependencies dependencies newctx in 
  OvCoqTyWithTerm {tT with dependencies = dependencies}, newctx   *)
  (* we don't support overridable term here as overriding may happen 
      during inheritance *)
  cerror ~einfo:("Don't Support Overridable Term "^__LOC__) ()
| CoqIndTy ({indsigs_from_org_ctx; _} as tT) ->
  let indsigs_from_org_ctx = wkinh_indsigs indsigs_from_org_ctx newctx in 
  (CoqIndTy {tT with indsigs_from_org_ctx}, newctx)
| RecTy ({recursordef ; inductivedef ; motive; recty; rawrecdef; postfix; _}) ->
  let oldctx = snd rawrecdef in 
  let recursordef = fst @@ wkinh_path (recursordef, oldctx) newctx in 
  let inductivedef = fst @@ wkinh_path (inductivedef, oldctx) newctx in 
  let motive = wkinh_coq_term motive newctx in 
  let recty = wkinh_coq_type recty newctx in 
  let newrtm, rtm_checker = get_rawtm_for_recursor fname newctx (recursordef, newctx) motive (inductivedef, newctx) postfix in 
  (* do a checking here *)
  if (not postpone_exhaustiveness_checking) then rtm_checker newctx else ();
  (* The implementation detail here needs some extra consideration *)
  RecTy {recty ; recursordef; inductivedef ; motive ; rawrecdef = (newrtm, newctx); postfix}, newctx
| Rec2DTy ({recursordef; inductivedef ; _}) ->
  let open Pp in 
  Utils.msg_notice (str "(* Inheriting Rec2D in wkinh_coqtype_deep ..." ++ (Names.Id.print fname) ++ str "*)");
  let oldctx = snd recursordef in 
  let recursordef = wkinh_path recursordef newctx in
  let inductivedef = fst @@ wkinh_path (inductivedef, oldctx) newctx in 
  (* always regenerate ... because the constructors might be more *)
  let new2dty, new2dtm = 
    let indref = inductivedef in 
    let recursorref = fst recursordef in 
    generate_computational_axiom_for_rec newctx ~recursorref ~indref  in
  let compiledterm = new2dtm in 
  let compiledtype = new2dty, newctx in  
    Rec2DTy {inductivedef; recursordef; compiledtype; compiledterm}, newctx
| PRecTy ({inductivedef; precrawty; cstrs; _} as tT) -> 
  let inductivedef = wkinh_path inductivedef newctx in 
  let precrawty = wkinh_rawterm precrawty newctx in 
  let ModTerm prectm = generate_partial_recursor_tm fname newctx (fst inductivedef) (fst precrawty) (List.length cstrs) in
  let prectm = ModType prectm in 
  PRecTy {tT with inductivedef; prectm; precrawty}, newctx 
| FTheoremTy ({indref; recty ; _ } as tT) -> 
  let indref = wkinh_path indref newctx in
  let recty  = wkinh_coq_type  recty newctx in 
  FTheoremTy {tT with indref; recty}, newctx
(* | _ -> nonimplement ~moreinfo:__LOC__ () *)
end

(* this will add an inhinh about fname into i *)
let inhinh_nonfamily  
  (i : inh) (fname : name)
  ~(postpone_exhaustiveness_checking : bool)
  ~(inpty : family_type_or_coq_type typed) : inh = 
  begin match (fst inpty) with 
  | FamTy _ -> cerror ~einfo:("Not supposed to be a family! "^__LOC__) () 
  | OvCoqTyWithTerm _ -> 
    (* TODO: add a check that all the stuff in inherited chain are inherited (not overrided) *)
    Utils.msg_notice (Pp.str "Warning: Inheriting Overridable Term without checking inheritance chain! Only supposed to happen in mixin");
    inhinhgeneric i fname ~inpty
  | _ ->   
    let ((inp, oup), FamCtx ctx), inhs = i in 
    (* TODO: Sanity Check about linkage shape *)
    let newfamname = fst @@ fst oup in 
    let current_oupctx : family_ctxtype = FamCtx ((newfamname, oup)::ctx) in 
    let newinhs = (fname, CInhInherit)  :: inhs in 
    let (newinp, newctx) = famty_ext_  (inp, FamCtx ctx) fname (fst inpty) in 
    let oupty, _ = 
      wkinh_coqtype_deep fname ~postpone_exhaustiveness_checking inpty current_oupctx in 
    let (newoup, _) = famty_ext_  (oup, FamCtx ctx) fname oupty in
    ((newinp, newoup), FamCtx ctx), newinhs
  end; 




module InhMixin :
sig
(* Extend the given inheritance to the given input type *)

(* given an inheritance and a larger domain as the family type
   we return the new inheritance that is with the larger domain
   i.e. it will use inheritance on those domain *)


val inh_extend_inputtype : ?postpone_recursor:bool -> fam_name -> family_type typed -> inh -> inh


val inh_direct_compose : fam_name -> inh -> inh -> inh
(* type inhApp
val input_type  : inhApp -> family_type typed
val output_type : inhApp -> family_type typed
val wrap : inh -> inhApp
val extend_next : inhApp -> inh -> inhApp
val extend_next_several : inhApp -> inh list -> inhApp
val inh_Apply : inhApp -> family_term typed -> family_term typed *)
type inh_classification = INew | IExtend | IInherit | IOverride
val classicy_inhop : inh_op -> inh_classification

val calculate_inh_style_on_expected : ( name list) -> (name list) -> (name list) -> name list

end
= struct

(* this is used to guide the inheritance *)
(* type inh_style = Extend | Inherit | ExtendOrInherit  *)

(* This is to classify the given *)
type inh_classification = INew | IExtend | IInherit | IOverride





let classicy_inhop (i : inh_op) : inh_classification =
  match i with 
  | CInhInherit  -> IInherit
  | CInhNew _ 
  | CInhNewFam _ 
  | CInhNewAxiom _ 
  | CInhFThm {kind = `New; _} -> INew 
  | CInhExtendInd _ 
  | CInhExtendInh _ 
  | CInhFThm {kind = `Extend; _} -> IExtend
  | CInhOverride _ 
  | CInhOverrideFamily _ -> IOverride

(* Remove the last item in the list *)
(* let remove_last (t : 'a list) : 'a list = 
  List.rev (List.tl (List.rev t))
let last (t : 'a list) : 'a = List.hd (List.rev t) *)

(* let rec remained_last (l : 'a list) : ('a list) * 'a =
  match l with
  | [] -> cerror ~einfo:__LOC__ () 
  | [a] -> [], a 
  | h::t -> let remained, last = remained_last t in (h :: remained, last) *)

(* we don't allow duplicate in bigger *)
let is_sublist_of (smaller : name list) (bigger : name list) : bool = 
  let bigger = smap_construct bigger (0 :: List.init (List.length bigger - 1) ((+) 1)) in 
  let bigger_index = Dict_Name.add_seq (List.to_seq bigger) Dict_Name.empty in 
  let smaller_indices = List.map (
    fun x ->
      match Dict_Name.find_opt x bigger_index with 
      | None -> cerror ~einfo:"should be a subset!" ()
      | Some k -> k) smaller in  
  (* Now we have to check smaller_indices is an increasing list *)
  let increasing = 
    if List.length smaller_indices <= 1 then true else
    let in_pairs = smap_construct ~force_same_length:true smaller_indices (List.tl smaller_indices) in
    let all_comparison = List.map (fun (x,y) -> x < y) in_pairs in
    List.fold_left (&&) true all_comparison in
    increasing
(* This function will output the inh_style for each of the expect_input
    Note the order -- we consider expect_input starts from (List.hd expect_input)
      Unlike how family_type encode it   

  We will first do sanity checking -- if it is not possible to extend the orig_input to
      the expected one, then we will raise an error
  We will first make sure orig_inp is a sublist of expect_input
  We will also make sure that the intersection of expect_input and orig_oup will leads to the same sublist in two list

  TLDR, given an inheritance of {A1 A2 ...An} -> {B1 B2 ...} and expect_input
*)
let calculate_inh_style_on_expected (expect_input : name list) (orig_inp : name list) (orig_oup : name list) : 
(* inh_style Dict_Name.t *  *)
(name list) = 
  assert_cerror_forced ~einfo:"expect_input should be a super set of orig_inp" (fun _ -> is_sublist_of orig_inp expect_input);
  (* let orig_inp_set  = Set_Name.add_seq (List.to_seq orig_inp) Set_Name.empty in  *)
  let orig_oup_set  = Set_Name.add_seq (List.to_seq orig_oup) Set_Name.empty in 
  let expect_input_set = Set_Name.add_seq (List.to_seq expect_input) Set_Name.empty in 
  let intersection_expected_inp_oup = Set_Name.inter expect_input_set orig_oup_set in 
  assert_cerror_forced ~einfo:"Expect to have same order dependent on the fields"
  (fun _ -> 
    let sublist_in_orig_oup_set = List.filter (fun x -> Set_Name.mem x intersection_expected_inp_oup) orig_oup in 
    let sublist_in_expect_input = List.filter (fun x -> Set_Name.mem x intersection_expected_inp_oup) expect_input in
    sublist_in_orig_oup_set = sublist_in_expect_input
    );
  (* let result = ref Dict_Name.empty in  *)
  (* Now for each expected_input, we see if *)
    (* If the item is not inside orig_inp and not inside origoup, then we have item maps to Inherit *)
    (* If the item is not inside orig_inp but inside origoup, then we have item maps to Extend *)
    (* If the item is inside orig_inp (then also inside origoup) then it is ExtendOrInherit
        *)
  (* List.iter
  (fun item -> 

    let classification = 
        if  (not (Set_Name.mem item orig_inp_set))
        then if  (not (Set_Name.mem item orig_oup_set)) then Inherit
            else Extend 
        else if  ((Set_Name.mem item orig_oup_set)) then ExtendOrInherit 
            else cerror ~einfo:("Unexpected "^__LOC__) () in
    result := Dict_Name.add item classification (!result)
    ) expect_input; *)
   (* then we construct the final output order of the output fields
      we always make the things from expect_input appears before orig_output, just a priority we choose
    the idea is to slice expect_input/orig_oup into list of list,
            each element in that list of list has one element from orig_inp as the the last element 
            and the list of list must concat into expect_input/orig_oup
      and then everything is easy to see
      
    *)
  let slice_groups (standard : Set_Name.t) (to_slice : name list) : name list list =
    let rec slice_groups_ (standard : Set_Name.t) (to_slice : name list) : name list list =
      (* the invariance for this subfunction is always to_slice == (List.concat return) 
         but ultmately for the outside function, we will filter out the empty list along the way*)
      match to_slice with 
      | [] -> [[]] 
      | h :: t -> 
        let later = slice_groups_ standard t in 
        if (Set_Name.mem h standard) 
        then (
          match later with 
          | [] -> cerror ~einfo:("Not Possible to be empty!"^__LOC__) ()
          | laterh::latert -> [] :: (h :: laterh) :: latert
        )
        else (
          match later with 
          | [] -> cerror ~einfo:("Not Possible to be empty!"^__LOC__) ()
          | laterh::latert -> (h :: laterh) :: latert
        )
    in 
      (* List.filter (fun x -> x <> [])  @@  *)
      (* we don't remove empty here *)
      slice_groups_ standard to_slice 
  in
  let final_output_order = 
    (* but we will use the intersection as the standard *)
    let standard = intersection_expected_inp_oup in 
    let sliced_expect_input = slice_groups standard expect_input in 
    let sliced_orig_output  = slice_groups standard orig_oup in 
    assert_cerror_forced ~einfo:"Expect Sliced Groups same size!" (fun _ -> List.length sliced_expect_input = List.length sliced_orig_output); 
    let sliced_regroup = 
      List.concat @@
      List.map (fun (ga, gb) -> 
                match ga with 
                | [] -> ga@gb
                | gah :: gat ->   
                  if  (Set_Name.mem gah standard) 
                  then (
                      (* assert gb non empty *)
                      assert_cerror_forced ~einfo:__LOC__ (fun _ -> gb <> []);
                      (* assert gb.head is gah *)
                      assert_cerror_forced ~einfo:__LOC__ (fun _ -> Names.Id.to_string @@ List.hd gb = Names.Id.to_string gah);
                      ga@(List.tl gb)
                    )
                  else ga@gb) @@
      smap_construct sliced_expect_input sliced_orig_output in
    sliced_regroup
  in 
  let _ = 
    let open Pp in 

    Utils.msg_notice @@ (str "expect_input :") ++ pr_list_name expect_input;
    Utils.msg_notice @@ (str "orig_inp :") ++ pr_list_name orig_inp;
    Utils.msg_notice @@ (str "orig_oup :") ++ pr_list_name orig_oup;
    Utils.msg_notice @@ (str "final_output_order :") ++ pr_list_name final_output_order

  in 
  (* !result,  *)
  final_output_order 



(* Apparently some new can be lifted to extend, for example
    CInhNewFam, CInhNewInd, CInhNewFThm, when name-conflict
    
  But the remaining new will raise error during name conflict
    CInhNew,(CInhNewRec, CInhNewAxiom, CInhNewMetaData)

  But right now we don't do any lifting to avoid the "diamond" problem
  (I consider diamond problem more of an ambiguouity of late binding)

  Still we use List.rev to make sure the order

  we only deal with grounded inheritance judgement
  *)
let context_length (FamCtx f) = List.length f



let rec inh_extend_inputtype ?(postpone_recursor = false) (newfamname : fam_name) (expect_input : family_type typed) (i : inh) : inh = 
  let current_ctx = snd (fst i) in 
  let postpone_exhaustiveness_checking = postpone_recursor in
  assert_cerror_forced ~einfo:"Expect Same Level of Context" (fun _ -> context_length current_ctx = context_length (snd expect_input));
  let expect_input_names = 
    List.rev @@
    List.map (fun (x,y) -> x) @@ snd (fst expect_input) in 
  let expect_input_name_to_type = 
    let (_, expect_input), _ = unfold_typed_family_type expect_input in
    Dict_Name.add_seq (List.to_seq expect_input) Dict_Name.empty in 
  let orig_input_names, orig_output_names = 
    let (((_, a), (_, b)), _), _ = i in 
    List.rev (List.map fst a), List.rev (List.map fst b) in 
  let output_names = calculate_inh_style_on_expected expect_input_names orig_input_names orig_output_names in
   (*we need a dictionary mapping output name to the inh piece and output type
         *)
  let dict_of_inh = dictionary_of_inh i 
  in
  (* the main algorithm is to iterate over
    output_names, and the corresponding inh piece,
      for each output name there are three cases
      1. the output name appears in the expect_input, but not the inh-dict 
            then we will let this output name be Inherited
      2. the output name doesn't appear in the expect_input, but in the inh-dict,
            then we have to make sure this is a InhNew 
      3. the output appears in both expect_input and inh_dict,
            then it has to be an InhExtension or InhOverride or Inherit itself -- 
                we can lift some of the InhNew into InhExtension but not all kinds of InhNew
                for those unliftable and InhNew, we will have an error
   *)
  let res_inh = 
    let result = 
      let ((basename, _), (_, _)), ctx = fst i in  
      ref (empty_inh basename newfamname ctx) in 
    List.iter (
      fun each_outputname ->
        let _ = 
          let open Pp in 
          Utils.msg_notice @@ (str "(* Combining ") ++ (Names.Id.print each_outputname) ++  (str " *)")
        in 
        let current_ctx = 
          let current_inh = fst !result in 
          let (_, (famname, current_oup)), FamCtx ctx = current_inh in 
          FamCtx ((fst famname, (famname, current_oup))::ctx) in 
        let newinh =
        (match (Dict_Name.find_opt each_outputname expect_input_name_to_type),
              (Dict_Name.find_opt each_outputname dict_of_inh) with 
        | Some inpty, None -> 
          (match inpty with
           | RecTy _, oldctx -> 
            (* inhinhrec ~postpone_recursor !result each_outputname recty (recursordef, oldctx) motive (inductivedef, oldctx) postfix rawrecdef current_ctx *)
           inhinh_nonfamily ~postpone_exhaustiveness_checking !result each_outputname ~inpty
           | _ ->  inhinhgeneric !result each_outputname ~inpty)
        | None, None -> cerror ~einfo:("Unexpected Error "^__LOC__) ()
        | Some inpty, Some (inhinfo, newoupty) -> 
            (* this is the most complicated one, 
               for IInh, IOverride cases are simple  *)

            (match inhinfo, newoupty with
            (* | CInhInherit, (CoqIndTy _, _) -> 
              (match inpty with 
              | (CoqIndTy ({indsigs_from_org_ctx; _} as tT)), ctx -> 
                let indsigs_from_org_ctx = wkinh_indsigs indsigs_from_org_ctx current_ctx in
                let inpty = Some inpty in 
                let oupty = CoqIndTy ({tT with indsigs_from_org_ctx = indsigs_from_org_ctx}) in
                inh_internal ~inpty ~oupty !result each_outputname CInhInherit
              | _ -> cerror ~einfo:("It should be an Inductive Type!"^__LOC__) ())
            | CInhInherit, (FTheoremTy _, _) -> 
              (match inpty with 
              | FTheoremTy {motive; indref; all_handlers; postfix; recty} , _ -> 
                inhinhfthm !result each_outputname motive indref all_handlers postfix recty
              | _ -> cerror ~einfo:("It should be an FTheorem!"^__LOC__) ())
            | CInhInherit, (PRecTy _, _) -> 
              (match inpty with 
              | PRecTy {inductivedef; cstrs; precty; prectm; precrawty} , _ -> 
                inhinhprec  !result each_outputname inductivedef cstrs prectm precty precrawty
              | _ -> cerror ~einfo:("It should be an Partial Recursor!"^__LOC__) ())
            | CInhInherit, (Rec2DTy _, _) -> 
              (match inpty with 
              | Rec2DTy {recursordef; inductivedef; compiledtype; compiledterm} , _ -> 
                let oldrecursorref = recursordef in 
                let oldindref = inductivedef in 
                inhinhrec2d !result each_outputname ~oldrecursorref ~oldindref compiledtype compiledterm
              | _ -> cerror ~einfo:("It should be the Computational Axioms for Recursor!"^__LOC__) ())
            | CInhInherit , (RecTy _, _) ->
              (match inpty with 
              | RecTy {recty; recursordef; inductivedef; motive; postfix; rawrecdef}, ctx -> 
                inhinhrec ~postpone_recursor !result each_outputname recty (recursordef, ctx) motive (inductivedef, ctx) postfix rawrecdef current_ctx 
              | _ ->  cerror ~einfo:("It should be a    Recursor!"^__LOC__) ()) *)
            | CInhInherit, (FamTy _, _ ) ->
              inhinhgeneric !result each_outputname ~inpty
            | CInhInherit, _ -> 
              inhinh_nonfamily ~postpone_exhaustiveness_checking !result each_outputname ~inpty

            | CInhOverride (t,tctx), (CoqTy tT, ctxT) -> 
                  (* inhoverride !result each_outputname (t,tctx) parentty *)
                nonimplement ~moreinfo:__LOC__ ()
            (* For the case of InhExtend, it will be harder
                we need to calculate the correct output type *)
            | CInhExtendInd (_, incr_def), _   -> 
              (match inpty with 
              | (CoqIndTy {indsigs_from_org_ctx; registered_prec; _}), ctx -> 
              let incr_def = wkinh_indsig incr_def current_ctx in 
              inhextendind_incrementally !result each_outputname indsigs_from_org_ctx incr_def (!registered_prec)
              | _ -> cerror ~einfo:("It should be an Inductive Type!"^__LOC__) ())
            | CInhExtendInh inneri, (FamTy _, _) -> 
              (match inpty with 
              | (FamTy (newtT, _)), ctx -> 
                (* let newtT, _ = wkinh_family_type (newtT, ctx) current_ctx in 
                let newinneri = inh_extend_inputtype (newtT, current_ctx) inneri in *)
                let newinneri = wkinh_inh inneri current_ctx in 
                let nested_famname = 
                  let (_, (famname, _)), _ = fst inneri in  
                  famname
                in 
                (* let __org_inputty, _ =  (fst (fst newinneri)) in  *)
                let (wken_newtT) =  wkinh_family_type (newtT, ctx) current_ctx in 
                let newinneri = inh_extend_inputtype nested_famname wken_newtT newinneri in
                  inhextendinh !result each_outputname wken_newtT newinneri
              | _ -> cerror ~einfo:("It should be a Family!"^__LOC__) ())
            | CInhFThm {kind = `Extend; motive = motive_in_coqtm; compiled_handlers =  handlers_in_mod; rec_cstr = rec_constr; all_handlers} , _ ->
              (match inpty with 
                | FTheoremTy {motive; indref; postfix; recty; all_handlers = all_handlers_earlier}, _ -> 
                (* let motive = wkinh_coq_type motive current_ctx in  *)
                let indref = wkinh_path indref current_ctx in 
                let recty  = wkinh_coq_type recty current_ctx in  
                let motive_in_coqtm = wkinh_coq_term motive_in_coqtm current_ctx in 
                let handlers_in_mod = wkinh_coq_term handlers_in_mod current_ctx in 
                let complete_all_handlers = 
                  let earlier_handlers_set = Set_Name.add_seq (List.to_seq all_handlers_earlier) Set_Name.empty in 
                  let added_handlers = List.filter (fun x -> not (Set_Name.mem x earlier_handlers_set)) all_handlers in 
                  all_handlers_earlier @ added_handlers
                in 
                inhnew_or_extend_fthm !result each_outputname (Some inpty) rec_constr handlers_in_mod motive indref recty complete_all_handlers motive_in_coqtm
                | _, _ -> cerror ~einfo:"__LOC__" ()
              ) 
            | _ -> 
              let fieldname = Names.Id.print each_outputname in 
              let inh_info = pr_inh_op inhinfo in 
              let open Pp in 
              let info = (str "Dealing with : ") ++ fieldname ++ (str " using ") ++ inh_info ++ (str "  ") in 
              let info = Pp.string_of_ppcmds info in 
              nonimplement ~moreinfo:(info ^ __LOC__) ()
            )
        | None, Some (newinhop, newoupty) ->
            assert_cerror_forced ~einfo:__LOC__ (fun _ -> classicy_inhop newinhop = INew);
            (* Check the current inh is of style INew *)
            inhnew !result each_outputname ~newinhop ~newoupty)
        in 
        result := newinh
    ) output_names; 
    !result
  in
  let _ = 
    let open Pp in
    let __org_inputty, __org_outputty =  (fst (fst i)) in 
    Utils.msg_notice @@ (str "Initial Inheritance input: ") ++ (pr_family_type __org_inputty);
    Utils.msg_notice @@ (str "Initial Inheritance output: ") ++ (pr_family_type __org_outputty);
    Utils.msg_notice @@ (str "Extension Input Type: ") ++ (pr_family_type (fst expect_input));
    let __new_inputty, __new_ouputty =  (fst (fst (res_inh))) in 
    Utils.msg_notice @@ (str "Extended Inheritance input: ") ++ (pr_family_type __new_inputty);
    Utils.msg_notice @@ (str "Extended Inheritance output: ") ++ (pr_family_type __new_ouputty); in 
  res_inh

(* Directly compose two inh 
    only support inheritance, new and extend now  
    only for mixin 
*)
let rec inh_direct_compose (newfamname : fam_name) (fsti : inh) (nexti : inh) : inh =
  (* check type information first, 
      i.e. output of fst is included in the input of next *)
  assert_cerror_forced ~einfo:"Expect Smaller Input" (fun _ -> 
     let _, fst_out =  fst (fst fsti) in 
     let next_in, _ =  fst (fst nexti) in 
        List.length (snd fst_out) <= List.length (snd next_in));
  let outputty =  (snd (fst (fst nexti))) in 
  (* we just go through the final inh output
      one by one but we also need to 
    don't forget about the order -- we need to reverse it
      *)
  let output_field_names = List.rev (snd outputty) in 
  let fst_dict = dictionary_of_inh fsti in 
  let next_dict = dictionary_of_inh nexti in 
  let fst_inputty = fst (fst (fst fsti)) in 
  (* we also need to handle the input ty *)
  (* let fst_inh_inptys = 
    let (_, inpty_list), _ = fst @@ fst fsti in 
    Dict_Name.add_seq (List.to_seq inpty_list) (Dict_Name.empty)
  in  *)
  (* But an even better idea is to just ignore the inputty,
      and directly use fst.inputty at the very end *)
  (* We make an accumulator *)
  let res_inh = 
    let result = 
      let ((basename, _), (famname, _)), _ = fst (fsti) in
      let ctx = snd @@ fst nexti in  
      ref (empty_inh basename newfamname ctx) 
    in  
    List.iter (
      fun (each_outputfield, oupty) -> 
        let current_ctx = 
          let current_inh = fst !result in 
          let (_, (_, current_oup)), FamCtx ctx = current_inh in 
          FamCtx ((fst newfamname, (newfamname, current_oup))::ctx) in 
        let fst_inhop = 
          let found = Dict_Name.find_opt each_outputfield fst_dict in 
          Option.map fst found in 

        let snd_inhop, expected_fieldtype = 
          Dict_Name.find each_outputfield next_dict in 

        (* we only deal with inh, extend, new
            no overriding allowed
           none _ -> use the other, the second must be new
           _ none -> error
           inh _ ; _ inh -> use the other
           new new -> error
           new extend -> ok -- INew, we don't support it now
           extend new -> error
           extend extend -> ok *)
        let newinh = 
        match fst_inhop with 
        | None -> 
          assert_cerror_forced ~einfo:"New Field expecteed" 
          (fun _ -> classicy_inhop snd_inhop = INew);
          inh_internal ~oupty !result each_outputfield snd_inhop
        | Some fst_inhop ->
          (match (classicy_inhop fst_inhop), 
                 (classicy_inhop snd_inhop) with 

          | IInherit, theother ->
            inh_internal ~oupty !result each_outputfield snd_inhop
          | theother, IInherit -> 
            (* This one, we need to refresh here for  *)
            (* let fst_inhop = 
              match fst_inhop with 
              | CInhNewRec ((r, _), k) -> CInhNewRec ((r, current_ctx), k)
              | _ -> fst_inhop
              in *)
            inh_internal ~oupty !result each_outputfield fst_inhop
            (* nonimplement ~moreinfo:"Unsupported Inheritance composition!" () *)
          | _, INew 
          | INew, IExtend 
            (* legacy code ... *)
            (* -> 
            nonimplement ~moreinfo:"Unsupported Inheritance composition! New Field and Extension Fields!" () *)
            (* Now we support the first new and the second extend
                because stronger mixin needs it *)
          | IExtend, IExtend -> 
            (match fst_inhop, snd_inhop with 
            | CInhNew _, CInhExtendInd ((alldefwithpast, ctx), _) ->
              (* let current_complete_def = List.hd alldefwithpast in  *)
              (* let mixedinhop = CInhNewInd (current_complete_def, ctx) in  *)
              let mixedinhop = nonimplement ~moreinfo:__LOC__ () in 
              inh_internal ~oupty !result each_outputfield mixedinhop
            | CInhExtendInd (dummy, incre_def1) , CInhExtendInd (_, incre_def2) -> 
              let incre_def1 = wkinh_indsig incre_def1 current_ctx in 
              let incre_def2 = wkinh_indsig incre_def2 current_ctx in 
              let incre_def = combine_indsig_for_newcstrs incre_def1 incre_def2 in 
              let mixedinhop = CInhExtendInd (dummy, incre_def) in 
              inh_internal ~oupty !result each_outputfield mixedinhop
            | CInhNewFam (parent, fst0), CInhExtendInh next0 ->
              let fname = fst (fst (fst (fst fst0))) in 
              let nested_inh = inh_direct_compose fname fst0 next0 in
              inh_internal ~oupty !result each_outputfield (CInhNewFam (parent, nested_inh))
            | CInhExtendInh fst0 , CInhExtendInh next0 -> 
              let fname = fst (fst (fst (fst fst0))) in 
              let nested_inh = inh_direct_compose fname fst0 next0 in
              inh_internal ~oupty !result each_outputfield (CInhExtendInh nested_inh)
            | CInhFThm {kind = parentkind; compiled_handlers = handlers_in_mod_old; _},
            CInhFThm {kind = `Extend; motive = motive_in_coqtm; compiled_handlers =  handlers_in_mod_new; rec_cstr = raw_recursor_constr; all_handlers} ->
              let modname, ctx = 
              let ModTerm newmodname, ctx = handlers_in_mod_new in 
              let _, prefix = to_qualid_name newmodname in 
              freshen_name ~prefix (), ctx in 
              let ModTerm newmod = fst handlers_in_mod_new in 
              let ModTerm oldmod = fst handlers_in_mod_old in 
              let combined_mod = 
                let open CoqVernacUtils in 
                runVernac @@ 
                (define_module modname (famctx_to_parameters_selfprefix ctx)
                  (fun ctx ->  
                    let* _ = include_mod (apply_mods (pure oldmod) ctx) in 
                    let* _ = include_mod (apply_mods (pure newmod) ctx) in 
                    return ())) in
              let typed_combined_mod = ModTerm combined_mod, ctx in 
              let extfthm_inhop = CInhFThm {kind = parentkind; motive = motive_in_coqtm; compiled_handlers = typed_combined_mod; rec_cstr = raw_recursor_constr; all_handlers} in 
              inh_internal ~oupty !result each_outputfield extfthm_inhop
            | _ , _-> cerror ~einfo:"Same fields must be of same kind" ()
            )
          | _, _ -> nonimplement ~moreinfo:"Unsupported Inheritance composition!" ()
          ) in 
          result := newinh
    ) output_field_names;
    (* now we attach input-ty into result *)
    let newinh = 
      let incorrect_inp = !result in 
      let ((_, oupty), ctx_) , inhinfo = incorrect_inp in
      let _ = 
        let open Pp in
        Utils.msg_notice @@ (pr_fam_name newfamname) ++ (str " Extended Inheritance input: ") ++ (pr_family_type fst_inputty);
        Utils.msg_notice @@ (pr_fam_name newfamname) ++ (str " Extended Inheritance output: ") ++ (pr_family_type oupty)in 
      ((fst_inputty, oupty), ctx_) , inhinfo 
    in 
    newinh in 
  res_inh 

(* 
type inhApp = {ctx : family_ctxtype; 
               input_type : family_type; 
               output_type : family_type;
               content : inh list }

let input_type  : inhApp -> family_type typed =
  fun x -> (x.input_type, x.ctx)
let output_type : inhApp -> family_type typed =
  fun x -> (x.output_type, x.ctx) 

let wrap (content : inh) : inhApp =
  let ((input_type, output_type), ctx) = fst content in 
  let content = [content] in 
  {ctx; input_type; output_type; content}


let inh_Apply (t : inhApp) : family_term typed -> family_term typed = 
  let rec inh_Apply_ (t : inh list) (i : family_term typed) : family_term typed = 
    match t with 
    | [] -> i
    | h :: tail -> inh_Apply_ tail (inh_apply h i) in 
  fun i -> inh_Apply_ t.content i

let extend_next (first : inhApp) (next : inh) : inhApp = 
  assert_cerror ~einfo:"Should be in the same context" (fun _ -> first.ctx = (snd (fst next)));
  (* assert_cerror_forced ~einfo:"Should be in the same context" (fun _ -> List.length(first.ctx) = List.length(second.ctx)); *)
  let next = inh_extend_inputtype (output_type first) next in 
  let output_type = snd (fst (fst next)) in 
  {ctx = first.ctx; 
  input_type = first.input_type; 
  output_type = output_type; 
  content = first.content @ [next]
  } *)
(* let compose  (first : inhApp)  (second : inhApp) : inhApp =
  assert_cerror ~einfo:"Should be in the same context" (fun _ -> first.ctx = second.ctx);
  (* assert_cerror_forced ~einfo:"Should be in the same context" (fun _ -> List.length(first.ctx) = List.length(second.ctx)); *)
  let extended_second_inh_content = inh_extend_inputtype (output_type first)  in
  {ctx = first.ctx; 
  input_type = first.input_type; 
  output_type = second.output_type; 
  content = first.content @ second.content
  } *)
(* let rec extend_next_several (first : inhApp) (nexts : inh list) : inhApp = 
  match nexts with 
  | [] -> first 
  | h :: tail -> extend_next_several (extend_next first h) tail *)

end


(* let pr_inh_classification (i : InhMixin.inh_classification) : Pp.t = 
  match i with 
  |  *)

(* find output info for the inheritance *)
let rec classify_path_in_inheritance (i : inh) (f : fieldpath) :  InhMixin.inh_classification option = 
  let open InhMixin in 
  let first, remain =  to_name_optionqualid f in 
  let indexing = dictionary_of_inh i in 
  let res = Dict_Name.find_opt first indexing in 
  match remain with 
  | None -> Option.map (fun (res, _) ->  
    let open Pp in 
    Utils.msg_notice @@ (str "Found ") ++ (Names.Id.print first) ++ (str "  ") ++ (pr_inh_op res);
    classicy_inhop res) res 
  | Some remain_p ->
    (match res with 
    | None -> 
      let open Pp in 
      Utils.msg_notice @@ (str "Unfound ") ++ (Names.Id.print first);
      None 
    | Some (CInhInherit, _) -> Some IInherit
    | Some (CInhNewFam (_, inneri), _) -> classify_path_in_inheritance inneri remain_p 
    | Some (CInhExtendInh inneri, _) -> 
      let if_found = classify_path_in_inheritance inneri remain_p in 
      (match if_found with 
      | None -> Some IInherit 
      | Some h -> Some h)
    | _ -> 
      let open Pp in 
      Utils.msg_notice @@ (str "Unfound ") ++ (Names.Id.print first);
      None)


let classify_path_in_inheritances (i : (name * inh) list) (f : fieldpath) = 
  let first, remain =  to_name_optionqualid f in 
  let res = List.assoc_opt first i in 
  match remain with 
  | None -> nonimplement ~moreinfo:__LOC__ ()
  | Some remain_p -> Option.flatten @@ Option.map (fun i -> classify_path_in_inheritance i remain_p) res 

(* return true if all of the dependency fields are inherited,
    return false otherwise
  TODO: we simplified the implementation here that 
        if dependency relies on everything (pins_everything), then we directly return false
            (just assume something is inherited)
        proper way to do it is to traverse all the former overridable fields to see if all of them are inherited
       *)
let overridable_dependency_check_if_all_inherited (i : (name * inh) list) (dependency : pins_dependencies) : bool = 
  let open InhMixin in 
  match dependency with 
  | PinsEverything -> false
  | Pins dependency ->
  Set_Fieldpath.for_all (fun path -> 
    let open Pp in 
    Utils.msg_notice @@ (str "Checking Dependency ") ++ (Libnames.pr_qualid path);
  classify_path_in_inheritances i path = Some IInherit) dependency

(* open InhMixin *)
(* This is one piece of inheritance
    the essence is to gather enough information 
    so that inh... functions can be recovered from inh_piece 
   the important part of inh... functions are that, they are untyped inh 
   they don't require well-typed-ness
    *)


(* type inh_piece = inh_op * (family_type_or_coq_type typed)
type pre_inh = inh_piece Dict_Name.t * name list
let inh_piece_mixin ((ia, iaT) : inh_piece) ((ib, ibT) : inh_piece) : inh_piece = nonimplement ()


let inh_piece_action (action : inh_piece) 
  (fname : name)  
  (baseinh : inh) : inh = nonimplement () 

(* I don't need the following *)
let pre_inh_action (action : pre_inh)
   (baseinh : inh) : inh = nonimplement ()
(* Because we never  *)

let extract_preinh (a : inh) : pre_inh = 
  
  nonimplement ()

let inh_mixin_pre (a : inh) (b : inh) : pre_inh = 
  let ainpfields, aoupfields = 
    let (((_, ainp), (_, aoup)), _), _ = a in 
    List.rev (List.map fst ainp), List.rev (List.map fst aoup)
    in 
  
  let binpfields, boupfields = 
    let (((_, binp), (_, boup)), _), _ = a in 
    List.rev (List.map fst binp), List.rev (List.map fst boup)
  in 
  (* should assert ainpfields = binpfields ？ *)
  (* let newinpfields = binpfields in  *)
  let newoupfields = calculate_inh_style_on_expected binpfields ainpfields aoupfields in 
  let dicta = dictionary_of_inh a in 
  let dictb = dictionary_of_inh b in 
  let result_dict = ref Dict_Name.empty in
  let _ = List.map (
    fun n -> 
      let current_piece = ref [] in 
      if Dict_Name.mem n dicta then 
        current_piece := Dict_Name.find n dicta::(!current_piece) else ();
      if Dict_Name.mem n dictb then 
        current_piece := Dict_Name.find n dictb:: (!current_piece) else ();
      let result_piece = match !current_piece with 
      | current_piece :: [] -> current_piece
      | piecea::pieceb::[] -> inh_piece_mixin piecea pieceb 
      | _ -> cerror ~einfo:__LOC__ () in 
      result_dict := Dict_Name.add n result_piece (!result_dict)
  ) newoupfields in 
  (* Now for each field,  we collect the pieces *)
  (!result_dict, newoupfields)  *)



