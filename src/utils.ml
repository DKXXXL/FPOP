open Ltac_plugin

type name = Names.Id.t 

(* We use a lot of structual comparison
    thus assertions might be slow -- 
    turn if off if you find it too slow   
*)
let dbg_mode = Summary.ref ~name:"DbgMode" (false)


let msg_notice t =
  if !dbg_mode then  
  let open Pp in 
  Feedback.msg_notice @@ (str "(* ") ++ t ++ (str " *)") 
  else ()

type ('key, 'value) smap = ('key * 'value) list 

let map_smap (f : 'a -> 'b) (d : ('key, 'a) smap) : ('key, 'b) smap = 
  List.map (fun (x,y) -> (x, f y)) d



type safecoqtype = Constr.types  (* alias here *)
type safecoqterm = Constr.constr  (* alias here *)

type rawterm = Constrexpr.constr_expr

let compare_qualid (x : Libnames.qualid) y =
  let x = Pp.string_of_ppcmds (Libnames.pr_qualid x) in 
  let y = Pp.string_of_ppcmds (Libnames.pr_qualid y) in 
  String.compare x y

type modtermref = Libnames.qualid 
(* * Names.ModPath.t    *)
type modtyperef = Libnames.qualid 
(* * Names.ModPath.t    *)

type coqtype = ModType of modtyperef 
type coqterm = ModTerm of modtermref 
type coqtermwN = coqterm * name 
type coqtypewN = coqtype * name
(* a module where we only focus on a single field member of that name
    can rougly considered as singleton module *)

let compare_modtermref = compare_qualid
let compare_modtyperef = compare_qualid

let compare_name (x : name) y = Names.Id.compare x y

type module_expr = Constrexpr.module_ast

let get_current_env_sigma () =
  try Vernacstate.Declare.get_current_context ()
  with Vernacstate.Declare.NoCurrentProof ->
    let env = Global.env() in
    Evd.from_env env, env
  [@@ocaml.warning "-3"]

let pr_econstr t =
  let sigma, env = get_current_env_sigma () in
  Printer.pr_econstr_env env sigma t

let pr_constr t =
  let sigma, env = get_current_env_sigma () in
  Printer.pr_constr_env env sigma t
let pr_constr_expr t =
  let sigma, env = get_current_env_sigma () in
  Ppconstr.pr_constr_expr env sigma t

let type_check e  =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, t) = Constrintern.interp_constr_evars env sigma e in
  let (sigma, typ) = Typing.type_of env sigma t in
  EConstr.to_constr sigma typ

let reflect_safeterm e = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let e = EConstr.of_constr e in 
  Constrextern.extern_constr env sigma e

let getglobaldefs (idname_ : string) : Constr.t =
    let open Pp in 
    let open Names.GlobRef in
    let idname = Nametab.global @@ Libnames.qualid_of_string idname_ in
    match idname with 
    | ConstRef cst ->
    let cb = Global.lookup_constant cst in
      (match Global.body_of_constant_body Library.indirect_accessor cb with
      | None -> CErrors.user_err (strbrk "UnBound Definition " ++ (Names.Constant.print cst))
      | Some(e, _, _) ->  e )
    | _ -> CErrors.user_err (Pp.str "LookupDefs can only look for constant definition now")


let ec_to_constr (c : EConstr.t) : Constr.t =
  let env = Global.env () in
  let sigma = Evd.from_env env in
    EConstr.to_constr sigma c

exception FamPluginError of string

let print_stack_depth = 20

let assert_cerror ?(forced = false) ?(einfo = "Assertion Failed") (c : unit -> bool) : unit  =
  if not (forced || !dbg_mode) then () else
  let stack_trace = Printexc.raw_backtrace_to_string @@ Printexc.get_callstack print_stack_depth in 
  let complete_info = 
    (String.concat "\n" 
      [einfo; "Stack Trace:"; stack_trace]) in 
  if not (c ()) 
  then CErrors.user_err (Pp.str complete_info)
  else ()

let assert_cerror_forced ?(einfo = "Assertion Failed") (c : unit -> bool) =
  assert_cerror ~forced:true ~einfo c 



let cerror ?(einfo = "Assertion Failed") () : 'a  =
  assert_cerror_forced ~einfo:einfo (fun _ -> false);
  raise (FamPluginError einfo)

let nonimplement ?(moreinfo="") () = 
  
  cerror ~einfo:("Not Implemented "^moreinfo) ()


let unique_id =
  let counter = ref 0 in 
  fun () -> 
  counter := !counter + 1;
  !counter
(* TODO:
  the following is too sketchy
  Fix it into an appropriate way *)
let fresh_name ?(prefix="v") () : name = 
  (* let open Unix in  *)
  (* let {tm_sec; tm_min ; tm_hour; _} = Unix.gmtime (Unix.time ()) in 
  let time_stamp = tm_hour * 10000 + tm_min * 100 + tm_sec in  *)
  (* let {tms_utime ; _} = times () in 
  let time_stamp = Int64.bits_of_float tms_utime in 
  let to32 (x : Int64.t) : (Int64.t) * int = 
    let open Int64 in
    (div x (of_int 32), to_int (rem x (of_int 32))) in 
  let rec to32List (x : Int64.t) : int list = 
    let open Int64 in 
    if (equal x (of_int 0)) then [] else 
      let a , b = to32 x in 
      b :: to32List a in
  let to_ascii (x : int) =
    if x < 10 then x + 48 else x + 55 in 
  let time_stamp = List.map (fun x -> Char.chr (to_ascii x)) @@ to32List time_stamp in 
  let time_stamp = String.of_seq (List.to_seq time_stamp) in  *)
  let time_stamp = string_of_int @@ unique_id () in 
  (* we use 回 to replace @ to do the name mangling *)
  Names.Id.of_string (prefix ^ "回" ^ time_stamp) 
  
let freshen_name ?(prefix=(Names.Id.of_string "v")) () : name = 
  fresh_name ~prefix:(Names.Id.to_string prefix) ()

let fresh_string ?(prefix="v") () : string = 
  let time_stamp = string_of_int @@ unique_id () in 
  prefix^time_stamp

(* push and pop as sugar wrapping *)
let push l x : unit = l:= x :: !l
let pop l  =
    (match !l with
    | h :: t -> let () = l := t in h
    | _ -> cerror ~einfo:("Currently Not Defining any Family.") ())

let peek l = 
  (match !l with
    | h :: t -> h
    | _ -> cerror ~einfo:("Empty List To Peek from.") ())

(* Return a Coq's String Term *)
let coq_stringterm (s : string) : EConstr.constr =
  let open Constrexpr in 
  let untyped = CAst.make @@ CPrim (String s) in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, typed) =  Constrintern.interp_constr_evars env sigma untyped in 
  let (_, _) = Typing.type_of env sigma typed in 
    typed


let pure (x : modtermref) : module_expr = 
    CAst.make @@ Constrexpr.CMident x 

let apply_mods (operand : module_expr) (args : modtermref list) : module_expr = 
  let open Constrexpr in 
  let args = List.map (fun x -> CAst.make (CMident x)) args in 
  List.fold_left (fun op x ->  CAst.make (CMapply (op, x))) operand args
    
module CoqVernacUtils = struct

type 'a customized =
  | Original of 'a 
  | TrySilent of 'a
  | Thunk of (unit -> ('a customized list))

  


  (* writer monad for vernac *)
(* Currently there are two ways to invoke vernac_expr
1. use translate_vernac and interp_typed_vernac like interp_expr
2. directly use Vernacinterp.interp  
      we will stick with option 2 first because it seems deal with 
        universe stuff as well (see interp_control)

*)
let rec emit_vernac_exprs (ls : Vernacexpr.vernac_expr customized list) : unit =
  
  let emit_vernac_expr ?(on_silence=false) (orgexpr : Vernacexpr.vernac_expr) : unit =
    let _ = msg_notice @@ 
      let open Pp in 
      (Ppvernac.pr_vernac_expr orgexpr) ++ (str ".") in 
    let open Vernacexpr in 
    let expr = {control = []; attrs = []; expr = orgexpr} in 
    let expr = CAst.make expr in 
    let backtrace = Printexc.raw_backtrace_to_string @@ Printexc.get_callstack 5 in 
    let dummyst = Vernacstate.freeze_interp_state ~marshallable:false in 
    try 
      let _ = Vernacinterp.interp ~st:dummyst expr in () 
    with reraise ->
      let info = "Exception Info: " ^ Printexc.to_string reraise ^ "\n" ^ (Pp.string_of_ppcmds @@ CErrors.print reraise) ^ "\n\n" in 
        let ver_exc = "Error Happens during translation\n   " ^ (Pp.string_of_ppcmds @@  Ppvernac.pr_vernac_expr orgexpr) ^ "\n" in 
        let stack_info = backtrace in 
        if on_silence 
        then ()
        else cerror ~einfo:(info ^ ver_exc ^ "Stack Trace \n" ^ stack_info ^ "\n") () in 
  
  let emit_customized_vernac_expr (exp : Vernacexpr.vernac_expr customized) : unit =
    match exp with 
    | Original e -> emit_vernac_expr e 
    | TrySilent e -> 
        emit_vernac_expr ~on_silence:true e 
    | Thunk e ->
        let es = e () in 
        emit_vernac_exprs es
  in 
  match ls with
  | h :: tail -> 
      let _ = emit_customized_vernac_expr h in 
      emit_vernac_exprs tail
  | [] -> () 


  type 'a vernacWriter = (Vernacexpr.vernac_expr customized list) * 'a 

  let vernac_ (e : Vernacexpr.vernac_expr) : unit vernacWriter = ([Original e], ())
  let vernacs_ (e : Vernacexpr.vernac_expr list) : unit vernacWriter = (List.map (fun x -> Original x) e, ())
  let try_ (e : Vernacexpr.vernac_expr list) : unit vernacWriter = (List.map (fun x -> TrySilent x) e, ())
 
  let thunk (e : unit -> unit vernacWriter) : unit vernacWriter = ([Thunk (fun () -> fst @@ e())], ())
  let withtry (e : 'a vernacWriter) : 'a vernacWriter = 
    let rec withtry_ (e : 'b customized list) : 'b customized list =
      List.map 
        (fun x -> 
            match x with 
            | Original x' -> TrySilent x' 
            | TrySilent x' -> x 
            | Thunk e -> Thunk (fun () -> withtry_ @@ e ())
          ) e in 
    let l, e' = e in 
    
    (withtry_ l, e')

  let bind (x : 'a vernacWriter) (f : 'a -> 'b vernacWriter) : 'b vernacWriter =
    let l1, x_ = x in 
    let l2, y_ = f x_ in 
      (l1@l2, y_) 
  let (>>) (x : 'a vernacWriter) (y : 'b vernacWriter) : 'b vernacWriter =
    bind x (fun _-> y)
  let (let*) x f = bind x f

  let runVernac (exec: 'a vernacWriter) : 'a =
    (* let initial = !Flags.we_are_parsing in 
    Flags.we_are_parsing := true; *)
    let exec_, res = exec in 
    let () =  emit_vernac_exprs exec_ in 
    (* Flags.we_are_parsing := initial; *)
    res

  let return (x : 'a) : 'a vernacWriter = ([], x)

  let rec flatmap (xs : 'a vernacWriter list) : unit vernacWriter =
    match xs with 
    | [] -> return ()
    | h::t -> h >> (flatmap t)

  (* Also allow define functor *)
  let define_module 
    (modname : name) (parameters : (name * module_expr) list) 
    (body : modtermref list -> 'x vernacWriter) : modtermref vernacWriter = 
    let open Vernacexpr in 
    let modname_ = CAst.make modname in 
    let parameters_ = 
      List.map 
        (fun (n,m) -> 
          (None, [CAst.make n], (m, Declaremods.DefaultInline))) parameters in 
    
    let inner_parameter =
      List.map 
        (fun (n,m) ->
          Libnames.qualid_of_ident n) parameters in 
    let* _ = vernac_ (VernacDefineModule (None, modname_ , parameters_ , Declaremods.Check [], []) ) in 
    let* _ = body inner_parameter in 
    let* _ = vernac_ (VernacEndSegment modname_) in 
      return @@ Libnames.qualid_of_ident modname


  let define_moduletype 
    (modname : name) (parameters : (name * module_expr) list) 
    (body : modtermref list -> 'x vernacWriter) : modtyperef vernacWriter = 
    let open Vernacexpr in 
    let modname_ = CAst.make modname in 
    let parameters_ = 
      List.map 
        (fun (n,m) -> 
          (None, [CAst.make n], (m, Declaremods.DefaultInline))) parameters in 
    
    let inner_parameter =
      List.map 
        (fun (n,m) ->
          Libnames.qualid_of_ident n) parameters in 
    let* _ = vernac_ (VernacDeclareModuleType (modname_ , parameters_ , [], []) ) in 
    let* _ = body inner_parameter in 
    let* _ = vernac_ (VernacEndSegment modname_) in 
      return @@ Libnames.qualid_of_ident modname


  let define_term 
    (fname : name) ?eT:(eT = None) (e : Constrexpr.constr_expr) : unit vernacWriter = 
    let eT : Constrexpr.constr_expr option = eT in 
    let open Vernacexpr in
    let fname_ = (CAst.make @@ Names.Name.mk_name fname, None)  in 
      vernac_ (VernacDefinition ( (NoDischarge,  Decls.Definition), fname_ , DefineBody ([], None, e , eT)))

  let assume_parameter 
    (fname : name) (eT : Constrexpr.constr_expr) : unit vernacWriter = 
    let open Vernacexpr in
    let fname_ = (CAst.make @@ fname, None)  in 
      vernac_ (VernacAssumption ( (NoDischarge, Decls.Definitional), Declaremods.NoInline , [(false , ([ fname_ ], eT))] ))

  let postulate_axiom 
    (fname : name) (eT : Constrexpr.constr_expr) : unit vernacWriter = 
    let open Vernacexpr in
    let fname_ = (CAst.make @@ fname, None)  in 
      vernac_ (VernacAssumption ( (NoDischarge, Decls.Logical), Declaremods.NoInline , [(false , ([ fname_ ], eT))] ))

  
  
  let include_mod (m : module_expr) : unit vernacWriter = 
    let open Vernacexpr in
      vernac_ (VernacInclude [(m ,Declaremods.DefaultInline )] )

  
  (* this can prove a bunch of lemmas *)
  let define_lemmas (lemmagroups : (name * Constrexpr.constr_expr) list) 
      : unit vernacWriter = nonimplement ()

    (* nonimplement () *)
  
  (* This one is just like define_module except the body is the result of application *)
  let let_mod (modname : name) (mexpr : module_expr) : modtermref vernacWriter = 
    let open Vernacexpr in 
    let modname_ = CAst.make modname in 
    let* _ = vernac_ (VernacDefineModule (None, modname_ , [] , Declaremods.Check [], [(mexpr , Declaremods.DefaultInline)]) ) in 
      return @@ Libnames.qualid_of_ident modname


(* This part is because, in module signature (module type)
      we will sometime have nested module
    For example,
  Module Type B. End B.
  
  Module Type A.

  Module B_. // this part needs to be a "module", and use include in the body 
    Include B.
  End B.

  End A.

  This is not a primitive operation
*)
  let include_mod_in_current_modtype 
    (modname : name) 
    (inner_modtype : module_expr) : modtyperef vernacWriter = 
    let open Vernacexpr in
      define_module modname [] 
      (fun ctx ->
          vernac_ (VernacInclude [(inner_modtype ,Declaremods.DefaultInline )] ))



end 



let _point_qualid_ (f : name) (path : Libnames.qualid)  : Libnames.qualid = 
  let path, base =  Libnames.repr_qualid path in 
  let newpath =  List.append (Names.DirPath.repr path) [f] in
  Libnames.make_qualid (Names.DirPath.make newpath) base 

let _point_optionqualid (f : name) (path : Libnames.qualid option) : Libnames.qualid = 
  match path with 
  | None -> Libnames.qualid_of_ident f 
  | Some x -> _point_qualid_ f x

let _qualid_point_ (path : Libnames.qualid option) (f : name) : Libnames.qualid = 
  match path with 
  | Some path ->
    let path, base =  Libnames.repr_qualid path in 
    let path = base :: Names.DirPath.repr path in 
    let path = Names.DirPath.make path in 
    Libnames.make_qualid path f
  | None -> Libnames.qualid_of_ident f

let _qualid_qualid_ (headpath : Libnames.qualid) (tailpath : Libnames.qualid) : Libnames.qualid = 
  let tailpath1, base = Libnames.repr_qualid tailpath in 
  let headpath_in_list = 
    let headpath1, headpath2 = Libnames.repr_qualid headpath in 
    let headpath1 = Names.DirPath.repr headpath1 in 
    headpath2 :: headpath1 in 
  let tailpath1 = Names.DirPath.repr tailpath1 in 
  let newtailpath1 = tailpath1 @ headpath_in_list in 
  Libnames.make_qualid (Names.DirPath.make newtailpath1) base


(* extract a path into (path "." name) *)
let to_qualid_name (path : Libnames.qualid) : Libnames.qualid option * name = 
  let open Libnames in 
  if qualid_is_ident path then (None, qualid_basename path) else 
    let (prefix_path, base) = Libnames.repr_qualid path in 
    match Names.DirPath.repr prefix_path with 
    | [] -> cerror ~einfo:"Unexpected Error" () 
    | newbase :: remained -> 
      (Some (make_qualid (Names.DirPath.make remained) newbase), base)

(* extract a path into (name "." path) *)
let to_name_qualid (path : Libnames.qualid) : name * Libnames.qualid = 
  let (prefix_path, base) = Libnames.repr_qualid path in 
  let prefix_path = Names.DirPath.repr prefix_path in 
  let rec extract_final l =
    match l with 
    | [] -> nonimplement ~moreinfo:__LOC__ () 
    | [t] -> (t, [])
    | h :: t -> 
      let (final, t') = extract_final t in 
      (final, (h :: t')) in 
  let (startingpoint, remained) = extract_final prefix_path in 
  let remained = Libnames.make_qualid (Names.DirPath.make remained) base in 
  (startingpoint, remained)

let to_name_optionqualid (path : Libnames.qualid) : name * (Libnames.qualid option) =
  let open Libnames in 
  if qualid_is_ident path then (qualid_basename path, None) else 
  let head, tail = to_name_qualid path in
  (head, Some tail)

let wrap_modtype_into_module_modtype 
    (modname : name) 
    (inner_modtype : modtyperef) 
    parameters : modtyperef CoqVernacUtils.vernacWriter = 
    let open CoqVernacUtils in 
    let modname1 = freshen_name ~prefix:modname () in 
      define_moduletype modname1 parameters
      (fun ctx ->
        define_module modname []
          (fun _ ->
            let applied_modtype = apply_mods (pure inner_modtype) ctx in 
              include_mod applied_modtype
            )
        )




(* Given 
    Module A (ctxs : Ctxs ...). End A. 
  
   return a new module that wraps inner part 
      into a module
   Module A_ (ctxs : Ctxs ...). 
        Module A'.
        Include A(ctxs). 
        End A'.
   End A_.
  *)
let wrap_inner_mod 
    (modname : name) 
    (inner_mod : modtermref) 
    parameters : modtyperef CoqVernacUtils.vernacWriter = 
    let open CoqVernacUtils in 
    let modname1 = freshen_name ~prefix:modname () in 
      define_module modname1 parameters
      (fun ctx ->
        define_module modname []
          (fun _ ->
            let applied_mod = apply_mods (pure inner_mod) ctx in 
              include_mod applied_mod
            )
        )


let smap_assoc ?(einfo="") (a : 'a) (l : ('a * 'b) list) : 'b = 
  match List.assoc_opt a l with 
  | Some b -> b 
  | None -> cerror ~einfo:("Assoc Unfound! "^einfo) ()


let smap_construct ?(force_same_length = false) (a : 'a list) (b : 'b list) : ('a * 'b) list =
  
  let a, b = 
    if force_same_length then 
      let len = min (List.length a) (List.length b) in 
      let a = List.filteri (fun i _ -> i >= 0 && i < len) a in 
      let b = List.filteri (fun i _ -> i >= 0 && i < len) b in 
      (a, b) 
    else (a, b) 
  in 
  assert_cerror_forced ~einfo:"Not Same Length!" (fun _ -> List.length a = List.length b);
  List.combine a b



let cbn_term t = 
  let env = Global.env() in 
  let sigma = Evd.from_env env in 
  let (sigma, internalized) = Constrintern.interp_constr_evars env sigma t in
  let normalized_intern = Cbn.norm_cbn CClosure.allnolet env sigma internalized in
  let normalized_intern = EConstr.to_constr sigma normalized_intern in 
  (* let reflected = reflect_safeterm normalized_intern in 
  reflected *)
  normalized_intern

let cbn_term_no_delta t = 
  let env = Global.env() in 
  let sigma = Evd.from_env env in 
  let (sigma, internalized) = Constrintern.interp_constr_evars env sigma t in
  let normalized_intern = Cbn.norm_cbn CClosure.betaiotazeta env sigma internalized in
  let normalized_intern = EConstr.to_constr sigma normalized_intern in 
  (* let reflected = reflect_safeterm normalized_intern in 
  reflected *)
  normalized_intern

let cbv_all t =
  let env = Global.env() in 
  let sigma = Evd.from_env env in 
  let (sigma, internalized) = Constrintern.interp_constr_evars env sigma t in
  let normalized_intern = Tacred.compute env sigma internalized in
  let normalized_intern = EConstr.to_constr sigma normalized_intern in 
  (* let reflected = reflect_safeterm normalized_intern in 
  reflected *)
  normalized_intern

let cbv_beta t =
  let env = Global.env() in 
  let sigma = Evd.from_env env in 
  let (sigma, internalized) = Constrintern.interp_constr_evars env sigma t in
  let normalized_intern = Tacred.cbv_beta env sigma internalized in
  let normalized_intern = EConstr.to_constr sigma normalized_intern in 
  (* let reflected = reflect_safeterm normalized_intern in 
  reflected *)
  normalized_intern


let cbv_unfold_def t =
  let env = Global.env() in 
  let sigma = Evd.from_env env in 
  let (sigma, internalized) = Constrintern.interp_constr_evars env sigma t in
  let normalized_intern = Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.delta env sigma) internalized in
  let normalized_intern = EConstr.to_constr sigma normalized_intern in 
  (* let reflected = reflect_safeterm normalized_intern in 
  reflected *)
  normalized_intern

(* 
let testCstFunction () : unit =
  let open Constrexpr_ops in 
  let x = Names.Id.of_string "x" in 
  let f = mkLambdaC ([ CAst.make @@ Names.Name.mk_name x ], default_binder_kind, , mkIdentC x) *)


(* let testmkString (f : name) =
  let open Constrexpr in 
  let u = CAst.make @@ CPrim ( Constrexpr.String (Names.Id.to_string f)) in 
  simple_check u  *)

  
let testQualid (f : Libnames.qualid) : unit = ()



let testConstrQualid (f : rawterm) : unit =
  let open CAst in 
  let check = 
    match f.v with 
    | Constrexpr.CRef _ -> true
    | _ -> false in
  let _ = msg_notice @@ Pp.str ( "f is a CRef?" ^ Bool.to_string check) in 
  match f.v with 
  | Constrexpr.CRef (q, _) -> 
    (match Constrintern.intern_reference q with 
      | None -> ()
      | Some _ -> msg_notice @@ Pp.str "We can locate f using intern_reference")
  | _ -> ()

let verify_module (e : Libnames.qualid) : bool =
    (* let open CAst in  *)
    (* let open Constrexpr in  *)
    let _ = Nametab.locate_module e in true
    (* let m = CAst.make @@ CMident e in 
    let me, kind, cst = Modintern.interp_module_ast (Global.env()) Modintern.ModAny m in  *)
    (* kind <> Modintern.ModAny *)

(* let testQualidString (f : name) : unit = 
  let f = Names.Id.to_string f in 
  let qf = Libnames.qualid_of_ident (Names.Id.of_string f) in 
  let _ = msg_notice @@ Pp.str ( f ^ "  is being analyzed") in 
  let _ = msg_notice @@ Pp.str @@ "Module verified"  ^ Bool.to_string (verify_module qf) in 
  () *)


(* let testCstSigma () : unit =
  let env() = Global.env () in
  let sigma = Evd.from_env (env()) in
  let sigmaty_id =  Coqlib.lib_ref "core.sigT.type" in 
  let (sigma, sigmaty) = Evd.fresh_global (env()) sigma sigmaty_id  in
  let unitty_id = (Coqlib.lib_ref "core.True.type") in 
  let natid = (Coqlib.lib_ref "num.nat.type") in 
  let (sigma, truety) = Evd.fresh_global (env()) sigma unitty_id in 
  let (sigma, natty)  = Evd.fresh_global (env()) sigma natid in 
  (* let (sigma, truety2) = Evd.fresh_global env sigma unitty_id in  *)
  let bodyT =  EConstr.mkLambda(Context.nameR (Names.Id.of_string "x"), truety,
  natty) in 
  let csted = EConstr.mkApp (sigmaty, [| truety ; bodyT |]) in 
  let sigma, the_type = Typing.type_of ~refresh:true (env()) sigma csted in
  msg_notice (pr_econstr csted);
  msg_notice (pr_econstr the_type) *)


  
(* let test_proof (fname : name) (goal : rawterm) (proof : Tacexpr.raw_tactic_expr) =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let (evd, type_checked_goal) = Constrintern.interp_constr_evars env evd goal in 
  let info = Declare.Info.make () in
  let cinfo =
    Declare.CInfo.make ~name:fname ~typ:type_checked_goal () in 
  let ongoing_proof = Declare.Proof.start ~info ~cinfo evd in 
  let pfs = Tacinterp.interp proof in 
  let (ongoing_proof, _) = Declare.Proof.by pfs ongoing_proof in 
  ongoing_proof *)

(* let test_proof2 (fname : name) (goal : rawterm) (proof : Tacexpr.raw_tactic_expr) =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let (evd, type_checked_goal) = Constrintern.interp_constr_evars env evd goal in 
  let info = Declare.Info.make () in
  let cinfo =
    Declare.CInfo.make ~name:fname ~typ:type_checked_goal () in 
  let ongoing_proof = Declare.Proof.start ~info ~cinfo evd in 
  let pfs = Tacinterp.interp proof in 
  let (proof, _) = Declare.Proof.by pfs ongoing_proof in 
  let _ = Declare.Proof.save_regular ~proof ~opaque:Vernacexpr.Opaque ~idopt:None in  
  () *)



let simple_check e : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, t) = Constrintern.interp_constr_evars env sigma e in
  let (sigma, typ) = Typing.type_of env sigma t in
  msg_notice (Printer.pr_econstr_env env sigma t);
  msg_notice (Printer.pr_econstr_env env sigma typ)


type fieldpath = Libnames.qualid

  (* assume m1 and m2 are in the same context 
      we will construct one module to `inline` m1 and m2 to do conversion checking 
    used during overriding -- to check the overridable term has the same type as the overridden
    *)
  let conversion_check 
    (m1 : modtermref) (f1 : fieldpath) (m2 : modtermref) (f2 : fieldpath) ctx : bool = nonimplement () 
  
  
  
  
  module FamTyID : sig
    type famtyid
    val newfid : unit -> famtyid
    val pr_famtyid : famtyid -> Pp.t
    val compare : famtyid -> famtyid -> int
  end = struct
    type famtyid = int
    let newfid = unique_id 
    let pr_famtyid x = Pp.str (string_of_int x)
    let compare = compare
  end
  
  
open FamTyID
(* type famtyid = FamTyID.t *)
type fam_name = name * famtyid
let dummy_famname : fam_name = (Names.Id.of_string "回回回回回回", newfid())

module Fieldpath_Ord = struct
  type t = fieldpath
  let compare a b : int = 
    let a = Pp.string_of_ppcmds (Libnames.pr_qualid a) in 
    let b = Pp.string_of_ppcmds (Libnames.pr_qualid b) in 
    String.compare a b 
end

module Set_Fieldpath = Set.Make(Fieldpath_Ord)
module Set_Name = Set.Make(Names.Id)

type pins_dependencies = PinsEverything | Pins of (Set_Fieldpath.t)
  

let to_pins_dependencies (expose : Set_Fieldpath.t option) : pins_dependencies option = 
match expose with 
| None -> None 
| Some e -> Some (Pins e) 


type 'a stack = 'a list

module CoqIndSigUtil = struct

type coq_ind_sig = (Vernacexpr.inductive_expr * Vernacexpr.decl_notation list) list

type coq_ind_sigs = coq_ind_sig stack
  
(* Extract type information and 
    constructor information out of a inductive signature
*)
let extract_type_and_cstrs (s : Vernacexpr.inductive_expr) : ((name * (rawterm option)) * ((name * rawterm) list)) =
  let (indtypename, ind_params, indtype, cstrlist) = s in 
  assert_cerror ~einfo:"Doesn't Support Inductive Parameter yet" (fun _ -> fst ind_params = [] && snd ind_params = None);
  let _, (indtypename, _) = indtypename in
  let indtypename = CAst.with_val (fun x -> x) indtypename in 
  let each_constr ((_, (cname, cty)) : Vernacexpr.constructor_expr) : (name * rawterm) =
    let cname = CAst.with_val (fun x -> x) cname in (cname , cty) in 
  match cstrlist with 
  | Vernacexpr.Constructors cstrlist -> (indtypename, indtype), (List.map each_constr cstrlist)
  | _ -> cerror ~einfo:"Incorrect Inductive Signature" ()

let extract_all_ident (inddef : coq_ind_sigs) : name list = 
  (* TODO: deal with all the coqindsig later *)
  let inddef = List.hd inddef in 
  let allnames = List.map (fun k -> extract_type_and_cstrs @@ fst k) inddef in 
  let typenames = List.map (fun x -> fst (fst x)) allnames in 
  let cstnames = List.map fst @@ List.concat_map snd allnames in 
  let allname = typenames @ cstnames in 
  allname


let extract_type_ident (inddef : coq_ind_sigs) : name list = 
  (* TODO: deal with all the coqindsig later *)
  let inddef = List.hd inddef in 
  let allnames = List.map (fun k -> extract_type_and_cstrs @@ fst k) inddef in 
  let typenames = List.map (fun x -> fst (fst x)) allnames in 
  typenames

let extract_cstrs_ident (inddef : coq_ind_sigs) : name list = 
  (* TODO: deal with all the coqindsig later *)
  let inddef = List.hd inddef in 
  let allnames = List.map (fun k -> extract_type_and_cstrs @@ fst k) inddef in 
  let cstrnames = List.concat_map (fun x -> List.map fst (snd x)) allnames in 
  cstrnames

end


type rawterm_or_tactics = 
  RawTerm of rawterm 
  | ProofScript of {script : Tacexpr.raw_tactic_expr; 
                    starting_plain : bool ; 
                    opacity : Vernacexpr.opacity_flag}
  (* | PlainProofScript of Tacexpr.raw_tactic_expr  *)
  (* | Eqdecidability *)

let open_new_module (modname : name) params = 
  let open CoqVernacUtils in 
  let res = (Vernacexpr.VernacDefineModule (None, (CAst.make modname) , params , Declaremods.Check [], [])) in 
  runVernac @@ 
  vernac_ res; 
  let open Pp in 
  msg_notice @@ Ppvernac.pr_vernac_expr res ++ (str ".")

let close_defined_module (modname : name) = 
  let open CoqVernacUtils in 
  runVernac @@ 
  vernac_ (Vernacexpr.VernacEndSegment (CAst.make modname)) 


