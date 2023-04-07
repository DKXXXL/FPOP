

Require Import List.
Require Import String.

Open Scope string_scope.
(* This above is currently very important
    Our plugin relies on it to construct string literal
  TODO: Fix it.
*)

(* Make Interop of plugin easier *)
(* Polymorphic Definition RawSig := (list (string*Type)).
Polymorphic Definition nilsig : RawSig := nil.
Polymorphic Definition consig (id : string) (T : Type) (tail : RawSig) := (id,T)::tail.


Polymorphic Definition RecordTy : (list (string*Type)) -> Type := SignatureDef.RC.
Polymorphic Definition emptyRec : RecordTy nil := SignatureDef.empty.
Polymorphic Definition addRec   (id : string) (T : Type) (t : T) {l} (rec : RecordTy l) : RecordTy (consig id T l) := SignatureDef.add_field id T t rec.

(* The following won't work without universe polymorphism *)
(* Compute let b := {_ : RecordTy nilsig & nat} in  ("a",b)::nilsig.  *)
Polymorphic Definition b :=  let b := {_ : RecordTy nilsig & nat} in  consig "a" b nilsig.
Polymorphic Definition c := RecordTy b.

Register RawSig as fampoly.sig.rawsig.
Register nilsig as fampoly.sig.nilsig.
Register consig as fampoly.sig.consig.
Register RecordTy as fampoly.recordty.type.
Register emptyRec as fampoly.recordty.nilrec.
Register addRec as fampoly.recordty.addrec. *)

Axiom cheat : forall {A : Type}, A.

Ltac __cheat := eapply cheat; eauto.

Ltac __unfold_ftheorem_motive := 
  match goal with 
  | [ |- ?h ?t] => try unfold h; try unfold t 
  end.

Ltac generalize_pose c :=
  generalize c; intro.

Ltac prove_prec :=
  intros x; induction x; eauto; eauto using None.

Ltac unfold_nested G :=
  match G with 
  | True => idtac
  | (prod (?h ?a) ?G2)  => unfold h; unfold a; unfold_nested G2  
  end.

(* Need a recursive unfolding *)
Ltac __unfold_ftheorem_motive_nested := 
  match goal with 
  | [ |- (prod ?a ?b) ] => unfold_nested (prod a b)
  | _ => idtac
  end.


  


Declare ML Module "fampoly_plugin".

(* Following is about the discriminate tactic *)

Lemma transpose_f :
  forall {U V a b} (f : U -> V), a = b -> f a = f b.
intros U V a b f h; destruct h; eauto. Defined.

Lemma f_eq_apply:
  forall {U V} {f g : U -> V} a, f = g -> f a = g a.
intros U V f g a h; destruct h; eauto. Defined.


(* This one is the constant function
    for option *)
Ltac confun F n :=
  match F with 
  | (?a -> ?b) => let cf := confun b n in constr:((fun _ : a => cf))
  | _ => constr:(Some n)
  end.


(* add_hypo is pose but without concrete definition *)
Ltac add_hypo proof H :=
  pose (proof) as H ; 
  generalize H; 
  clear H; intros H.


(* ins_eqf will instantiate both sides of a equality
    for f = g 
    using confun  
  *)
Ltac ins_eqf heq n :=
  match type of heq with 
  | ?a = ?b => 
    match type of a with
    | ?x -> _ => let cf := confun x (n+1) in
                let neweq := constr:(f_eq_apply cf heq) in 
                ins_eqf neweq (n+2)
    | _ => constr:(heq)
    end
  end.


Ltac frec_eval prect := repeat (frec_eval_onestep prect; cbn in *).
(* prec_discriminate is the main discriminate function
    unlike discriminate
    we need specify the partial recursor and the incorrect equation
*)
Ltac prec_discriminate prect heq :=
  let prec__ := fresh "prec" in 
  pose (fun t => prect t (fun _ => nat)) as prec__; 
  cbn in *;
  let H_ := fresh "H" in 
  let jj := ins_eqf (transpose_f prec__ heq) 0 in add_hypo jj H_; 
  unfold prec__ in *; 
  (* cbv in *;  *)
  frec_eval prect;
  (* This cbv should be frec_eval instead *)
  discriminate; fail.



(* A Hack to support finjection *)
Ltac finjection H :=
  let cstr := 
    match type of H with 
    | (?T _ = _) => T
    | (?T _ _ = _) => T
    | (?T _ _ _= _) => T
    | (?T _ _ _ _ = _) => T
    | (?T _ _ _ _ _ = _) => T
    | (?T _ _ _ _ _ _ = _) => T
    | (?T _ _ _ _ _ _ _ = _) => T
    | (?T _ _ _ _ _ _ _ _ = _) => T
    | (?T _ _ _ _ _ _ _ _ _= _) => T
    | (?T _ _ _ _ _ _ _ _ _ _ = _) => T
    | (?T _ _ _ _ _ _ _ _ _ _ _ = _) => T
    | (?T _ _ _ _ _ _ _ _ _ _ _ _ = _) => T 
    end in finjection_on cstr H.

(* A Hack to support fdiscriminate *)
Ltac fdiscriminate heq :=
  match type of heq with 
  | ?X = _ => let typ := type of X in fdiscriminate_by heq typ
  end.

