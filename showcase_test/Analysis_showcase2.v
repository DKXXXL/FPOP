Require Import Fampoly.LibTactics.
Require Import Fampoly.Loader.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Structures.DecidableTypeEx.
Require Import Equalities Orders.
Require Import FSets FMaps.
Require Import Coq.FSets.FMapWeakList.
Require Import String.

From Coq Require Import Nat.
Require Import Coq.Init.Datatypes.

Import Notations.
Import ListNotations.

Module Analysis_showcase.

Definition ident := nat.

Axiom non_implement : forall {T : Type}, T.


Ltac destruct_ALL :=
  repeat 
    match goal with
    | [h : _ \/ _ |- _ ] => destruct h; subst; eauto    
    | [h : _ + _ |- _ ] => destruct h; subst; eauto
    | [h : _ * _ |- _ ] => destruct h; subst; eauto
    | [h : _ /\ _ |- _ ] => destruct h; subst; eauto
    | [h : exists _ , _ |- _ ] => destruct h; subst; eauto
    | [h : {_ & _} |- _ ] => destruct h; subst; eauto
    | [h : {_ & _ & _} |- _ ] => destruct h; subst; eauto
    | [h : Some _ = Some _ |- _] => inversion h; subst; eauto
    | [h : {_} + {_} |- _] => destruct h; subst; eauto
    end.

Module Type LATTICE.

Parameter t : Type. 
Parameter join : t -> t -> t.
Parameter le : t -> t -> Prop.
Parameter le_refl : forall x, le x x.
Parameter le_trans : forall x y z, le x y -> le y z -> le x z.
Parameter join_le_left:
  forall x y, le x (join x y).
Parameter join_le_right:
  forall x y, le y (join x y).

Parameter join_monoton:
  forall x y l,
    le x y ->
    le (join l x) (join l y).

Parameter le_antisymm :
  forall x y,
    le x y ->
    le y x ->
    x = y.
End LATTICE.

Module Type StrictDecidableType (E : DecidableType).
Parameter streq : 
  E.eq  = eq.
End StrictDecidableType.

Module Map_LATTICE (E:DecidableType) (SE : StrictDecidableType E) (L : LATTICE) 
(* <: LATTICE *)
.

Module M := FMapWeakList.Make(E).

Module MProp := WProperties_fun E M.
Module MFact := WFacts_fun E M.

Include SE.
Print E.

(* Print streq. *)
Definition t := M.t L.t.



Definition le (m1 : t) (m2 : t) :=
  forall k v,
  M.MapsTo k v m1 ->
  exists v', M.MapsTo k v' m2 /\ L.le v v'.

(* Somehow Coq's StdLib doesn't do this quotient ... 
    I will cheat here *)
Axiom Equal_as_quotient:
  forall (x y : t),
    M.Equal x y <-> x = y.

Lemma Map_to_unique:
  forall k v0 v1 (x : t),
    M.MapsTo k v0 x ->
    M.MapsTo k v1 x ->
     v0 = v1.
  intros. forwards*: M.find_1. clear H0.
  forwards*: M.find_1. clear H.
  rewrite H1 in *. injection H0; subst; eauto.
Qed.   

Ltac unify_map_to :=
  match goal with 
  | [H : M.MapsTo ?k _ ?m, H1 : M.MapsTo ?k _ ?m |- _] =>
    forwards*: (Map_to_unique _ _ _ _ H H1);subst; clear H1
  end.

Lemma le_antisymm :
  forall x y,
  le x y ->
  le y x ->
  x = y.

unfold le. intros x y H H0.
rewrite <- Equal_as_quotient. intro k.
destruct (M.find (elt:=L.t) k x) eqn:heq1.
forwards*: M.find_2.
forwards*: H. destruct_ALL.
forwards*: H0. destruct_ALL.
unify_map_to.
forwards*: L.le_antisymm; subst; eauto. symmetry. eauto using M.find_1.
destruct (M.find (elt:=L.t) k y) eqn:heq2; eauto.
forwards*: M.find_2.
forwards*: H0. destruct_ALL. 
forwards*: M.find_1. rewrite heq1 in *; try discriminate.
Qed.

  
Theorem le_refl:
  forall x, 
    le x x.
  unfold le. intros. eexists. eauto using L.le_refl.
Qed.

Theorem le_trans : forall x y z, le x y -> le y z -> le x z.
unfold le. intros x y z h1 h2. intros. 
forwards*: h1; destruct_ALL.
forwards*: h2; destruct_ALL. 
eexists; eauto using L.le_trans.
Qed.

(* Print M. *)

Definition single_join (k : M.key) (v : L.t) (m : M.t L.t)  : M.t L.t :=
  match M.find k m with 
  | None => M.add k v m 
  | Some v' => M.add k (L.join v v') m 
  end.

Lemma find_single_join_neq :
  forall x k v m,
  x <> k ->
  M.find x (single_join k v m) = M.find x m.
  intros. unfold single_join.
  destruct (M.find (elt:=L.t) k m) eqn:heq;
  rewrite MFact.add_neq_o; eauto; rewrite streq; eauto.
Qed.




Definition Ljoin' (l : L.t) (r : option L.t) : L.t :=
  match r with 
  | Some r => L.join l r 
  | None => l 
  end.
Lemma find_single_join_eq :
  forall k v m ,
  M.find k (single_join k v m) = Some (Ljoin' v (M.find k m)).
intros. unfold single_join.
destruct (M.find (elt:=L.t) k m) eqn:heq;
rewrite MFact.add_eq_o; eauto.
Qed.

Theorem Eeqdec:
  forall (x y : E.t),
  {x = y} + {x <> y}.
generalize (E.eq_dec). intros.
rewrite streq in *. eauto.
Qed.

(* Print MProp.map_induction. *)
Lemma single_join_commutative:
  forall a (k0 k' : E.t) (e e' : L.t),
  ~ E.eq k0 k' ->
  single_join k0 e (single_join k' e' a) =
  single_join k' e' (single_join k0 e a).
  rewrite streq.
  intros.
  rewrite <- Equal_as_quotient. intro k.
  destruct (Eeqdec k k0) eqn:heq1;
  destruct (Eeqdec k k') eqn:heq2; subst; eauto; try contradiction.
  + rewrite find_single_join_eq. rewrite find_single_join_neq; eauto. 
  rewrite find_single_join_neq; eauto. rewrite find_single_join_eq; eauto.
  + rewrite find_single_join_neq; eauto. rewrite find_single_join_eq.
    rewrite find_single_join_eq. rewrite find_single_join_neq; eauto.
  + repeat (rewrite find_single_join_neq); eauto.
Qed.



Lemma le_single_join:
  forall m k v,
    le m (single_join k v m).
intros m k v k0 v0 H.
destruct (Eeqdec k k0) eqn:heq1; subst; eauto.
exists (L.join v v0); split ;eauto using L.join_le_right.
eapply M.find_2. rewrite find_single_join_eq. erewrite M.find_1; eauto. cbn in *; eauto.
exists v0. split; eauto using L.le_refl.
eapply M.find_2. rewrite find_single_join_neq; eauto. eapply M.find_1; eauto.
Qed.




Lemma m_add_single_join:
forall k v y1 y2,
 ~ M.In (elt:=L.t) k y1 ->
  MProp.Add k v y1 y2 ->
single_join k v y1 = y2.
intros.
eapply Equal_as_quotient. intro k'.
unfold MProp.Add in *.
rewrite H0.
unfold single_join. destruct (M.find (elt:=L.t) k y1) eqn:h1; eauto. 
rewrite MFact.not_find_in_iff in *. rewrite H in *; try discriminate.
Qed.


Lemma single_join_monotonicity:
  forall x y,
    le x y ->
    forall k v,
    le (single_join k v x) (single_join k v y).
unfold le in *. intros.
(* if k0 in x, then we have one in y *)
destruct (MFact.In_dec x k0). 
rewrite MFact.in_find_iff in *. destruct (M.find (elt:=L.t) k0 x) eqn:h1; subst; eauto; try contradiction. 
destruct (Eeqdec k0 k); subst; eauto.
+ eexists. rewrite MFact.find_mapsto_iff. rewrite find_single_join_eq. split; eauto.
forwards*: M.find_2. forwards*: H. destruct_ALL. rewrite MFact.find_mapsto_iff in H2. rewrite H2. cbn in *.  rewrite MFact.find_mapsto_iff in H0. rewrite find_single_join_eq in H0. injection H0; intros; subst; eauto. rewrite h1; cbn in *. eapply L.join_monoton; eauto.
+  forwards*: M.find_2. forwards*: H. destruct_ALL. rewrite MFact.find_mapsto_iff in H2.
eexists. rewrite MFact.find_mapsto_iff. rewrite find_single_join_neq; eauto. rewrite H2. split; eauto. rewrite MFact.find_mapsto_iff in H0. rewrite find_single_join_neq in H0; eauto. rewrite H0 in h1; injection h1; intros; subst; eauto.
+ generalize n. rewrite MFact.not_find_in_iff . intros. rewrite MFact.find_mapsto_iff in H0. 
destruct (Eeqdec k0 k); subst; eauto.
++ rewrite find_single_join_eq in *. rewrite n0 in *. eexists. rewrite MFact.find_mapsto_iff.  rewrite find_single_join_eq. split; eauto. cbn in *. inversion H0; subst; eauto. unfold Ljoin'. destruct (M.find (elt:=L.t) k y); eauto using L.le_refl, L.join_le_left.

++ rewrite find_single_join_neq in *; eauto. rewrite H0 in *; try discriminate.
Qed. 




(* Definition join_ x :=
  List.fold_right 
  (fun p m => 
    match p with 
    | (k, v) => (single_join k v m)
    end)  (M.empty _) x.

Lemma join_single_join:
  forall k v l,
    join_ ((k, v) :: l) = single_join k v (join_ l).
  cbn in *. unfold join_. eauto.
Qed. *)

(* Print M.fold. *)

Definition join (m1 : t) (m2 : t) : t := 
  M.fold (fun k v t => single_join k v t) m1 m2.

Lemma join_empty:  
  forall (m : M.t L.t) y,
  M.Empty (elt:=L.t) m -> join m y = y.
intros. unfold join. rewrite MProp.fold_Empty; eauto.
Qed.



Lemma join_add:
  forall k v m m' y,
  ~ M.In (elt:=L.t) k m ->
  MProp.Add k v m m' -> join m' y = single_join k v (join m y).
intros. unfold join. rewrite MProp.fold_Add; eauto.
rewrite streq. solve_proper.
intro; intros. eauto using single_join_commutative.
Qed.

Lemma empty_unique:
  forall x,
    M.Empty (elt:=L.t) x ->
    x = (M.empty _ ).
  intros. eapply Equal_as_quotient. intro k. 

  cbn in *.   destruct (M.find (elt:=L.t) k x) eqn:h1; eauto.
  rewrite MProp.elements_Empty in *.
  rewrite MFact.elements_o in *. rewrite H in *. cbn in *. try discriminate.
Qed.



Lemma join_empty2:  
  forall (m : M.t L.t) y,
  M.Empty (elt:=L.t) m -> join y m = y.
intros m y. generalize dependent m. 
induction y using MProp.map_induction; intros; cbn in *. rewrite (join_empty); eauto. 
repeat (rewrite empty_unique); eauto using empty_unique.
erewrite join_add; eauto. rewrite IHy1; eauto.
eapply m_add_single_join; eauto.
Qed.



Lemma  join_le_right:
  forall x y, le y (join x y).
intros x y. generalize dependent x.
eapply  MProp.map_induction; cbn in *; intros; cbn in *; 
[rewrite join_empty | erewrite join_add]; eauto using le_refl.
eapply le_trans;[ | eapply le_single_join]; eauto.
Qed.



Lemma join_le_right_monoton:
  forall x y1 y2,
    le y1 y2 ->
    le (join x y1) (join x y2).
intros x. induction x using MProp.map_induction.
intros ; repeat rewrite join_empty; eauto.
intros. erewrite join_add; eauto. erewrite (join_add _ _ _ x2); eauto.
eapply single_join_monotonicity; eauto.
Qed.


Theorem join_le_left:
  forall x y, le x (join x y).


  intros x y. generalize dependent x. induction y using MProp.map_induction; intros.
  rewrite join_empty2; eauto using le_refl.
  eapply le_trans;[ | eapply join_le_right_monoton]; eauto.
  forwards* : m_add_single_join. rewrite <- H1.
  eapply le_single_join.
Qed.



Theorem InA_streq:
  forall p l,
  InA (M.eq_key_elt (elt:=L.t)) p l <->
  InA eq p l.
unfold M.eq_key_elt. unfold M.Raw.PX.eqke. rewrite streq. 
split. intros h. induction h; subst; destruct_ALL; cbn in *;subst; eauto.
intros h. induction h; subst; destruct_ALL; cbn in *;subst; eauto.
Qed.

Theorem join_monoton:
  forall x y l,
    le x y ->
    le (join l x) (join l y).
intros x y l. generalize dependent x. generalize dependent y.
induction l using MProp.map_induction. 
intros. repeat rewrite join_empty; eauto.
intros. (erewrite join_add; eauto). erewrite (join_add _ _ _ _ _ H H0); eauto.
eapply single_join_monotonicity; eauto.
Qed.

End Map_LATTICE.

Module ident_DEC <: DecidableType.

Definition t := ident.
Definition eq : t -> t -> Prop := fun x y => x = y.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
unfold eq.
repeat decide equality. Qed.

 (* Instance eq_equiv : Equivalence eq. 
 split; cbv delta in *; cbn in *; eauto; intros; subst; eauto.
 Qed.  *)
 Theorem eq_refl : forall x : t, eq x x. unfold eq. auto. Qed.
 Theorem eq_sym : forall x y : t, eq x y -> eq y x. unfold eq. auto. Qed.
 Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z. unfold eq. intros. auto. subst. auto. Qed.

Definition streq : eq = eq. auto. Qed.

End ident_DEC.

Module ident_Map := FMapWeakList.Make(ident_DEC).
Module ident_Map_Fact := WFacts_fun ident_DEC ident_Map.


Family Lang.

FInductive exp : Set := 
  | var : ident -> exp 
  | boolcst : bool -> exp
  (* | error : exp *)
  | strcst : string -> exp
  | concat : exp -> exp -> exp.


FScheme exp_prec PRecT about self__Lang.exp.


Overridable pins {exp} 
Field is_strcst_do : option self__Lang.exp -> (string -> option self__Lang.exp) -> option self__Lang.exp
:= fun e f =>
    match e with 
    | Some (self__Lang.__internal_strcst n) => (f n) 
    | _ => None 
    end.

Closing Fact is_strcst_do_axiom :
  forall n f,
  self__Lang.is_strcst_do (Some (self__Lang.strcst n)) f = (f n) 
by {intros n f; cbn in *; eauto}.

Overridable pins {exp is_strcst_do} 
Field  is_strcst_do_axiom2 :
  forall e f v,
  self__Lang.is_strcst_do e f = Some v ->
  exists s, e = Some (self__Lang.strcst s).
FProof.
intros e f v h; destruct e as [e |]; cbn in *; try discriminate. 
destruct e; try (cbn in *; inversion h; fail); cbn in *; simpl in h. 
eexists; eauto. 
Qed. FEnd is_strcst_do_axiom2. 


  
Closing Fact exp_eq_dec : 
  forall (x y : self__Lang.exp), {x = y} + {x <> y}
by plain transparent { intros x y;
     repeat (decide equality)}.

Field Memory : Type := ident_Map.t self__Lang.exp.
Field update : self__Lang.Memory -> ident -> self__Lang.exp -> self__Lang.Memory :=
  fun orig k v => ident_Map.add k v orig.

Field lookup : self__Lang.Memory -> ident -> option self__Lang.exp :=
  fun mem k => ident_Map.find k mem.


Field lookup_update:
  forall mem k1 k2 v,
    self__Lang.lookup (self__Lang.update mem k1 v) k2 = 
    if (ident_DEC.eq_dec k1 k2) then Some v else self__Lang.lookup mem k2.
FProof. cbn in *. eapply  ident_Map_Fact.add_o. 
Qed. FEnd lookup_update.



Family exp_eval_cases_handler.
Field motive : self__Lang.exp -> Type := fun _ => self__Lang.Memory -> option self__Lang.exp.
Field var : 
  forall i, self__exp_eval_cases_handler.motive (self__Lang.var i) :=
  fun i env => self__Lang.lookup env i.
Field boolcst : 
  forall b, self__exp_eval_cases_handler.motive (self__Lang.boolcst b) :=
  fun b env => Some (self__Lang.boolcst b).
(* 
Field error :
  self__exp_eval_cases_handler.motive self__Lang.error := fun _ => self__Lang.error. *)

Field strcst : 
  forall n, self__exp_eval_cases_handler.motive (self__Lang.strcst n) :=
  fun n env => Some (self__Lang.strcst n).


(* We have a horrible add hahaha *)
Field concat : 
  forall e1 (rec1 : self__exp_eval_cases_handler.motive e1) e2 (rec2 : self__exp_eval_cases_handler.motive e2), self__exp_eval_cases_handler.motive (self__Lang.concat e1 e2) :=
  fun e1 rec1 e2 rec2 env =>
  self__Lang.is_strcst_do 
      (rec1 env) 
      (fun n1 => 
      self__Lang.is_strcst_do 
          (rec2 env) 
          (fun n2 => Some (self__Lang.strcst (n1 ++ n2)))).

FEnd exp_eval_cases_handler  .

FRecursor exp_eval 
  about self__Lang.exp 
  motive self__Lang.exp_eval_cases_handler.motive
  using self__Lang.exp_eval_cases_handler
  by _rect WithRec2D.





MetaData _eval_exp_eval.

Ltac eval_eval_exp :=  
  repeat (frec_eval_onestep self__Lang.exp_eval ; cbn in * ).
FEnd _eval_exp_eval.


Field bexp_eval : self__Lang.Memory -> self__Lang.exp -> option bool :=
  fun env e =>
  let b := (self__Lang.exp_eval e env) in
  match b with 
  | None => None 
  | Some b => 
    match self__Lang.exp_eq_dec b (self__Lang.boolcst true) with
    | left _ => Some true 
    | _ => match self__Lang.exp_eq_dec b (self__Lang.boolcst false) with 
      | left _ => Some false 
      | _ => None
    end 
  end
  end.


FInductive stmt : Set :=
  | assign : ident -> self__Lang.exp -> stmt
  | seq    : stmt  -> stmt  -> stmt
  (* Only allow ident in the condition
      makes things easier *)
  | while  : self__Lang.exp -> stmt -> stmt
  | nop    : stmt
  | ifte   : self__Lang.exp -> stmt -> stmt -> stmt.

  

Closing Fact stmt_eq_dec : 
  forall (x y : self__Lang.stmt), {x = y} + {x <> y}
by plain transparent {intros x y; 
     repeat (decide equality)}.


(* We will just not call it continuation *)

Field stack : Type := list self__Lang.stmt.


(* Program Counter * Stack, but for first order language
    like ours, this is exactly program counter *)
Field PCS   : Type := self__Lang.stmt * self__Lang.stack.




Field PCS_eqdec :
  forall (x y : self__Lang.PCS),
  {x = y} + {~ x = y}.
FProof.
repeat decide equality. 
eapply self__Lang.stmt_eq_dec.
eapply self__Lang.stmt_eq_dec.
Qed. FEnd PCS_eqdec.


MetaData PCS_DEC_mod.

Module PCS_DEC <: DecidableType.

Definition t := self__Lang.PCS.
Definition eq : t -> t -> Prop := fun x y => x = y.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := self__Lang.PCS_eqdec.

 (* Instance eq_equiv : Equivalence eq. 
 split; cbv delta in *; cbn in *; eauto; intros; subst; eauto.
 Qed.  *)
 Theorem eq_refl : forall x : t, eq x x. unfold eq. auto. Qed.
 Theorem eq_sym : forall x y : t, eq x y -> eq y x. unfold eq. auto. Qed.
 Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z. unfold eq. intros. auto. subst. auto. Qed.

 Lemma eq_dec_id:
  forall x, 
    exists y, eq_dec x x = left _ y.
    intros. destruct (eq_dec x x). repeat eexists; eauto.
    destruct (n (eq_refl x)).
Qed.

Definition streq : eq = eq. auto. Qed.


End PCS_DEC.
FEnd PCS_DEC_mod.


Field State : Type := self__Lang.PCS * self__Lang.Memory.

Family eval__cases_handler.
Field motive : self__Lang.stmt -> Type 
  := fun _ => 
    self__Lang.stack -> self__Lang.Memory -> self__Lang.State.

Field assign : 
  forall i e, self__eval__cases_handler.motive (self__Lang.assign i e)
  := fun i e stk mem => 
  match self__Lang.exp_eval e mem with 
  | Some v =>
  (self__Lang.nop, stk, (self__Lang.update mem i v))
  | None => (self__Lang.assign i e, stk, mem)
  end.

Field seq:
  forall s1 (_ : self__eval__cases_handler.motive s1)
         s2 (_ : self__eval__cases_handler.motive s2), 
         self__eval__cases_handler.motive (self__Lang.seq s1 s2)
  := 
  fun s1 _ s2 _ stk mem =>
    (s1, s2 :: stk, mem).

Field while : 
  forall (cond : self__Lang.exp) stm (_ : self__eval__cases_handler.motive stm), 
         self__eval__cases_handler.motive (self__Lang.while cond stm)
  := fun cond sstm _ stk mem =>
  ((self__Lang.ifte cond (self__Lang.seq sstm (self__Lang.while cond sstm)) self__Lang.nop), stk, mem). 


Field ifte:
  forall (cond : self__Lang.exp) stm1 (_ : self__eval__cases_handler.motive stm1)
         stm2 (_ : self__eval__cases_handler.motive stm2), 
         self__eval__cases_handler.motive (self__Lang.ifte cond stm1 stm2)
  := fun cond stm1 _ stm2 _ stack mem =>
    let cond_val := self__Lang.bexp_eval mem cond in
    match cond_val with
    | Some true => (stm1, stack, mem)
    | Some false => (stm2, stack, mem)
    | None => (self__Lang.ifte cond stm1 stm2, stack, mem)
    end.



Field nop:
  self__eval__cases_handler.motive self__Lang.nop
  := fun stk mem => 
    match stk with 
    | [] => (self__Lang.nop, [], mem)
    | h::tail => (h, tail, mem)
    end.

FEnd eval__cases_handler  .

FRecursor eval__
  about self__Lang.stmt
  motive self__Lang.eval__cases_handler.motive
  using self__Lang.eval__cases_handler
  by _rect WithRec2D.



Field eval_ : self__Lang.State -> self__Lang.State :=
  fun st =>
    match st with 
    | ((stm, stack), mem) => self__Lang.eval__ stm stack mem 
    end.

Field eval : nat -> self__Lang.State -> self__Lang.State :=
  fix eval n st :=
  match n with 
  | 0 => st 
  | S n => 
    let st' := self__Lang.eval_ st in 
    eval n st' 
  end.

Field test : self__Lang.exp := self__Lang.var 0.

FEnd Lang.



Family LangwAbs extends Lang. 

Inherit Field eval.


Family AI.


Overridable Field absExp : Type := non_implement.
Overridable Field AEjoin : self__AI.absExp -> self__AI.absExp -> self__AI.absExp := non_implement .
Overridable Field AEle : self__AI.absExp -> self__AI.absExp -> Prop := non_implement.

Family AbsExpData.

Field t : Type := self__AI.absExp.
Field join : self__AbsExpData.t -> self__AbsExpData.t -> self__AbsExpData.t := self__AI.AEjoin.
Field le : self__AbsExpData.t -> self__AbsExpData.t -> Prop := self__AI.AEle.

Overridable Field le_refl : forall x, self__AbsExpData.le x x := non_implement.
Overridable Field le_trans : forall x y z, self__AbsExpData.le x y -> self__AbsExpData.le y z -> self__AbsExpData.le x z := non_implement.
Overridable Field join_le_left :
  forall x y, self__AbsExpData.le x (self__AbsExpData.join x y) := non_implement.
Overridable Field join_le_right :
  forall x y, self__AbsExpData.le y (self__AbsExpData.join x y) := non_implement.

Overridable Field le_antisymm : 
forall x y, self__AbsExpData.le x y -> self__AbsExpData.le y x -> x = y := non_implement.  

Overridable Field join_monoton:
forall x y l,
  self__AbsExpData.le x y ->
  self__AbsExpData.le (join l x) (join l y) := non_implement.

FEnd AbsExpData  .



MetaData _MAP_LATTICES_DECLARE.

Module ABSMemory := Map_LATTICE ident_DEC ident_DEC self__AI.AbsExpData.

Module ABSState := Map_LATTICE self__LangwAbs.PCS_DEC self__LangwAbs.PCS_DEC ABSMemory.

Module PCS_Map := ABSState.M.

Module PCS_Map_Properties := WProperties_fun self__LangwAbs.PCS_DEC PCS_Map.

Module ABSMemoryMap_Fact := WFacts_fun ident_DEC ABSMemory.M.

Module PCS_Map_Fact := WFacts_fun self__LangwAbs.PCS_DEC PCS_Map.


FEnd _MAP_LATTICES_DECLARE  .

Field absMemory : Type := self__AI.ABSMemory.t.

Field aupdate : self__AI.absMemory -> ident -> self__AI.AbsExpData.t  -> self__AI.absMemory :=
  fun orig k v => self__AI.ABSMemory.M.add k v orig.

Field alookup : self__AI.absMemory -> ident -> option self__AI.AbsExpData.t :=
  fun mem k  => self__AI.ABSMemory.M.find k mem.


Field alookup_aupdate : 
    forall mem k1 k2 v,
    self__AI.alookup (self__AI.aupdate mem k1 v) k2 = 
      if (ident_DEC.eq_dec k1 k2) then Some v else self__AI.alookup mem k2.
FProof.
cbn in *. eapply self__AI.ABSMemoryMap_Fact.add_o.
Qed. FEnd alookup_aupdate.

Overridable Field RExp : self__LangwAbs.exp -> self__AI.absExp -> Prop := non_implement.

Overridable Field RExp_monoton : 
  forall x a b,
    self__AI.RExp x a ->
    self__AI.AbsExpData.le a b ->
    self__AI.RExp x b := non_implement.

Field RMemory : self__LangwAbs.Memory -> self__AI.absMemory -> Prop := 
  fun mem amem =>
  forall k v, 
    self__LangwAbs.lookup mem k = Some v ->
    exists a, self__AI.alookup amem k = Some a /\ self__AI.RExp v a. 

Overridable 
Field exp_analyze  : self__LangwAbs.exp -> self__AI.absMemory ->  self__AI.absExp
  := non_implement.

Overridable
Field exp_analyze_sound : 
  forall e mem amem v,
    self__AI.RMemory mem amem ->
    self__LangwAbs.exp_eval e mem = Some v ->
    self__AI.RExp v (self__AI.exp_analyze e amem) := non_implement.

Field absState : Type := self__AI.ABSState.t.

Field RState : self__LangwAbs.State -> self__AI.absState -> Prop :=
  fun st ast =>
  let (pc, mem) := st in 
  match self__AI.PCS_Map.find pc ast with 
  | None => False 
  | Some amem => self__AI.RMemory mem amem 
  end.


Field Rupdate :
  forall x y mem amem i,
  self__AI.RMemory mem amem ->
  self__AI.RExp x y ->
  self__AI.RMemory (self__LangwAbs.update mem i x) (self__AI.aupdate amem i y).
FProof.
unfold self__AI.RMemory.
intros x y mem amem i H H1 k v H2. 
rewrite self__LangwAbs.lookup_update in *.
rewrite self__AI.alookup_aupdate in *.
destruct (ident_DEC.eq_dec i k); subst; eauto.
inversion H2; subst; eauto; eexists; eauto.
Qed. FEnd Rupdate.

Field injSt : self__LangwAbs.PCS -> self__AI.absMemory -> self__AI.absState :=
  fun pcs amem =>
  self__AI.PCS_Map.add pcs amem (self__AI.PCS_Map.empty _). 



Field Relate_inj_st:
    forall x y z,
    self__AI.RMemory y z ->
    self__AI.RState (x, y) (self__AI.injSt x z).
FProof. cbn in *. intros.
destruct (self__LangwAbs.PCS_DEC.eq_dec x x); subst; eauto; try contradiction.
Qed. FEnd Relate_inj_st.

Field joinSt : self__AI.absState -> self__AI.absState -> self__AI.absState :=
  self__AI.ABSState.join.

Family analyze__cases_handler.
Field motive : self__LangwAbs.stmt -> Type 
  := fun _ => 
    self__LangwAbs.stack -> self__AI.absMemory -> self__AI.absState.

Field assign : 
  forall i e, self__analyze__cases_handler.motive (self__LangwAbs.assign i e)
  := fun i e stk amem => 
  let v := self__AI.exp_analyze e amem in
  self__AI.joinSt
  (self__AI.injSt (self__LangwAbs.nop, stk) (self__AI.aupdate amem i v))
  (self__AI.injSt (self__LangwAbs.assign i e, stk) amem).

Field seq:
  forall s1 (_ : self__analyze__cases_handler.motive s1)
         s2 (_ : self__analyze__cases_handler.motive s2), 
         self__analyze__cases_handler.motive (self__LangwAbs.seq s1 s2)
  := 
  fun s1 _ s2 _ stk mem =>
    self__AI.injSt (s1, s2 :: stk) (mem).

Field while : 
  forall (cond : self__LangwAbs.exp) stm (_ : self__analyze__cases_handler.motive stm), 
         self__analyze__cases_handler.motive (self__LangwAbs.while cond stm)
  := fun cond sstm _ stk mem =>
  self__AI.injSt
  ((self__LangwAbs.ifte cond (self__LangwAbs.seq sstm (self__LangwAbs.while cond sstm)) self__LangwAbs.nop), stk) mem. 


Field ifte:
  forall (cond : self__LangwAbs.exp) stm1 (_ : self__analyze__cases_handler.motive stm1)
         stm2 (_ : self__analyze__cases_handler.motive stm2), 
         self__analyze__cases_handler.motive (self__LangwAbs.ifte cond stm1 stm2)
  := fun cond stm1 _ stm2 _ stack mem =>
  self__AI.joinSt
   (self__AI.joinSt (self__AI.injSt (stm1, stack) (mem))
                     (self__AI.injSt (stm2, stack) mem))
   (self__AI.injSt (self__LangwAbs.ifte cond stm1 stm2, stack) mem).



Field nop:
  self__analyze__cases_handler.motive self__LangwAbs.nop
  := fun stk mem => 
    match stk with 
    | [] => self__AI.injSt (self__LangwAbs.nop, []) mem
    | h::tail => self__AI.injSt (h, tail) mem
    end.

FEnd analyze__cases_handler  .


FRecursor analyze___
  about self__LangwAbs.stmt
  motive self__AI.analyze__cases_handler.motive
  using self__AI.analyze__cases_handler
  by _rect WithRec2D.






Field RMemory_monoton:
  forall m x y,
    self__AI.RMemory m x ->
    self__AI.ABSMemory.le x y ->
    self__AI.RMemory m y.
FProof.
unfold self__AI.RMemory. unfold self__AI.ABSMemory.le.
intros.
forwards*: H; destruct_ALL.
unfold self__AI.alookup in *.
forwards*: self__AI.ABSMemory.M.find_2.
forwards*: H0; destruct_ALL. 
clear H4. forwards*: self__AI.ABSMemory.M.find_1.
eexists; split; eauto.
eapply self__AI.RExp_monoton; eauto.
Qed. FEnd RMemory_monoton. 


Field le_ast : self__AI.absState -> self__AI.absState -> Prop := self__AI.ABSState.le.



Field RState_monoton:
  forall x y z,
  self__AI.RState x y ->
  self__AI.le_ast y z ->
  self__AI.RState x z.
FProof.
unfold self__AI.RState. unfold self__AI.le_ast. unfold self__AI.ABSState.le. intros.
destruct x.
destruct (self__AI.PCS_Map.find (elt:=self__AI.ABSMemory.t) p y) eqn:h1; try contradiction.
forwards*: self__AI.ABSState.M.find_2. forwards*: H0. destruct_ALL.
forwards*: self__AI.ABSState.M.find_1. rewrite H4.
eapply self__AI.RMemory_monoton; eauto.
Qed. FEnd RState_monoton.




Field join_le_ast_left:
  forall x y z,
    self__AI.le_ast x y ->
    self__AI.le_ast x (self__AI.joinSt y z).
FProof.
intros. eapply self__AI.ABSState.le_trans;[ idtac | eapply self__AI.ABSState.join_le_left]; eauto.
Qed. FEnd join_le_ast_left.



Field join_le_ast_right:
  forall x y z,
    self__AI.le_ast x z ->
    self__AI.le_ast x (self__AI.joinSt y z).
FProof.
intros. eapply self__AI.ABSState.le_trans;[ idtac | eapply self__AI.ABSState.join_le_right]; eauto.
Qed. FEnd join_le_ast_right.


MetaData __clear_PCS_DEC_eq_dec.

Ltac clear_PCS_DEC_eq_dec :=
match goal with 
| [|- context G [self__LangwAbs.PCS_DEC.eq_dec ?x ?x]] => destruct (self__LangwAbs.PCS_DEC.eq_dec x x);subst; eauto; try contradiction
end.
FEnd __clear_PCS_DEC_eq_dec.

Field analyze__ : self__LangwAbs.PCS * self__AI.absMemory -> self__AI.absState :=
  fun ast =>
    match ast with 
    | ((stm, stk), amem) => self__AI.analyze___ stm stk amem 
    end.

FInduction sync_eval__analyze__
  about self__LangwAbs.stmt 
  motive (
    fun stm =>
    forall stk mem amem,
    self__AI.RMemory mem amem -> 
    self__AI.RState (self__LangwAbs.eval_ (stm, stk, mem)) (self__AI.analyze__ ((stm, stk), amem))
  ).
 FProof. 
+  intros. unfold self__LangwAbs.eval_. unfold self__AI.analyze__. 
  frec_eval_onestep self__AI.analyze___.
  frec_eval_onestep self__LangwAbs.eval__. 
  unfold self__AI.analyze__cases_handler.assign.
  unfold self__LangwAbs.eval__cases_handler.assign.
  destruct (self__LangwAbs.exp_eval e mem) eqn:h1.
  ++ eapply self__AI.RState_monoton. eapply self__AI.Relate_inj_st.
  eapply self__AI.Rupdate; eauto. eapply self__AI.exp_analyze_sound; eauto. eapply self__AI.join_le_ast_left; eapply self__AI.ABSState.le_refl.
  ++ eapply self__AI.RState_monoton. eapply self__AI.Relate_inj_st; eauto.  eapply self__AI.join_le_ast_right; eapply self__AI.ABSState.le_refl. 
+ intros. unfold self__LangwAbs.eval_. unfold self__AI.analyze__. frec_eval self__AI.analyze___; frec_eval self__LangwAbs.eval__. self__AI.clear_PCS_DEC_eq_dec.
+ intros. unfold self__LangwAbs.eval_. unfold self__AI.analyze__. frec_eval self__AI.analyze___; frec_eval self__LangwAbs.eval__. self__AI.clear_PCS_DEC_eq_dec.
+ intros. unfold self__LangwAbs.eval_. unfold self__AI.analyze__. frec_eval self__AI.analyze___; frec_eval self__LangwAbs.eval__. destruct stk; eauto using self__AI.Relate_inj_st.
+ intros. unfold self__LangwAbs.eval_. unfold self__AI.analyze__. frec_eval self__AI.analyze___; frec_eval self__LangwAbs.eval__.  unfold self__LangwAbs.eval__cases_handler.ifte. unfold self__AI.analyze__cases_handler.ifte.
destruct (self__LangwAbs.bexp_eval mem e). destruct b;
eapply self__AI.RState_monoton; eauto using self__AI.Relate_inj_st.
++ eapply self__AI.join_le_ast_left. eapply self__AI.join_le_ast_left. eapply self__AI.ABSState.le_refl.
++  eapply self__AI.join_le_ast_left. eapply self__AI.join_le_ast_right. eapply self__AI.ABSState.le_refl.
++ eapply self__AI.RState_monoton; eauto using self__AI.Relate_inj_st. eapply self__AI.join_le_ast_right. eapply self__AI.ABSState.le_refl.
Qed. FEnd sync_eval__analyze__  .



Field analyze_ : self__AI.absState -> self__AI.absState :=
  fun ast => 
  List.fold_right 
  (fun p ast => 
  (self__AI.joinSt ast (self__AI.analyze__ p))
    )  (self__AI.PCS_Map.empty _) (self__AI.PCS_Map.elements ast).


Field point_wise_analyze_:
    forall x y,
  InA eq x y ->
  self__AI.le_ast (self__AI.analyze__ x)   
  (fold_right
  (fun p0 (ast0 : self__AI.absState) =>
   self__AI.joinSt ast0 (self__AI.analyze__ p0)) (self__AI.PCS_Map.empty _)
  y).
FProof.
intros x y h.
induction h; subst; eauto.
destruct y; subst; eauto. 
cbn. eapply self__AI.join_le_ast_right. eapply self__AI.ABSState.le_refl.
cbn in *. eauto using self__AI.join_le_ast_left, self__AI.join_le_ast_right.
Qed. FEnd point_wise_analyze_.



Field sync_eval_analyze_ :
  forall st ast,
    self__AI.RState st ast ->
    self__AI.RState (self__LangwAbs.eval_ st) (self__AI.analyze_ ast).
FProof. 
destruct st. intros ast h. cbn in h. 
destruct  (self__AI.PCS_Map.find (elt:=self__AI.ABSMemory.t) p ast ) eqn:h1; try contradiction. unfold self__LangwAbs.eval_. destruct p. 
(* unfold analyze_. *)
eapply self__AI.RState_monoton. eapply self__AI.sync_eval__analyze__; eauto.
unfold self__AI.analyze_.  
rewrite <- self__AI.PCS_Map_Fact.find_mapsto_iff in h1.
rewrite self__AI.PCS_Map_Fact.elements_mapsto_iff in h1.
eapply self__AI.point_wise_analyze_; eauto. rewrite self__AI.ABSState.InA_streq in h1. eauto.
Qed. FEnd sync_eval_analyze_.

Field analyze : nat -> self__AI.absState -> self__AI.absState :=
  fix f fuel st :=
    match fuel with 
    | 0 => st 
    | S fuel => 
      let st' := self__AI.analyze_ st in 
      f fuel st' 
    end.



Field analyze_partial_correct:
    forall fuel st ast,
    self__AI.RState st ast ->
    self__AI.RState (self__LangwAbs.eval fuel st) (self__AI.analyze fuel ast).
FProof.
induction fuel; cbn in *; eauto using self__AI.sync_eval_analyze_.
Qed. FEnd analyze_partial_correct.

FEnd AI.
FEnd LangwAbs.


Family LangTyping extends LangwAbs.

Inherit Until Field AI. 
Family AI. 
Inherit Until Field absExp.

FInductive type_aexp : Set :=
| ty_bool : type_aexp
| ty_str : type_aexp
| ty_error : type_aexp.

Closing Fact type_aexp_eq_dec :
  forall (x y : self__AI.type_aexp), {x = y} + {x <> y}
  by plain transparent {
    intros x y;
     repeat (decide equality)
  }.


MetaData type_aexp_Module.

(* We still need to use Decidable in Coq *)
Module type_aexp_Decidable. 
(* <: DecidableType *)
Definition t :=self__AI.type_aexp.
Definition eq : t -> t -> Prop := fun x y => x = y.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}
 := self__AI.type_aexp_eq_dec.


Instance eq_equiv : Equivalence eq. 
split; cbv delta in *; cbn in *; eauto; intros; subst; eauto. 
Qed.

Theorem eq_refl : forall x : t, eq x x. unfold eq. auto. Qed.
Theorem eq_sym : forall x y : t, eq x y -> eq y x. unfold eq. auto. Qed.
Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z. unfold eq. intros. auto. subst. auto. Qed.

Definition streq : eq = eq. auto. Qed.

End type_aexp_Decidable.



Module Set_of_type_aexp := FSetWeakList.Make(type_aexp_Decidable).

Module Set_of_type_aexp_prop := FSetProperties.WProperties_fun (type_aexp_Decidable) (Set_of_type_aexp).

Module Set_of_type_aexp_fact := FSetFacts.WFacts_fun (type_aexp_Decidable) (Set_of_type_aexp).


(* Again we take the quotient *)
Axiom Equal_as_quotient:
  forall x y,
  Set_of_type_aexp.Equal x y <-> x = y.

FEnd type_aexp_Module.


Override Field absExp : Type := self__AI.Set_of_type_aexp.t.

Override pins {absExp}
Field AEjoin : self__AI.absExp -> self__AI.absExp -> self__AI.absExp :=
  fun e1 e2 => 
    self__AI.Set_of_type_aexp.union e1 e2.

Override pins {absExp}
Field AEle : self__AI.absExp -> self__AI.absExp -> Prop :=
fun s1 s2 =>
  self__AI.Set_of_type_aexp.Subset s1 s2.


Inherit Until Field AbsExpData.
Family AbsExpData.

Inherit Until Field le_refl.
Override pins {absExp AEle}
Field 
le_refl : forall x, self__AbsExpData.le x x.
FProof.
unfold self__AbsExpData.le. unfold self__AI.AEle.  
unfold self__AI.Set_of_type_aexp.Subset. eauto.
Qed. FEnd le_refl.


Override pins {absExp AEle}
Field le_trans : 
forall x y z, self__AbsExpData.le x y -> self__AbsExpData.le y z -> self__AbsExpData.le x z.
FProof. unfold self__AbsExpData.le.  unfold self__AI.AEle.  
unfold self__AI.Set_of_type_aexp.Subset. intros. auto.
Qed. FEnd le_trans.

Override pins {absExp AEle AEjoin}
Field 
join_le_left :
  forall x y, self__AbsExpData.le x (self__AbsExpData.join x y).
FProof.
unfold self__AbsExpData.le.  unfold self__AI.AEle.  
unfold self__AI.Set_of_type_aexp.Subset.
unfold self__AbsExpData.join. unfold self__AI.AEjoin.  intros.  eapply self__AI.Set_of_type_aexp.union_2. eauto.
Qed. FEnd join_le_left. 

Override pins {absExp AEle AEjoin}
Field join_le_right :
  forall x y, self__AbsExpData.le y (self__AbsExpData.join x y).
FProof.
unfold self__AbsExpData.le.  unfold self__AI.AEle.  
unfold self__AI.Set_of_type_aexp.Subset.
unfold self__AbsExpData.join. unfold self__AI.AEjoin.  intros.  eapply self__AI.Set_of_type_aexp.union_3. eauto.
Qed. FEnd join_le_right.


Override pins {absExp AEle AEjoin}
Field le_antisymm : forall x y, self__AbsExpData.le x y -> self__AbsExpData.le y x -> x = y.
FProof.
unfold self__AbsExpData.le.
unfold self__AI.AEle. intros. forwards*: self__AI.Set_of_type_aexp_prop.subset_antisym. symmetry. eapply self__AI.Equal_as_quotient; eauto.
Qed. FEnd le_antisymm.

Override pins {absExp AEle AEjoin}
Field join_monoton :forall x y l,
  self__AbsExpData.le x y ->
  self__AbsExpData.le (self__AbsExpData.join l x) (self__AbsExpData.join l y).
FProof.
unfold self__AbsExpData.le.
unfold self__AI.AEle.
unfold self__AbsExpData.join.
intros. unfold self__AI.AEjoin. 
eapply self__AI.Set_of_type_aexp_prop.union_subset_3;
eauto using self__AI.Set_of_type_aexp_prop.union_subset_1.
eapply self__AI.Set_of_type_aexp_prop.subset_trans; eauto using self__AI.Set_of_type_aexp_prop.union_subset_5, self__AI.Set_of_type_aexp_prop.union_subset_2.
Qed. FEnd join_monoton.


FEnd AbsExpData.

Inherit Until Field RExp.

Override pins {absExp}
Field RExp : self__LangTyping.exp -> self__AI.absExp -> Prop
  := fun e ae =>
    (forall b, e = self__LangTyping.boolcst b -> self__AI.Set_of_type_aexp.In self__AI.ty_bool ae)
    /\ (forall s, e = self__LangTyping.strcst s -> self__AI.Set_of_type_aexp.In self__AI.ty_str ae).

Override pins {absExp RExp AEle}
Field RExp_monoton : forall x a b,
  self__AI.RExp x a ->
  self__AI.AbsExpData.le a b ->
  self__AI.RExp x b.
FProof. 
unfold self__AI.RExp. unfold self__AI.AbsExpData.le.
unfold self__AI.AEle. intros; destruct_ALL.
split; intros; subst; eauto.
Qed. FEnd RExp_monoton. 

Inherit Until Field exp_analyze.


Family exp_analyze_handler.

Field motive : self__LangTyping.exp -> Type := 
  fun e => 
    forall (amem : self__AI.absMemory),  
      {ae : self__AI.absExp | 
        forall mem v,
          self__AI.RMemory mem amem ->
          self__LangTyping.exp_eval e mem = Some v ->
          self__AI.RExp v ae
      }. 

Overridable pins {absExp RExp}
Field var : 
  forall (i : ident), self__exp_analyze_handler.motive (self__LangTyping.var i). 
FProof.
unfold self__exp_analyze_handler.motive.
intros.
destruct (self__AI.alookup amem i) eqn:h1. exists t.
frec_eval self__LangTyping.exp_eval. unfold self__LangTyping.exp_eval_cases_handler.var. intros. unfold self__AI.RMemory in *.
forwards*: H; destruct_ALL. rewrite h1 in H1. inversion H1; subst; eauto.
exists (self__AI.Set_of_type_aexp.singleton (self__AI.ty_error)).
frec_eval self__LangTyping.exp_eval. unfold self__LangTyping.exp_eval_cases_handler.var. intros. unfold self__AI.RMemory in *.
forwards*: H; destruct_ALL. rewrite h1 in H1; discriminate. 
Qed. FEnd var.

Overridable pins {absExp RExp}
Field boolcst :
  forall (b : bool), self__exp_analyze_handler.motive (self__LangTyping.boolcst b). 
FProof.
intros x mem. exists (self__AI.Set_of_type_aexp.singleton (self__AI.ty_bool)). unfold self__AI.RMemory. frec_eval self__LangTyping.exp_eval. unfold self__LangTyping.exp_eval_cases_handler.boolcst. unfold self__AI.RExp.  intros. inversion H0; subst; eauto. split; intros; eauto; try discriminate.
eapply self__AI.Set_of_type_aexp.singleton_2. eauto.
prec_discriminate self__LangTyping.exp_prec H1.
Qed. FEnd boolcst.


Overridable pins {absExp RExp}
Field strcst :
  forall n : string, self__exp_analyze_handler.motive (self__LangTyping.strcst n).
FProof. 
intros n mem; intros.
exists (self__AI.Set_of_type_aexp.singleton (self__AI.ty_str)). unfold self__AI.RMemory. frec_eval self__LangTyping.exp_eval. unfold self__LangTyping.exp_eval_cases_handler.strcst. unfold self__AI.RExp.  intros. inversion H0; subst; eauto. split; intros; eauto; try discriminate.
prec_discriminate self__LangTyping.exp_prec H1.
eapply self__AI.Set_of_type_aexp.singleton_2. eauto.
Qed. FEnd strcst.

Overridable pins {absExp RExp}
Field concat :
forall (e1 : self__LangTyping.exp) (rec1 : self__exp_analyze_handler.motive e1) 
       (e2 : self__LangTyping.exp) (rec2 : self__exp_analyze_handler.motive e2), self__exp_analyze_handler.motive (self__LangTyping.concat e1 e2).
FProof. 
intros. intros mem; intros.
destruct (rec1 mem) as [ae1 h1].
destruct (rec2 mem) as [ae2 h2].
exists (
  let strset := self__AI.Set_of_type_aexp.singleton (self__AI.ty_str) in
  let ifstr :=
    if andb (self__AI.Set_of_type_aexp.equal ae1 strset) 
            (self__AI.Set_of_type_aexp.equal ae2 strset)
    then strset
    else self__AI.Set_of_type_aexp.union (self__AI.Set_of_type_aexp.singleton (self__AI.ty_error)) strset in 
  ifstr
). 
unfold self__AI.RMemory in *. frec_eval self__LangTyping.exp_eval. unfold self__LangTyping.exp_eval_cases_handler.concat. unfold self__AI.RExp in *. intros.
forwards*: self__LangTyping.is_strcst_do_axiom2; destruct_ALL.
rewrite H1 in *. rewrite self__LangTyping.is_strcst_do_axiom in *.
forwards*: self__LangTyping.is_strcst_do_axiom2; destruct_ALL.
rewrite H2 in *. rewrite self__LangTyping.is_strcst_do_axiom in *.

split; intros ;subst; eauto.
inversion H0. prec_discriminate self__LangTyping.exp_prec H4.
destruct (
self__AI.Set_of_type_aexp.equal ae1
  (self__AI.Set_of_type_aexp.singleton self__AI.ty_str) &&
self__AI.Set_of_type_aexp.equal ae2
  (self__AI.Set_of_type_aexp.singleton self__AI.ty_str));
eauto using self__AI.Set_of_type_aexp.singleton_2, self__AI.Set_of_type_aexp.union_3.
Qed. FEnd concat. 


FEnd exp_analyze_handler  .


FRecursor exp_analyze_
  about self__LangTyping.exp
  motive self__AI.exp_analyze_handler.motive
  using self__AI.exp_analyze_handler
  by _rect.



Override Field exp_analyze : 
self__LangTyping.exp -> self__AI.absMemory ->  self__AI.absExp :=
  fun e amem => proj1_sig (self__AI.exp_analyze_ e amem).

Inherit Until Field exp_analyze_sound.

Override pins {exp_analyze}
Field exp_analyze_sound : forall e mem amem v,
  self__AI.RMemory mem amem ->
  self__LangTyping.exp_eval e mem = Some v ->
  self__AI.RExp v (self__AI.exp_analyze e amem).
FProof. unfold self__AI.exp_analyze. intros.
destruct (self__AI.exp_analyze_ e amem). cbn in *. eauto.
Qed. FEnd exp_analyze_sound.

FEnd AI.

FEnd LangTyping.


(* only check the final statement *)
Definition analyze_end (fuel : nat) (c : LangTyping.stmt) (i : ident) : option LangTyping.AI.absExp :=
  let initialst := LangTyping.AI.injSt (c, []) (LangTyping.AI.ABSMemory.M.empty _) in 
  let result := LangTyping.AI.analyze fuel initialst in
 
  match LangTyping.AI.ABSState.M.find (LangTyping.nop, []) result with 
  | None => None 
  | Some mem => LangTyping.AI.ABSMemory.M.find i mem 
  end.

End Analysis_showcase.


Module LangTypingTesting.
Import Analysis_showcase.
Import LangTyping.



Definition testcase3 := fun (_ : unit) => 
    (analyze_end 5 
      (ifte (boolcst true)
        (assign 1 (boolcst true))
        (assign 1 (strcst "2"))
      )
      1).

Definition testcase4 := fun (_ : unit) => 
    (analyze_end 10 
    (seq
      nop
      (while (boolcst true)
        (assign 1 (concat (var 1) (strcst "1")))
      ))
      1).

Definition testcase5 := fun (_ : unit) => 
    (analyze_end 5 
      (assign 1 (strcst "1")) 
      1).

Definition testcase6 := fun (_ : unit) => 
    (analyze_end 5 
      (seq (assign 1 (strcst "1"))
           (assign 1 (concat (var 1) (strcst "2")))
          ) 
      1).


Definition testcase7 := fun (_ : unit) => 
    (analyze_end 5 
      (ifte (boolcst true)
        (assign 1 (strcst "1"))
        (assign 1 (strcst "2"))
      )
      1).


Definition testcase8 := fun (_ : unit) => 
    (analyze_end 10 
    (seq
      (assign 1 (strcst "1"))
      (while (boolcst true)
        (assign 1 (concat (var 1) (strcst "1")))
      ))
      1).



End LangTypingTesting.


Import LangTypingTesting.
Require Import Coq.extraction.ExtrOcamlNativeString.
Extract Inductive nat => int [ "0" "succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extraction "./testoutput/test3.ml"  
testcase3 testcase4
testcase5 testcase6 testcase7 testcase8.

Check "This proof script ends here".

Print Analysis_showcase.LangTyping.