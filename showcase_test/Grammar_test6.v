Require Import Fampoly.Loader.
Require Import Fampoly.LibTactics.
Require Import Coq.Lists.List.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Structures.DecidableTypeEx.
Require Import Equalities Orders.
Require Import MSets.
Require Import Strings.Ascii.

Require Import String.

Require Import Coq.micromega.Lia.
Require Import Coq.Init.Datatypes.

Import ListNotations.
Import Notations.

Module CFG_Example.

(* Strong Induction for nat *)
Theorem strong_ind:
  forall n,
    forall (P : nat -> Type),
    (P 0) ->
    (forall n, (forall m, m < n -> P m) -> P n) ->
    P n.
  intros.
  eapply (nat_rect (fun i => forall n, n <= i -> P n)).
  intros. assert (n0 = 0); eauto; try lia; subst ;eauto.
  intros. eapply X0; eauto. intros. eapply X1; eauto. lia.
  
  eapply le_n.  
Defined.


(* First are general facility for Parser *)

Theorem cut:
  forall {A : Type} {B : Type},
    A -> (A -> B) -> B.
  intros. eauto. Defined.

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

Inductive FAIL : Type := F : FAIL.


Notation len := List.length.

Definition strs := list string.


Definition StrsP := strs -> Type.

(* Guarded Decidable *)
Definition GDecidable n (p : StrsP) := forall e, len e < n -> (p e) + (p e -> False). 

Lemma inj_app:
  forall {T : Type} {a b c d : list T},
    len a = len b ->
    a ++ c = b ++ d ->
    a = b.
intros T a. induction a; intros; eauto; cbn in *.
destruct b; cbn in *; eauto; try lia; eauto.
destruct b; cbn in *; eauto; try lia. inversion H; eauto.
inversion H0; eauto. erewrite IHa; eauto.
Defined. 

Lemma cut_list:
  forall k,
    forall s : strs,
    k <= len s ->
    {s1 & {s2 & (s = s1 ++ s2) /\ (len s1 = k) }}.
induction k.
intros. exists ([] : list string); exists s; repeat split; cbn in *; eauto.
intros. assert (k <= len s) as H0; eauto; try lia.
destruct (IHk s H0); destruct_ALL; subst; cbn in *; repeat rewrite app_length in *; eauto. 
destruct x0. cbn in *; eauto; try lia.
exists (x ++ [s]); exists (x0); cbn in *; repeat split; repeat rewrite app_length in *; cbn in *; eauto; eauto; try lia. 
rewrite <- app_assoc. cbn in *; auto.
Defined.

Theorem dec_comp_helper:
forall {k} {P1 P2 : StrsP},
forall {n},
GDecidable n P1 -> GDecidable n P2 ->
GDecidable (S n) (fun e => {e1 & {e2 & (P1 e1) * (P2 e2) * ((len e1) < (len e)) * ((len e2) < (len e)) * (e = e1 ++ e2) * (len e1 = k)}}).
unfold GDecidable. intros.
destruct (Compare_dec.le_lt_dec (len e) k).
right. intros. destruct_ALL. repeat rewrite app_length in *. eauto; try lia.
assert (k <= len e) as H0; eauto; try lia.
destruct (cut_list k e H0); destruct_ALL; repeat rewrite app_length in *.
assert (len x < n); eauto; try lia.
  destruct (Peano_dec.eq_nat_dec (len x) 0).
  right; intros; destruct_ALL; eauto; try lia. symmetry in e0. forwards*: (inj_app e0 e1); subst; eauto. 
  forwards*:app_inv_head; subst; eauto; try lia. 
assert (len x0 < n); eauto; try lia.

destruct (X x H1); destruct (X0 x0 H2); eauto.
left; repeat eexists; eauto; eauto; try lia.
right; intros; destruct_ALL. symmetry in e. forwards*: (inj_app e e0); subst; eauto. forwards*: app_inv_head; subst; eauto.

right; intros; destruct_ALL. symmetry in e. forwards*: (inj_app e e0); subst; eauto. 

right; intros; destruct_ALL. symmetry in e. forwards*: (inj_app e e0); subst; eauto.
Defined. 

(* Recursive Extraction dec_comp_helper. *)


Theorem dec_comp_helper2:
forall {k} {P1 P2 : StrsP},
forall {n},
GDecidable n P1 -> GDecidable n P2 ->
GDecidable (S n) (fun e => {e1 & {e2 & (P1 e1) * (P2 e2) * ((len e1) < (len e)) * ((len e2) < (len e)) * (e = e1 ++ e2) * (len e1 <= k)}}).
intros k.
induction k.
intros.
unfold GDecidable in *. intros. right; intros; destruct_ALL.
repeat rewrite app_length in *; eauto. eauto; try lia.

unfold GDecidable in *.
intros.
destruct (IHk _ _ _ X X0 e H).
left; destruct_ALL; repeat eexists; eauto.
eapply (cut (dec_comp_helper (k := S k) (n := n) X X0)). unfold GDecidable.
intros. destruct (X1 e H); eauto. left; destruct_ALL; repeat eexists; eauto. lia.
right. intros. destruct_ALL; eauto.
repeat rewrite app_length in *.
destruct (Peano_dec.eq_nat_dec (len x) (S k)). eapply f0; eauto.
repeat rewrite app_length in *;
repeat eexists; eauto.
assert (len x <= k); eauto; try lia.
eapply f; eauto. repeat eexists; repeat split; eauto.
Defined.

(* Recursive Extraction dec_comp_helper2. *)


Theorem dec_comp:
forall {P1 P2 : StrsP},
forall {n},
GDecidable n P1 -> GDecidable n P2 ->
GDecidable (S n) (fun e => {e1 & {e2 & (P1 e1) * (P2 e2) * ((len e1) < (len e)) * ((len e2) < (len e)) * (e = e1 ++ e2)}}).
intros.
eapply (cut (dec_comp_helper2 (k := (S n)) X X0)); intros.
unfold GDecidable in *.
intros. destruct (X1 _ H); destruct_ALL.
right; intros; destruct_ALL; repeat rewrite app_length in *; eauto.
eapply f. repeat eexists; eauto. eauto; try lia. 
Defined.

(* Recursive Extraction dec_comp. *)




Lemma dec_comp2:
  forall {P1 : StrsP} {P2 : StrsP},
  forall s,
    GDecidable (len s) P1 ->
    GDecidable (len s) P2 ->
    {s1 & {s2 & (P1 s1)  * (P2 s2) * ((len s1) < (len s)) * ((len s2) < (len s)) * (s = s1 ++ s2)}} +
    ({s1 & {s2 & (P1 s1) * (P2 s2) * ((len s1) < (len s)) * ((len s2) < (len s)) * (s = s1 ++ s2)}} -> False).
  intros P1 P2. intros. subst. eapply cut; intros; unfold GDecidable in *.
  eapply (dec_comp (P1 := P1) (P2 := P2)); eauto. unfold GDecidable in *. eauto.
Defined. 

(* Recursive Extraction dec_comp2. *)


Lemma GDecidable_strong:
  forall {n} {P},
    GDecidable (S n) P ->
    GDecidable n P.
  unfold GDecidable. intros. eauto.
Defined.

Lemma dec_gdec:
  forall {P : StrsP},
    (forall s, (P s) + (P s -> False)) ->
    forall {n}, GDecidable n P. 
unfold GDecidable. intros. eauto.
Defined.

Theorem dec_comp_:
forall {P1 P2 : StrsP},
forall {n},
GDecidable n P1 -> GDecidable n P2 ->
GDecidable n (fun e => {e1 & {e2 & P1 e1 * P2 e2 * ((len e1) < (len e)) * ((len e2) < (len e)) * (e = e1 ++ e2)}}).
intros. eapply GDecidable_strong. eapply dec_comp; eauto.
Defined.

(* Apparently we can make the following generalized
    into a list
    but not really necessary *)

Theorem dec_comp3:
  forall {P1 P2 P3 : StrsP},
  forall e,
    GDecidable (len e) P1 -> GDecidable (len e) P2 -> GDecidable (len e) P3 ->
    ({e1 & {e2 & {e3 & ((P1 e1) * P2 e2 * P3 e3) * (e = e1 ++ e2 ++ e3)* (len e1 < len e)* (len e2 < len e)* (len e3 < len e) * (0 < len e1) * (0 < len e2) * (0 < len e3) }}} + ({e1 & {e2 & {e3 & ((P1 e1) * P2 e2 * P3 e3) * (e = e1 ++ e2 ++ e3)* (len e1 < len e)* (len e2 < len e)* (len e3 < len e) * (0 < len e1) * (0 < len e2) * (0 < len e3) }}} -> False)).
  intros P1 P2 P3. intros.
  eapply cut. eapply (dec_comp2 e X (dec_comp_  X0 X1)); cbn in *; intros.
  intros. destruct_ALL; repeat rewrite app_length in *.

  left. exists x; exists x1; exists x2; repeat split; eauto; eauto; try lia.
  right; intros; cbn in *; destruct_ALL; eauto. eapply f; eauto.
  
  exists x; exists (x0 ++ x1). repeat split; eauto; repeat rewrite app_length in *. exists x0; exists x1. repeat split; eauto; eauto; try lia. lia.
Defined. 

Theorem dec_comp4:
  forall {P1 P2 P3 P4 : StrsP},
  forall e,
    GDecidable (len e) P1 -> GDecidable (len e) P2 -> GDecidable (len e) P3 -> GDecidable (len e) P4 ->
    {e1 & {e2 & {e3 & { e4 & ((P1 e1) * P2 e2 * P3 e3 * P4 e4) * (e = e1 ++ e2 ++ e3 ++ e4)* (len e1 < len e)* (len e2 < len e)* (len e3 < len e) * (len e4 < len e) * (0 < len e1) * (0 < len e2) * (0 < len e3) * (0 < len e4) }}}} 
    + (    {e1 & {e2 & {e3 & { e4 & ((P1 e1) * P2 e2 * P3 e3 * P4 e4) * (e = e1 ++ e2 ++ e3 ++ e4)* (len e1 < len e)* (len e2 < len e)* (len e3 < len e) * (len e4 < len e) * (0 < len e1) * (0 < len e2) * (0 < len e3) * (0 < len e4) }}}} 
    -> False).
  intros P1 P2 P3 P4. intros.
  eapply cut. eapply (dec_comp3 e X X0 (dec_comp_  X1 X2)); cbn in *; intros.
  intros. destruct_ALL; repeat rewrite app_length in *.

  left. repeat eexists; repeat split; eauto; eauto; try lia.
  right; intros; cbn in *; destruct_ALL; eauto. eapply f; eauto.
  repeat eexists; repeat split; eauto; repeat rewrite app_length in *; try lia. 
Defined. 

(* Recursive Extraction dec_comp3. *)

Theorem gdec_unify:
    forall (e : strs),
    forall {n},
    GDecidable n (fun s => s = e).
    unfold GDecidable.
  intros. destruct (list_eq_dec string_dec e0 e); eauto.
Defined.

(* Recursive Extraction gdec_unify. *)



Definition PN_is_non_empty (PN : StrsP) :=
  forall s,
  PN s -> len s > 0.    

Definition ClauseType (PN : StrsP) : Type :=
  {Sub : StrsP & (forall e, Sub e -> PN e) 
               * (forall e, GDecidable (len e) PN -> (Sub e) + (Sub e -> False))}.

Definition any_of_allclauses (e : strs) {PN : StrsP} (PN_allclauses : list (ClauseType PN)) : Type := (List.fold_right (fun b a => a + ((projT1 b) e) ) (False : Type) PN_allclauses ).

Definition PN_with_allclauses_complete
   {PN : StrsP}
   (PN_allclauses : list (ClauseType PN)) :=
  forall s,
  PN s -> any_of_allclauses s PN_allclauses.


Module RcgDec.

Definition PN_allclauses_sound {PN} (l : list (ClauseType PN)) :
  forall s,
    any_of_allclauses s l -> PN s. 
  unfold any_of_allclauses. 
  generalize dependent l.
  induction l; cbn in *; intros; eauto; try contradiction; unfold ClauseType in *.
  destruct X. 
  eapply IHl; eauto. 
  destruct a as [p1 [h0 h1]].
  cbn in *. eauto.
Defined.

Lemma GDecidable_any_of_allclauses {PN} (l : list (ClauseType PN)):
  forall e, 
    (GDecidable (len e) PN) ->
    (any_of_allclauses e l) + (any_of_allclauses e l -> False).
  unfold any_of_allclauses.
  generalize dependent l.
  induction l; intros; cbn in *;eauto.
  unfold ClauseType in *. 
  destruct a as [p [h0 pgdec]]. cbn in *.
  forwards*: pgdec.
  destruct H.
  left. right. auto.
  forwards*: IHl.
  destruct H. left. left. auto.
  right. intros. destruct X0; eauto.
Defined. 


Definition PN_non_empty_ {PN} (h : PN_is_non_empty PN) :
  (PN []) -> False.
  intros. unfold PN_is_non_empty in *. pose (h _ X) as K; cbn in *. inversion K.
Defined.  

Definition PN_Dec {PN} 
  (l : list (ClauseType PN)) 
  (HH0 : PN_is_non_empty PN) 
  (HH1 : PN_with_allclauses_complete l):
  forall s,
    (PN s) + (PN s -> False).
  intros s.
  remember (len s).
  symmetry in Heqn.
  generalize dependent s. 
  induction n using strong_ind.
  + intros; subst. destruct s; cbn in *; try contradiction; try inversion Heqn. right. eapply PN_non_empty_; eauto.  
  + intros. subst. 
  eapply (cut (GDecidable_any_of_allclauses l)). intros.
  unfold GDecidable in *.
  forwards*: (X0 s).
  destruct H; eauto using (HH1), (PN_allclauses_sound l).
Defined.

End RcgDec.

Definition is_alphabetical_ascii (t : ascii) : bool :=
  let t := nat_of_ascii t in 
  andb (Nat.leb 97 t) (Nat.leb t 122).


Definition is_alphabetical_ (t : string) : bool :=
  let asciis := list_ascii_of_string t in 
  List.fold_left andb (List.map is_alphabetical_ascii asciis) true.

Definition is_alphabetical t := is_alphabetical_ t = true.

Theorem is_alphabetical_dec:
  forall s,
  {is_alphabetical s} + {~is_alphabetical s}.
  intros s; unfold is_alphabetical in *. destruct (is_alphabetical_ s) eqn:hh;
  try (left; eauto; fail);
  try (right; eauto; fail).
Defined.


(* 
General Parsing/Recognizer Facility above
*)

Family Lang.

(* Axiom alphabetical : string -> Prop. *)


(* Axiom is_alphabetical:
  forall s,
    {alphabetical s} + {~ alphabetical s}. *)

(* But to make things easier *)


MetaData _is_atom.
Inductive is_atom : string -> Type :=
  | ia_alphabetical : forall (a : string), is_alphabetical a -> is_atom a.
FEnd _is_atom.

(* Later we can also make is_atom extensible
    and make this Field Overridable pins on is_atom
*)
Field is_atom_dec:
  forall s, 
  (self__Lang.is_atom s) + (self__Lang.is_atom s -> False).
FProof.
intros s.
  destruct (is_alphabetical_dec s) eqn:HH. left; eapply self__Lang.ia_alphabetical; eauto.
  right;intros; try contradiction. inversion H; eauto.
Defined. FEnd is_atom_dec. 




FInductive is_exp : strs -> Type :=
  | ie_atom : forall (a : string), self__Lang.is_atom a -> is_exp ([ a ])
  | ie_addition : forall a b, is_exp a -> is_exp b -> is_exp (a ++ ["+"] ++ b).

Family is_exp_dec.

Field PN : StrsP := self__Lang.is_exp.


FInduction PN_non_empty
about self__Lang.is_exp 
motive (
  fun s (h : self__is_exp_dec.PN s) =>
  len s > 0
).
FProof.
+ intros; cbn in *; auto.
+ intros; cbn in *; repeat rewrite app_length; cbn in *; eauto. try lia. 
Qed. FEnd PN_non_empty.


Field P1 : StrsP := 
  fun l => 
    {a & {b & (self__Lang.is_exp a) * (self__Lang.is_exp b) * (l = a ++ ["+"] ++ b)}}.

Field P1_sound:
  forall s,
    self__is_exp_dec.P1 s ->  self__Lang.is_exp s.
FProof.
  unfold self__is_exp_dec.P1. intros.
  destruct_ALL. eapply self__Lang.ie_addition; eauto.
Defined. FEnd P1_sound.


(* Let's see how hard it is to prove P1_dec with the above helper *)
Field P1_gdec:
  forall e,
    GDecidable (len e) self__Lang.is_exp ->
    (self__is_exp_dec.P1 e) + (self__is_exp_dec.P1 e -> False).
FProof.
  intros e H.  unfold self__is_exp_dec.P1.
  eapply (cut (dec_comp3 e H (gdec_unify ["+"]) H)).
  intros H2. destruct H2.
  destruct_ALL; left; repeat eexists; eauto. 
  right. intros H0.
  eapply f. destruct_ALL. 
  eapply (cut (self__is_exp_dec.PN_non_empty _ i)). eapply (cut (self__is_exp_dec.PN_non_empty _ i0)).
  intros. unfold self__is_exp_dec._auxillary_motive_mod_PN_non_empty420308420.__motiveTPN_non_empty in *.
  repeat eexists; repeat rewrite app_length; cbn in *; eauto; eauto; try lia. 
Defined.  FEnd P1_gdec.



Field P2 : StrsP := 
    fun l => {a & ((self__Lang.is_atom a) : Type) * (l = [a])}.


Field P2_sound:
  forall s,
    self__is_exp_dec.P2 s ->  self__Lang.is_exp s.
FProof.
  unfold self__is_exp_dec.P2. intros.
  destruct_ALL;  eauto. eapply self__Lang.ie_atom; eauto.
Defined. FEnd P2_sound.


Field P2_gdec:
  forall e,
  GDecidable (len e) self__Lang.is_exp ->
  (self__is_exp_dec.P2 e) + (self__is_exp_dec.P2 e -> False).
FProof.
  unfold self__is_exp_dec.P2.
  intros e _ .
  destruct e. right; intros; destruct_ALL; try discriminate.
  destruct e. destruct (self__Lang.is_atom_dec s); eauto.
  right; intros; destruct_ALL; try discriminate. inversion e; subst; eauto.
  right; intros; destruct_ALL; try discriminate.
Defined. FEnd P2_gdec.


(* Definition ClauseType : Type :=
  {Sub : StrsP & (forall e, Sub e -> PN e) 
               * (forall e, GDecidable (len e) PN -> (Sub e) + (Sub e -> False))}. *)

Field PN_allclauses_origin : list (ClauseType self__Lang.is_exp) :=
  [
    (existT _ self__is_exp_dec.P1 (self__is_exp_dec.P1_sound, self__is_exp_dec.P1_gdec));
    (existT _ self__is_exp_dec.P2 (self__is_exp_dec.P2_sound, self__is_exp_dec.P2_gdec))
  ].

Overridable
Field PN_allclauses : list (ClauseType self__Lang.is_exp) :=
  self__is_exp_dec.PN_allclauses_origin.


(* Definition any_of_allclauses (e : strs) : Type :=
  (List.fold_right (fun b a => a + ((projT1 b) e) ) (False : Type) PN_allclauses ). *)

Overridable pins {is_exp PN_allclauses}
Field PN_allclauses_complete :
  forall s, self__Lang.is_exp s -> any_of_allclauses s self__is_exp_dec.PN_allclauses.
FProof.
cbn in *. intros s h; induction h; eauto;
unfold  self__is_exp_dec.P1 in *; unfold self__is_exp_dec.P2 in *.
+ left. right. repeat (eexists; try split; try eauto).
+ right.   repeat (eexists; try split; try eauto).
Qed. FEnd PN_allclauses_complete.



Field is_exp_dec : forall s, (self__Lang.is_exp s) + (self__Lang.is_exp s -> False)
  := RcgDec.PN_Dec 
     (self__is_exp_dec.PN_allclauses)
     (self__is_exp_dec.PN_non_empty)
     (self__is_exp_dec.PN_allclauses_complete).

FEnd is_exp_dec  .


FInductive is_prog : strs -> Type :=
| ip_seq : forall a b, is_prog a -> is_prog b -> is_prog (a ++ [";"] ++ b) 
| ip_assign : forall i e, self__Lang.is_atom i -> self__Lang.is_exp e -> is_prog ([i; ":="] ++ e).


Family is_prog_dec. 

Field PN : StrsP := self__Lang.is_prog.
FInduction PN_non_empty
about self__Lang.is_prog 
motive (
  fun s (h : self__is_prog_dec.PN s) =>
  len s > 0
).
FProof.
+ intros; cbn in *;  repeat rewrite app_length in *; cbn in *; eauto. try lia.  
+ intros; cbn in *; repeat rewrite app_length; cbn in *; eauto. try lia. 
Qed. FEnd PN_non_empty.

Field P1 : StrsP := 
  fun l => {a & {b & self__Lang.is_prog a * (self__Lang.is_prog b) * (l = (a ++ [";"] ++ b))}}.


Field P1_sound:
  forall s,
    self__is_prog_dec.P1 s ->  self__Lang.is_prog s.
FProof.
  unfold self__is_prog_dec.P1. 
  intros e h. destruct_ALL. eapply self__Lang.ip_seq; eauto.   
Defined. FEnd P1_sound.


(* Let's see how hard it is to prove P1_dec with the above helper *)
Field P1_gdec:
  forall e,
    GDecidable (len e) self__Lang.is_prog ->
    (self__is_prog_dec.P1 e) + (self__is_prog_dec.P1 e -> False).
FProof.
unfold self__is_prog_dec.P1. unfold GDecidable in *.
intros e H.
destruct ( (dec_comp3 e H (gdec_unify [";"]) H)).
destruct_ALL; subst; eauto; repeat rewrite app_length in *; left; eauto.
right. intros. eapply f. destruct_ALL; subst; eauto. 
eapply (cut (self__is_prog_dec.PN_non_empty _ i)). eapply (cut (self__is_prog_dec.PN_non_empty _ i0)).
intros. unfold self__is_prog_dec._auxillary_motive_mod_PN_non_empty420308420.__motiveTPN_non_empty in *.
repeat eexists; repeat split; eauto; subst; repeat rewrite app_length in *; eauto; try lia.
Defined.   FEnd P1_gdec.


Field P2 : StrsP :=
  fun l => {a & {b & self__Lang.is_atom a * (self__Lang.is_exp b) * (l = ([a] ++ [":="] ++ b))}}.


Field P2_sound:
  forall e,
    self__is_prog_dec.P2 e -> self__Lang.is_prog e.
FProof. 
  unfold self__is_prog_dec.P2. intros. destruct_ALL; subst. eapply self__Lang.ip_assign; eauto. 
Defined. FEnd P2_sound.


Field is_atom_singleton_dec :
  forall e : strs,
    ((fun l => {a & (self__Lang.is_atom a) * (l = [a])}) e) + 
    ((fun l => {a & (self__Lang.is_atom a) * (l = [a])}) e -> False).
FProof.
  intros e. cbn in *.
  destruct e. right; intros; destruct_ALL; try discriminate.
  destruct e; try (right; intros; destruct_ALL; try discriminate; fail).
  destruct (self__Lang.is_atom_dec s). left; eexists; eauto.
  right; intros; destruct_ALL. inversion e; subst; eauto. 
Defined. FEnd is_atom_singleton_dec.


Field P2_gdec:
  forall e,
    GDecidable (len e) self__Lang.is_prog ->
    (self__is_prog_dec.P2 e) + (self__is_prog_dec.P2 e -> False).
FProof.  
    unfold self__is_prog_dec.P2. 
  intros. destruct (dec_comp3 e (dec_gdec self__is_prog_dec.is_atom_singleton_dec) (gdec_unify [":="]) (dec_gdec self__Lang.is_exp_dec.is_exp_dec)). destruct_ALL; subst; eauto. left.  eexists. eexists. split. split; eauto. auto.  
  right. intros. destruct_ALL. eapply f. repeat eexists; repeat rewrite app_length in *; cbn in *;  eauto; eauto; try lia. inversion i; subst; eauto. eapply  self__Lang.is_exp_dec.PN_non_empty; eauto.
  Unshelve. auto.
Defined. FEnd P2_gdec.


 
Field PN_allclauses_origin : list (ClauseType self__Lang.is_prog) :=
  [
    (existT _ self__is_prog_dec.P1 (self__is_prog_dec.P1_sound, self__is_prog_dec.P1_gdec));
    (existT _ self__is_prog_dec.P2 (self__is_prog_dec.P2_sound, self__is_prog_dec.P2_gdec))
  ].

Overridable 
Field PN_allclauses : list (ClauseType self__Lang.is_prog) :=
  self__is_prog_dec.PN_allclauses_origin.

  
Overridable pins {is_prog PN_allclauses}
Field PN_allclauses_complete :
  forall s, self__Lang.is_prog s -> any_of_allclauses s self__is_prog_dec.PN_allclauses.
FProof. 
intros s h; cbn in *; induction h; eauto;
unfold self__is_prog_dec.P1; unfold self__is_prog_dec.P2 in *. 
+ right. repeat eexists; eauto. 
+ left; right. eexists; eexists. repeat (split;try eauto). 
Qed. FEnd PN_allclauses_complete.



Field is_prog_dec : forall s, (self__Lang.is_prog s) + (self__Lang.is_prog s -> False) 
:= RcgDec.PN_Dec 
(self__is_prog_dec.PN_allclauses)
(self__is_prog_dec.PN_non_empty)
(self__is_prog_dec.PN_allclauses_complete).

FEnd is_prog_dec  .
FEnd Lang.

Family LangMore extends Lang. 
Inherit Until Field is_exp.
FInductive is_exp : strs -> Type :=
| ie_mult : forall a b, is_exp a -> is_exp b -> is_exp (a ++ ["*"] ++ b).

Family is_exp_dec. 

Inherit Until Field PN_non_empty. 

FInduction PN_non_empty.
FProof.
intros. cbn in *; repeat rewrite app_length; cbn in *; eauto. try lia. 
Qed. FEnd PN_non_empty.

Field P3 : StrsP :=
  fun l => 
  {a & {b & (self__LangMore.is_exp a) * (self__LangMore.is_exp b) * (l = a ++ ["*"] ++ b)}}.



Field P3_sound:
  forall s,
    self__is_exp_dec.P3 s ->  self__LangMore.is_exp s.
FProof.
  unfold self__is_exp_dec.P3. intros.
  destruct_ALL. eapply self__LangMore.ie_mult; eauto.
Defined. FEnd P3_sound.


(* Let's see how hard it is to prove P1_dec with the above helper *)
Field P3_gdec:
  forall e,
    GDecidable (len e) self__LangMore.is_exp ->
    (self__is_exp_dec.P3 e) + (self__is_exp_dec.P3 e -> False).
FProof. unfold self__is_exp_dec.P3. intros e H.
eapply (cut (dec_comp3 e H (gdec_unify ["*"]) H)).
intros H2. destruct H2.
destruct_ALL; left; repeat eexists; eauto. 
right. intros H0.
eapply f. destruct_ALL. 
eapply (cut (self__is_exp_dec.PN_non_empty _ i)). eapply (cut (self__is_exp_dec.PN_non_empty _ i0)).
intros. unfold self__is_exp_dec._auxillary_motive_mod_PN_non_empty420308420.__motiveTPN_non_empty in *.
repeat eexists; repeat rewrite app_length; cbn in *; eauto; eauto; try lia.
Defined. FEnd P3_gdec. 

Field PN_allclauses_more : list (ClauseType self__LangMore.is_exp) :=
  [
    (existT _ self__is_exp_dec.P3 (self__is_exp_dec.P3_sound, self__is_exp_dec.P3_gdec))
  ].

Inherit Until Field PN_allclauses.
Override 
Field PN_allclauses : list (ClauseType self__LangMore.is_exp) :=
  self__is_exp_dec.PN_allclauses_origin ++ self__is_exp_dec.PN_allclauses_more.

Override pins {is_exp PN_allclauses}
Field PN_allclauses_complete :
  forall s, self__LangMore.is_exp s -> any_of_allclauses s self__is_exp_dec.PN_allclauses.
FProof.
cbn in *. intros s h; induction h; eauto;
unfold  self__is_exp_dec.P1 in *; unfold self__is_exp_dec.P2 in *; unfold self__is_exp_dec.P3 in *.
+ left. right. repeat (eexists; try split; try eauto).
+ right.   repeat (eexists; try split; try eauto). 
+ left. left. right.   repeat (eexists; try split; try eauto).   
Qed. FEnd PN_allclauses_complete.

FEnd is_exp_dec  .

FInductive is_prog : strs -> Type :=
| ip_if : forall a b, self__LangMore.is_exp a -> is_prog b -> is_prog (["if"] ++ a ++ ["then"] ++ b).

Family is_prog_dec.

Inherit Until Field PN_non_empty.
FInduction PN_non_empty.
FProof.
intros; repeat rewrite app_length; try lia.
Qed. FEnd PN_non_empty.


Field P3 : StrsP :=
  fun l =>
   {a & {b & (self__LangMore.is_exp a) * (self__LangMore.is_prog b) * (l = (["if"] ++ a ++ ["then"] ++ b))}}.


Field P3_sound:
  forall s,
    self__is_prog_dec.P3 s ->  self__LangMore.is_prog s.
FProof.
  unfold self__is_prog_dec.P3. 
  intros e h. destruct_ALL. eapply self__LangMore.ip_if; eauto.   
Defined. FEnd P3_sound.


Field P3_gdec:
  forall e,
    GDecidable (len e) self__LangMore.is_prog ->
    (self__is_prog_dec.P3 e) + (self__is_prog_dec.P3 e -> False).
FProof.
unfold self__is_prog_dec.P3. unfold GDecidable.

intros e H.
destruct ( (dec_comp4 e (gdec_unify ["if"]) (dec_gdec self__LangMore.is_exp_dec.is_exp_dec) (gdec_unify ["then"]) H)).
destruct_ALL; subst; eauto; repeat rewrite app_length in *; left; eauto.
right. intros. eapply f. destruct_ALL; subst; eauto. 
eapply (cut (self__LangMore.is_exp_dec.PN_non_empty _ i)). eapply (cut (self__is_prog_dec.PN_non_empty _ i0)).
intros. 
unfold self__is_prog_dec._auxillary_motive_mod_PN_non_empty420308420.__motiveTPN_non_empty in *.
unfold self__LangMore.is_exp_dec._auxillary_motive_mod_PN_non_empty420308420.__motiveTPN_non_empty in *.
repeat eexists; repeat split; eauto; subst; repeat rewrite app_length in *; eauto; try lia.
Defined. FEnd P3_gdec.

Field PN_allclauses_ift : list (ClauseType self__LangMore.is_prog) :=
  [
    existT _ self__is_prog_dec.P3 (self__is_prog_dec.P3_sound, self__is_prog_dec.P3_gdec)
  ].

Inherit Until Field PN_allclauses.

Override 
Field PN_allclauses : list (ClauseType self__LangMore.is_prog) :=
  (self__is_prog_dec.PN_allclauses_origin) ++ self__is_prog_dec.PN_allclauses_ift .


Override pins {is_prog PN_allclauses}
Field PN_allclauses_complete :
  forall s, self__LangMore.is_prog s -> any_of_allclauses s self__is_prog_dec.PN_allclauses.
FProof. 
intros s h; cbn in *; induction h; eauto;
unfold self__is_prog_dec.P1; unfold self__is_prog_dec.P2 in *; unfold self__is_prog_dec.P3 in *. 
+ right. repeat eexists; eauto. 
+ left; right. eexists; eexists. repeat (split;try eauto). 
+ left; left; right. repeat eexists; eauto.   
Qed. FEnd PN_allclauses_complete.


FEnd is_prog_dec  .

FEnd LangMore.

End CFG_Example.


Module ExtractionTestCases.

Import CFG_Example.LangMore.is_exp_dec.
Import CFG_Example.LangMore.is_prog_dec.

Print is_exp_dec.
Print is_prog_dec.


Definition testcase1 := fun (_ : unit) => is_exp_dec ["a"; "+"; "b"].
Definition testcase2 := fun (_ : unit) => is_exp_dec ["a"; "+"; "b" ; "+"; "c"].

Definition testcase3 := fun (_ : unit) => is_prog_dec ["a"; "+"; "b"; ";"].
Definition testcase4 := fun (_ : unit) => is_prog_dec ["v"; ":="; "a"; "+"; "b"].
Definition testcase5 := fun (_ : unit) => is_prog_dec ["v"; ":="; "a"; "+"; "b"; ";"; "v"; ":="; "a"; "+"; "b"].

End ExtractionTestCases.

Import ExtractionTestCases.
Require Import Coq.extraction.ExtrOcamlNativeString.

Extraction "./testoutput/test1.ml"  testcase1 testcase2 testcase3 testcase4 testcase5.

Check "This ProofScript ends here".

Print CFG_Example.LangMore.