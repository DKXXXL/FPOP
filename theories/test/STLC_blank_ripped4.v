From Coq Require Import Strings.String.
From Fampoly Require Import LibTactics.
From Fampoly Require Import Maps.

(* From Top.PLF Require Import Smallstep. *)
From Coq Require Import Nat.


Module Type Lang.
Parameter ty: Type.
Parameter ty_arrow : ty -> ty -> ty.

Notation ID := string.

Parameter tm : Set.
Parameter value : Set.

Parameter tm_pure : value -> tm.
Parameter  tm_let : ID -> tm -> tm -> tm.
Parameter  tm_app : value -> value -> tm.


Parameter tm_var : ID -> value. (* The only unwanted value *)
Parameter tm_abs : ID ->  ty -> tm -> value.


(* TODO : Add partial recursor signature to here *)

Parameter subst_tm : ID -> value -> tm -> tm.
Parameter subst_v : ID -> value -> value -> value.

Parameter fv : ID -> tm -> Prop.
Parameter fvv : ID -> value -> Prop.
Parameter fv_pure : forall x v, fvv x v -> fv x (tm_pure v).
Parameter fv_let1 : forall x i a body, fv x a -> fv x (tm_let i a body).
Parameter fv_let2 : forall x i a body, fv x body -> x <> i -> fv x (tm_let i a body).

Parameter fv_app1 : forall x a b, fvv x a -> fv x (tm_app a b).

Parameter fv_app2 : forall x a b, fvv x b -> fv x (tm_app a b).

Parameter fv_var : forall x, fvv x (tm_var x).

Parameter fv_abs :  forall x v T body, fv x body -> x <> v -> fvv x (tm_abs v T body).


End Lang.

(* Fixpoint subst_tm (x : ID) (s: value) (t: tm) : tm  :=
  let sub k := subst_tm x s k in 
  match t with
  | tm_let i bind body => 
    if (eqb_string x i) then tm_let i (sub bind) body 
    else tm_let i (sub bind) (sub body) 
  | tm_app a b =>  tm_app (subst_v x s a) (subst_v x s  b)
  | tm_pure v => tm_pure (subst_v x s v)
  end
with subst_v (x : ID) (s : value) (t : value) : value :=
  let sub k := subst_v x s k in 
  match t with 
  | tm_var i => if (eqb_string x i) then s else t
  | tm_abs i T body => 
      if (eqb_string x i) then t else (tm_abs i T (subst_tm x s body))
  end. *)
  
  

(* Declare Custom Entry stlc.

Notation "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc at level 201). *)

Module Type LangQ (L : Lang).
Include L.

Parameter step : tm -> tm -> Prop.
Parameter st_let0 : forall i a a' body, 
step a a' -> step (tm_let i a body) (tm_let i a' body).
Parameter st_let1 : forall i a body,
step (tm_let i (tm_pure a) body) (subst_tm i a body).
Parameter st_app : forall i v T body,
step (tm_app (tm_abs i T body) v) (subst_tm i v body).

Parameter step_app_inversion :
  forall x y z,
    step (tm_app x y) z ->
    (exists i T body, 
      x = tm_abs i T body /\ 
      z = subst_tm i y body
    ).

Parameter step_tm_pure_inv:
  forall x y,
    ~ step (tm_pure x) y.

Definition canonical_value x := (forall i, x <> tm_var i).
Definition canonical_term x := exists v, x = tm_pure v /\ canonical_value v.

  

Inductive steps : tm -> tm -> Prop:=
  | sts_refl : forall x, steps x x
  | sts_trans : forall x y z, step x y -> steps y z -> steps x z.
  
Definition context := partial_map ty.

Parameter has_type : context -> tm -> ty -> Prop.
Parameter has_type_v : context -> value -> ty -> Prop.

Parameter ht_app : forall G x y T1 T2,
has_type_v G x (ty_arrow T1 T2) ->
has_type_v G y T1 ->
has_type G (tm_app x y) T2.

Parameter ht_let : forall G bind body i T1 T2,
has_type G bind T1 ->
has_type (i |-> T1; G) body T2 ->
has_type G (tm_let i bind body) T2.

Parameter ht_pure : forall G v T,
has_type_v G v T ->
has_type G (tm_pure v) T.


Parameter ht_var : forall G x T1,
G x = Some T1 ->
has_type_v G (tm_var x) T1.

Parameter ht_abs : forall G x body T1 T2,
has_type (x |-> T1; G) body T2 ->
has_type_v G (tm_abs x T1 body) (ty_arrow T1 T2).

Parameter ht_abs_inv : forall G x body T1 T2 T3,
has_type_v G (tm_abs x T3 body) (ty_arrow T1 T2) -> 
has_type (x |-> T1; G) body T2.


Notation "Gamma '⊢' t '∈' T" := (has_type Gamma t T) 
    (at level 101).
Notation "Gamma '⊢*' t '∈' T" := (has_type_v Gamma t T) 
    (at level 101).

End LangQ.


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

Module stlc_progress_handlers (L : Lang) (Q : LangQ L).

(* Include L.  *)
Include Q.





Lemma value_arrow_type_inv:
  forall t A B,
  has_type_v empty t (ty_arrow A B) ->
  exists i T body, t = tm_abs i T body.
Admitted.




(* Scheme has_type_indm := Minimality for has_type Sort Prop
  with has_typev_indm := Minimality for has_type_v Sort Prop.
  
Print has_type_indm. *)

(* 
     : forall (P : context -> tm -> ty -> Prop)
         (P0 : context -> value -> ty -> Prop),
       (forall (G : context) (x y : value) (T1 T2 : ty),
        (G ⊢* x ∈ ty_arrow T1 T2) ->
        P0 G x (ty_arrow T1 T2) ->
        (G ⊢* y ∈ T1) -> P0 G y T1 -> P G (tm_app x y) T2) ->
       (forall (G : context) (bind body : tm) (i : ID) (T1 T2 : ty),
        (G ⊢ bind ∈ T1) ->
        P G bind T1 ->
        (i |-> T1; G ⊢ body ∈ T2) ->
        P (i |-> T1; G) body T2 -> P G (tm_let i bind body) T2) ->
       (forall (G : context) (v : value) (T : ty),
        (G ⊢* v ∈ T) -> P0 G v T -> P G (tm_pure v) T) ->
       (forall (G : ID -> option ty) (x : ID) (T1 : ty),
        G x = Some T1 -> P0 G (tm_var x) T1) ->
       (forall (G : partial_map ty) (x : ID) (body : tm) (T1 T2 : ty),
        (x |-> T1; G ⊢ body ∈ T2) ->
        P (x |-> T1; G) body T2 -> P0 G (tm_abs x T1 body) (ty_arrow T1 T2)) ->
       forall (c : context) (t : tm) (t0 : ty), (c ⊢ t ∈ t0) -> P c t t0
*)


(* this motive is based on has_type_ind instead of has_type_indcomp 
note that, has_type_ind at the end looks like

forall (c : context) (t : tm) (t0 : ty), (c ⊢ t ∈ t0) -> P c t t0

So P is irrelevant w.r.t. proof term of has_type
*)
Definition P : context -> tm -> ty -> Prop  :=
    fun G x T  => 
      G = empty ->
      (canonical_term x) \/ (exists x' , step x x').

(* I think the key point here for code reuse is that, 
    P0 might never change *)
Definition P0 :  context -> value -> ty -> Prop :=
    fun G x T =>
      G = empty ->
      canonical_value x.

(* This one is the one being inherited *)
Lemma stlc_progress_app' :
  (forall (G : context) (x y : value) (T1 T2 : ty),
  (G ⊢* x ∈ ty_arrow T1 T2) -> P G (tm_app x y) T2).

repeat (intro; intros); subst; eauto.
forwards*: value_arrow_type_inv. destruct_ALL; subst; auto.
right; eexists; eauto using st_app.
Qed.

(* This one is the real handler *)
Lemma stlc_progress_app :
  (forall (G : context) (x y : value) (T1 T2 : ty),
  (G ⊢* x ∈ ty_arrow T1 T2) ->
  P0 G x (ty_arrow T1 T2) ->
  (G ⊢* y ∈ T1) -> P0 G y T1 -> P G (tm_app x y) T2).
  eauto using stlc_progress_app'.
Qed.

(* The key point is that, the inherited one 'stlc_progress_app'' is the one only care about *value* that control the stepping
   so it can be easily reused, and P0 should never change
*)


(* because let is the only one having congruence
    I think any prop using congruence cannot be reused *)
Lemma stlc_progress_let:
(forall (G : context) (bind body : tm) (i : ID) (T1 T2 : ty),
(G ⊢ bind ∈ T1) ->
P G bind T1 ->
(i |-> T1; G ⊢ body ∈ T2) ->
P (i |-> T1; G) body T2 -> P G (tm_let i bind body) T2).

repeat (intro; intros); subst; eauto. unfold P in *.
clear H2. destruct (H0 eq_refl); unfold canonical_term in *;
destruct_ALL; subst; eauto; right; eexists; eauto using st_let0, st_let1.
Qed. 


(* This one should be able to be reused all the time *)
Lemma stlc_progress_tm_pure :
(forall (G : context) (v : value) (T : ty),
(G ⊢* v ∈ T) -> P0 G v T -> P G (tm_pure v) T).
repeat (intro; intros); subst; eauto. unfold P0 in *.
unfold canonical_term in *; unfold canonical_value in *; eauto.
Qed. 

(* This one should be able to be reused all the time *)
Lemma  stlc_progress_tm_var :
  (forall (G : ID -> option ty) (x : ID) (T1 : ty),
  G x = Some T1 -> P0 G (tm_var x) T1).
repeat (intro; intros); eauto; subst; eauto; cbv in *; try discriminate.
Qed.

Lemma  stlc_progress_tm_abs' :
(forall (G : partial_map ty) (x : ID) (body : tm) (T1 T2 : ty),
(x |-> T1; G ⊢ body ∈ T2) ->
P0 G (tm_abs x T1 body) (ty_arrow T1 T2)).
repeat (intro; intros); eauto; subst; eauto; try discriminate.
(* require discriminate *)
Admitted.
(* This one require injectivity of the contructor of tm
    I think it definitely holds *)
Lemma  stlc_progress_tm_abs :
(forall (G : partial_map ty) (x : ID) (body : tm) (T1 T2 : ty),
(x |-> T1; G ⊢ body ∈ T2) ->
P (x |-> T1; G) body T2 -> P0 G (tm_abs x T1 body) (ty_arrow T1 T2)).
intros; eapply stlc_progress_tm_abs'; eauto.
Qed.


End stlc_progress_handlers.




Module stlc_preservation (L : Lang) (Q : LangQ L).
Include Q.

Lemma subst_lemma:
  forall G x body k T1 T2,
    has_type (update G x T1) body T2 ->
    (forall G', has_type_v G' k T1) ->
    has_type G (subst_tm x k body) T2.

Admitted.

(* Lemma subst_lemma_v:
  forall G x body k T1 T2,
    has_type_v (update G x T1) body T2 ->
    (forall G', has_type_v G' k T1) ->
    has_type_v G (subst_v x k body) T2.
Admitted.

(* We also need free-var as well *)

Theorem free_var_in_ctx:
  forall G x t T ,
    has_type G t T ->
    fv x t ->
    exists U, G x = Some U.
Admitted.

Theorem free_var_in_ctx_v:
  forall G x t T ,
    has_type_v G t T ->
    fvv x t ->
    exists U, G x = Some U.
Admitted.


Theorem free_var_matters:
  forall G1 G2 t T,
  (forall x,
    fv x t -> G1 x = G2 x) ->
  has_type G1 t T ->
  has_type G2 t T.
Admitted.


Theorem weakening_lemma:
  forall k T,
    has_type empty k T ->
    (forall G, has_type G k T).
Admitted. *)

Theorem weakening_lemma_v:
  forall k T,
    has_type_v empty k T ->
    (forall G, has_type_v G k T).
Admitted.

(* Print has_type_indm. *)

Module stlc_preservation_handler.

Definition P : context -> tm -> ty -> Prop  :=
  fun G x T => 
  G = empty ->
  forall x', 
  step x x' ->
  has_type empty x' T.

Definition P0 :  context -> value -> ty -> Prop :=
  fun G v T => True.

(* only possible place to be reused 
    just like progress *)
Theorem case_tm_app :
  (forall (G : context) (x y : value) (T1 T2 : ty),
  (G ⊢* x ∈ ty_arrow T1 T2) ->
  P0 G x (ty_arrow T1 T2) ->
  (G ⊢* y ∈ T1) -> P0 G y T1 -> P G (tm_app x y) T2).
unfold P in *. unfold P0 in *. intros; subst; eauto.
forwards*: step_app_inversion; destruct_ALL.
forwards*: ht_abs_inv; eauto.
eapply subst_lemma; eauto. 
eapply weakening_lemma_v; eauto.
Qed.

(* imagine the type for tm_if 
  (forall (G : context) (c : value) (t1 t2 : term) (T : ty),
  (G ⊢* c ∈ Bool) ->
  P0 G c Bool ->
  (G ⊢* t1 ∈ T) ->
  P G t1 T -> 
  (G ⊢* t2 ∈ T) ->
  -> P G t2 T -> P G (tm_if c t1 t2) T).

  we in turn prove 
  (forall (G : context) (c : value) (t1 t2 : term) (T : ty),
  (G ⊢* c ∈ Bool) ->
  (G ⊢* t1 ∈ T) ->

  (G ⊢* t2 ∈ T) -> -> P G (tm_if c t1 t2) T).
  ≡
    (forall (G : context) (c : value) (t1 t2 : term) (T : ty),
  (G ⊢* c ∈ Bool) ->
  (G ⊢ t1 ∈ T) ->
  (G ⊢ t2 ∈ T) ->
  -> G = empty -> forall x', step (tm_if c t1 t2) x' -> empty |- x' : T.

  this should be easy to prove by using inversion lemma of tm_if

*)

(* the only place of code reuse... *)
Theorem case_tm_pure :
(forall (G : context) (v : value) (T : ty),
(G ⊢* v ∈ T) -> P0 G v T -> P G (tm_pure v) T).
unfold P ; unfold P0; intros; subst; eauto.
destruct (step_tm_pure_inv _ _ H2).
Qed.

(* Apparently there is no code reuse here, because P0 ... = True *)
Theorem case_tm_var :
(forall (G : ID -> option ty) (x : ID) (T1 : ty),
G x = Some T1 -> P0 G (tm_var x) T1).
unfold P0;repeat (intro; intros); eauto.
Qed.

Theorem case_tm_abs : 
(forall (G : partial_map ty) (x : ID) (body : tm) (T1 T2 : ty),
(x |-> T1; G ⊢ body ∈ T2) ->
P (x |-> T1; G) body T2 -> P0 G (tm_abs x T1 body) (ty_arrow T1 T2)).
unfold P0;repeat (intro; intros); eauto.
Qed.

Theorem case_tm_let :
(forall (G : context) (bind body : tm) (i : ID) (T1 T2 : ty),
(G ⊢ bind ∈ T1) ->
P G bind T1 ->
(i |-> T1; G ⊢ body ∈ T2) ->
P (i |-> T1; G) body T2 -> P G (tm_let i bind body) T2).
unfold P ; unfold P0; intros; subst; eauto.
Admitted.



End stlc_preservation_handler.
End stlc_preservation.