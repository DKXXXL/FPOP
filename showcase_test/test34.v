(* to be used e.g. in : coqtop -I src -R theories Tuto3 < theories/test.v *)

Require Import Fampoly.Loader.
Require Import String.

Open Scope string_scope.

Module Test32.





Family K.

FInductive b : Set 
  := tt : b | ff : b.

FInductive c : Set :=
  | q1 : nat -> c  
  | q2 : c -> c -> c
  | q4 : nat -> c.

FScheme c_prec PRecT about c.


Field test : forall n m , q1 n = q1 m -> n = m. 
FProof.
intros.
finjection  H. destruct H0. eauto.
Qed. FEnd test.

Field test3 : forall n m, q1 n = q4 m -> False.
FProof.
intros. fdiscriminate  H. 
Qed. FEnd test3.

FEnd K.

Family B2 extends K.


FInductive c : Set 
  := q3 : nat -> nat -> c.


Field test2 : forall n m , q3 n 1 = q3 m 1 -> n = m. 
FProof.
intros. 
destruct (self__B2.q3__injective H). eauto.
Qed. FEnd test2.

Override 
Field test3 : forall n m, q1 n = q4 m -> False.
FProof.
intros. fdiscriminate  H. 
Qed. FEnd test3.
FEnd B2.

End Test32.

Check "This ProofScript ends here".
Print Test32.B2.