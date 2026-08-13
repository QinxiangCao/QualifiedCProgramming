Require Import Coq.Classes.Morphisms.

Definition lift_fun0 {A B} (f: B): A -> B :=
  fun _ => f.

Definition lift_fun1 {A B} (f: B -> B): (A -> B) -> (A -> B) :=
  fun x a => f (x a).

Definition lift_fun2 {A B} (f: B -> B -> B): (A -> B) -> (A -> B) -> (A -> B) :=
  fun x y a => f (x a) (y a).

Definition lift_binder {A B} (f: (nat -> B) -> B): (nat -> A -> B) -> (A -> B) :=
  fun xs a => f (fun n => xs n a).

Definition lift_rel1 {A B} (P: B -> Prop): (A -> B) -> Prop :=
  fun x => forall a, P (x a).

Definition lift_rel2 {A B} (P: B -> B -> Prop): (A -> B) -> (A -> B) -> Prop :=
  fun x y => forall a, P (x a) (y a).

Definition lift_set_summary {A B} (F: (B -> Prop) -> B): ((A -> B) -> Prop) -> (A -> B) :=
  fun x a => F (fun b => exists f, x f /\ f a = b).

Lemma lift_fun2_proper: forall {A B} (f: A -> A -> A) (R1 R2 R3: A -> A -> Prop),
  Proper (R1 ==> R2 ==> R3) f ->
  Proper (lift_rel2 R1 ==> lift_rel2 R2 ==> lift_rel2 R3) (@lift_fun2 B _ f).
Proof.
  intros.
  unfold Proper, respectful; intros.
  intros b.
  apply H; auto.
Qed.

