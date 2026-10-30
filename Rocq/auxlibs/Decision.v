(* From stdpp *)
Class Decision (P : Prop) := decide : {P} + {~ P}.
Global Arguments decide _ {_} : simpl never, assert.

From Coq.Unicode Require Import Utf8.

(** The following combinators are useful to create Decision proofs in
combination with the [refine] tactic. *)
Notation swap_if S := (match S with left H => right H | right H => left H end).
Notation cast_if S := (if S then left _ else right _).
Notation cast_if_and S1 S2 := (if S1 then cast_if S2 else right _).
Notation cast_if_and3 S1 S2 S3 := (if S1 then cast_if_and S2 S3 else right _).
Notation cast_if_and4 S1 S2 S3 S4 :=
  (if S1 then cast_if_and3 S2 S3 S4 else right _).
Notation cast_if_and5 S1 S2 S3 S4 S5 :=
  (if S1 then cast_if_and4 S2 S3 S4 S5 else right _).
Notation cast_if_and6 S1 S2 S3 S4 S5 S6 :=
  (if S1 then cast_if_and5 S2 S3 S4 S5 S6 else right _).
Notation cast_if_or S1 S2 := (if S1 then left _ else cast_if S2).
Notation cast_if_or3 S1 S2 S3 := (if S1 then left _ else cast_if_or S2 S3).
Notation cast_if_not_or S1 S2 := (if S1 then cast_if S2 else left _).
Notation cast_if_not S := (if S then right _ else left _).

(** * Instances of [Decision] *)
(** Instances of [Decision] for operators of propositional logic. *)
(** The instances for [True] and [False] have a very high cost. If they are
applied too eagerly, HO-unification could wrongfully instantiate TC instances
with [λ .., True] or [λ .., False].
See https://gitlab.mpi-sws.org/iris/stdpp/-/issues/165 *)
Global Instance True_dec: Decision True | 1000 := left I.
Global Instance False_dec: Decision False | 1000 := right (False_rect False).

Section prop_dec.
  Context {P Q} `(P_dec : Decision P) `(Q_dec : Decision Q).

  Global Instance not_dec: Decision (¬P).
  Proof. refine (cast_if_not P_dec); intuition. Defined.
  Global Instance and_dec: Decision (P ∧ Q).
  Proof. refine (cast_if_and P_dec Q_dec); intuition. Defined.
  Global Instance or_dec: Decision (P ∨ Q).
  Proof. refine (cast_if_or P_dec Q_dec); intuition. Defined.
  Global Instance impl_dec: Decision (P → Q).
  Proof. refine (if P_dec then cast_if Q_dec else left _); intuition. Defined.
End prop_dec.
Global Instance iff_dec {P Q} `(P_dec : Decision P) `(Q_dec : Decision Q) :
  Decision (P ↔ Q) := and_dec _ _.

From Coq Require Import List.
Global Instance Forall_dec {A} (P: A -> Prop) `{forall x, Decision (P x)} :
  forall l, Decision (Forall P l).
Proof.
  induction l as [|x xs IH].
  - left. constructor.
  - destruct (decide (P x)) as [Hx | Hx].
    + destruct IH as [Hxs | Hxs].
      * left. constructor; auto.
      * right. intros HForall. inversion HForall. tauto.
    + right. intros HForall. inversion HForall. tauto.
Defined.

(** We can convert decidable propositions to booleans. *)
Definition bool_decide (P : Prop) {dec : Decision P} : bool :=
  if dec then true else false.

Lemma bool_decide_decide P `{!Decision P} :
  bool_decide P = if decide P then true else false.
Proof. reflexivity. Qed.
Lemma decide_bool_decide P {Hdec: Decision P} {X : Type} (x1 x2 : X):
  (if decide P then x1 else x2) = (if bool_decide P then x1 else x2).
Proof. unfold bool_decide, decide. destruct Hdec; reflexivity. Qed.


Lemma bool_decide_eq_true (P : Prop) {dec : Decision P} : bool_decide P = true ↔ P.
Proof. unfold bool_decide. destruct dec; simpl; split; try tauto. congruence. Qed.

Lemma bool_decide_eq_false (P : Prop) {dec : Decision P} : bool_decide P = false ↔ ¬P.
Proof. unfold bool_decide. destruct dec; simpl; split; try tauto. congruence. Qed.
Lemma bool_decide_ext (P Q : Prop) `{Decision P, Decision Q} :
  (P ↔ Q) → bool_decide P = bool_decide Q.
Proof.
  intros HPQ.
  change ((if decide P then true else false) = if decide Q then true else false).
  destruct (decide P) as [p|np], (decide Q) as [q|nq]; simpl; auto.
  - apply HPQ in p. tauto.
  - apply HPQ in q. tauto.
Qed.
Lemma bool_decide_eq_true_1 P `{!Decision P}: bool_decide P = true → P.
Proof. apply bool_decide_eq_true. Qed.
Lemma bool_decide_eq_true_2 P `{!Decision P}: P → bool_decide P = true.
Proof. apply bool_decide_eq_true. Qed.

Lemma bool_decide_eq_false_1 P `{!Decision P}: bool_decide P = false → ¬P.
Proof. apply bool_decide_eq_false. Qed.
Lemma bool_decide_eq_false_2 P `{!Decision P}: ¬P → bool_decide P = false.
Proof. apply bool_decide_eq_false. Qed.



(** Truncation of a decidable proposition to a mere proposition *)
Definition trunc_dec (P : Prop) {d : Decision P} : Prop :=
  match decide P with
  | left _ => True
  | right _ => False
  end.
Global Arguments trunc_dec _ {_} : simpl never, assert.


Definition trunc_dec_intro [P : Prop] {d : Decision P} : P -> trunc_dec P.
Proof. intros p. unfold trunc_dec. destruct (decide P) as [p'|np]; auto. Defined.

Definition trunc_dec_elim [P : Prop] {d : Decision P} : trunc_dec P -> P.
Proof. unfold trunc_dec. destruct (decide P) as [p|np]; auto. intros []. Defined.

Lemma trunc_dec_iff (P : Prop) {d : Decision P} : trunc_dec P <-> P.
Proof. split; [apply trunc_dec_elim | apply trunc_dec_intro]. Qed.

Lemma trunc_dec_eq [P : Prop] {d : Decision P} : forall (p q : trunc_dec P), p = q.
Proof. unfold trunc_dec. destruct (decide P); intros [] []; auto. Qed.

(* Transparent versions of proj1, proj2 *)
Definition proj1 [A B : Prop] (p : A /\ B) : A :=
  match p with
  | conj a b => a
  end.
Definition proj2 [A B : Prop] (p : A /\ B) : B :=
  match p with
  | conj a b => b
  end.
