Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Arith.

Lemma strong_induction {P: nat -> Prop}:
  (forall n, (forall m, m < n -> P m) -> P n) ->
  (forall n, P n).
Proof.
  intros ?.
  assert (forall n, (forall m, m < n -> P m)).
  + intro n; induction n.
    - intros; lia.
    - intros.
      destruct (lt_dec m n).
      * apply IHn; auto.
      * assert (m = n) by lia; subst m.
        apply H; auto.
  + intros.
    apply (H0 (S n)).
    constructor.
Qed.

Ltac strong_induction n :=
  generalize dependent n;
  intro n;
  pattern n;
  revert n;
  apply strong_induction;
  intros ?n ?IH.
