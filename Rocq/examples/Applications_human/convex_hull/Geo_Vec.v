(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope Z.
(* /COQ-HEAD *)

Record vec: Type := {
  vec_x: Z;
  vec_y: Z;
}.

Module VecNotation.

Notation "v '.(x)'" := (vec_x v) (at level 1).
Notation "v '.(y)'" := (vec_y v) (at level 1).

End VecNotation.

Import VecNotation.

Definition cross_prod (v1 v2: vec): Z :=
  v1.(x) * v2.(y) - v2.(x) * v1.(y).

Definition dot_prod (v1 v2: vec): Z :=
  v1.(x) * v2.(x) + v1.(y) * v2.(y).

Definition left_equal (v1 v2: vec): Prop :=
  cross_prod v1 v2 <= 0.

Definition left_than (v1 v2: vec): Prop :=
  cross_prod v1 v2 < 0.

Definition nonzero (v: vec): Prop :=
  dot_prod v v <> 0.

Definition perp (v1 v2: vec): Prop :=
  dot_prod v1 v2 = 0.

Definition parallel (v1 v2: vec): Prop :=
  cross_prod v1 v2 = 0.

Definition forward_dir (v1 v2: vec): Prop :=
  dot_prod v1 v2 > 0.

Definition backward_dir (v1 v2: vec): Prop :=
  dot_prod v1 v2 < 0.

Definition forward_or_perp (v1 v2: vec): Prop :=
  dot_prod v1 v2 >= 0.

Definition backward_or_perp (v1 v2: vec): Prop :=
  dot_prod v1 v2 <= 0.

Lemma cross_prod_comm: forall v1 v2,
  cross_prod v1 v2 = - cross_prod v2 v1.
Proof. unfold cross_prod. intros. lia. Qed.

Lemma cross_prod_self: forall v,
  cross_prod v v = 0.
Proof. unfold cross_prod. intros. lia. Qed.

Lemma dot_prod_comm: forall v1 v2,
  dot_prod v1 v2 = dot_prod v2 v1.
Proof. unfold dot_prod. intros. lia. Qed.

Lemma metric_nonneg: forall v,
  dot_prod v v >= 0.
Proof. unfold dot_prod. intros. nia. Qed.

Lemma nonzero_iff: forall v,
  nonzero v <-> dot_prod v v > 0.
Proof.
  unfold nonzero.
  intros.
  pose proof metric_nonneg v.
  nia.
Qed.

Lemma zero_or_nonzero: forall v,
  v.(x) = 0 /\ v.(y) = 0 \/ nonzero v.
Proof.
  intros.
  unfold nonzero, dot_prod.
  nia.
Qed.

Lemma forward_or_perp_iff: forall v1 v2,
  forward_or_perp v1 v2 <->
  forward_dir v1 v2 \/ perp v1 v2.
Proof. unfold forward_or_perp, forward_dir, perp; lia. Qed.

Lemma backward_or_perp_iff: forall v1 v2,
  backward_or_perp v1 v2 <->
  backward_dir v1 v2 \/ perp v1 v2.
Proof. unfold backward_or_perp, backward_dir, perp; lia. Qed.

Lemma left_equal_iff: forall v1 v2,
  left_equal v1 v2 <-> 
  left_than v1 v2 \/ parallel v1 v2.
Proof. unfold left_equal, left_than, parallel; lia. Qed.

Lemma parallel_refl: forall v,
  parallel v v.
Proof. unfold parallel, cross_prod. intros. lia. Qed.

Lemma parallel_sym: forall v1 v2,
  parallel v1 v2 ->
  parallel v2 v1.
Proof. unfold parallel, cross_prod. intros. lia. Qed.

(** parallel_trans? nontrivial! will be proved later. *)

Lemma forward_dir_refl: forall v,
  nonzero v -> forward_dir v v.
Proof.
  intros.
  rewrite nonzero_iff in H.
  unfold forward_dir.
  tauto.
Qed.

Lemma forward_dir_symm: forall v1 v2,
  forward_dir v1 v2 -> forward_dir v2 v1.
Proof. unfold forward_dir, dot_prod; nia. Qed.

Lemma forward_or_perp_refl: forall v,
  forward_or_perp v v.
Proof.
  intros.
  pose proof metric_nonneg v.
  unfold forward_or_perp.
  tauto.
Qed.

Lemma forward_or_perp_symm: forall v1 v2,
  forward_or_perp v1 v2 -> forward_or_perp v2 v1.
Proof. unfold forward_or_perp, dot_prod; nia. Qed.

Lemma backward_dir_symm: forall v1 v2,
  backward_dir v1 v2 -> backward_dir v2 v1.
Proof. unfold backward_dir, dot_prod; nia. Qed.

Lemma backward_or_perp_symm: forall v1 v2,
  backward_or_perp v1 v2 -> backward_or_perp v2 v1.
Proof. unfold backward_or_perp, dot_prod; nia. Qed.

Lemma aux2: forall v v1 v2: vec,
  cross_prod v1 v2 * dot_prod v v =
  cross_prod v1 v * dot_prod v2 v -
  cross_prod v2 v * dot_prod v1 v.
Proof. unfold cross_prod, dot_prod. nia. Qed.

Lemma aux3: forall v v1 v2 v3: vec,
  cross_prod v1 v3 * dot_prod v v * cross_prod v2 v =
  cross_prod v1 v * (cross_prod v2 v * dot_prod v3 v -
                     cross_prod v3 v * dot_prod v2 v) +
  cross_prod v3 v * (cross_prod v1 v * dot_prod v2 v -
                     cross_prod v2 v * dot_prod v1 v).
Proof. unfold cross_prod, dot_prod. nia. Qed.

Lemma le_trans: forall v v1 v2 v3: vec,
  left_than v1 v ->
  left_than v2 v ->
  left_equal v3 v ->
  left_equal v1 v2 ->
  left_equal v2 v3 ->
  left_equal v1 v3.
Proof.
  unfold left_equal, left_than, cross_prod.
  intros.
  nia.
Qed.

(** Translate inequality *)
Lemma aux: forall v v1 v2: vec,
  dot_prod v1 v2 * dot_prod v v =
  dot_prod v1 v * dot_prod v2 v +
  cross_prod v1 v * cross_prod v2 v.
Proof.
  unfold dot_prod, cross_prod.
  intros.
  nia.
Qed.

Lemma forward_left: forall v v1 v2: vec,
  forward_dir v v1 ->
  forward_dir v v2 ->
  left_than v1 v ->
  left_than v2 v ->
  forward_dir v1 v2.
Proof.
  unfold left_than, forward_dir, cross_prod, dot_prod.
  intros.
  nia.
Qed.

Theorem cross_dot_eqn: forall v1 v2,
  dot_prod v1 v1 * dot_prod v2 v2 =
  cross_prod v1 v2 * cross_prod v1 v2 +
  dot_prod v1 v2 * dot_prod v1 v2.
Proof.
  unfold dot_prod, cross_prod.
  intros.
  nia.
Qed.

Lemma left_than_nonzero: forall v1 v2,
  left_than v1 v2 ->
  nonzero v1 /\ nonzero v2.
Proof.
  intros.
  pose proof sqr_pos (dot_prod v1 v2).
  pose proof cross_dot_eqn v1 v2.
  unfold left_than in H.
  unfold nonzero.
  nia.
Qed.

Lemma perp_parallel: forall v1 v2,
  perp v1 v2 ->
  parallel v1 v2 ->
  nonzero v1 ->
  nonzero v2 ->
  False.
Proof.
  intros.
  pose proof cross_dot_eqn v1 v2.
  unfold perp, parallel, nonzero, cross_prod, dot_prod in *.
  rewrite H, H0 in H3.
  nia.
Qed.

Lemma left_than_nonzero1: forall v1 v2,
  left_than v1 v2 ->
  nonzero v1.
Proof. intros. apply left_than_nonzero in H. tauto. Qed.

Lemma left_than_nonzero2: forall v1 v2,
  left_than v1 v2 ->
  nonzero v2.
Proof. intros. apply left_than_nonzero in H. tauto. Qed.

Lemma fwd_nonzero: forall v1 v2,
  forward_dir v1 v2 ->
  nonzero v1 /\ nonzero v2.
Proof.
  intros.
  pose proof sqr_pos (cross_prod v1 v2).
  pose proof cross_dot_eqn v1 v2.
  unfold forward_dir in H.
  unfold nonzero.
  nia.
Qed.

Lemma parallel_trans: forall v1 v2 v3,
  parallel v1 v2 ->
  parallel v2 v3 ->
  nonzero v2 ->
  parallel v1 v3.
Proof.
  unfold parallel, nonzero, cross_prod, dot_prod.
  intros.
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v3.(y) = 0).
  { rewrite H. lia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v3.(x) = 0).
  { rewrite H. lia. }
  assert ((v2.(x) * v3.(y) - v3.(x) * v2.(y)) * v1.(y) = 0).
  { rewrite H0. lia. }
  assert ((v2.(x) * v3.(y) - v3.(x) * v2.(y)) * v1.(x) = 0).
  { rewrite H0. lia. }
  assert ((v1.(x) * v3.(y) - v3.(x) * v1.(y)) * v2.(x) = 0).
  { nia. }
  assert ((v1.(x) * v3.(y) - v3.(x) * v1.(y)) * v2.(y) = 0).
  { nia. }
  assert ((v1.(x) * v3.(y) - v3.(x) * v1.(y)) * v2.(x) * v2.(x) = 0).
  { rewrite H6. lia. }
  assert ((v1.(x) * v3.(y) - v3.(x) * v1.(y)) * v2.(y) * v2.(y) = 0).
  { rewrite H7. lia. }
  nia.
Qed.

Lemma perp_perp: forall v v1 v2,
  perp v v1 ->
  perp v v2 ->
  nonzero v ->
  parallel v1 v2.
Proof.
  unfold perp, nonzero, parallel, cross_prod, dot_prod.
  intros.
  assert ((v.(x) * v1.(x) + v.(y) * v1.(y)) * v2.(y) = 0).
  { rewrite H. lia. }
  assert ((v.(x) * v1.(x) + v.(y) * v1.(y)) * v2.(x) = 0).
  { rewrite H. lia. }
  assert ((v.(x) * v2.(x) + v.(y) * v2.(y)) * v1.(y) = 0).
  { rewrite H0. lia. }
  assert ((v.(x) * v2.(x) + v.(y) * v2.(y)) * v1.(x) = 0).
  { rewrite H0. lia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(x) = 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(y) = 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(x) * v.(x) = 0).
  { rewrite H6. lia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(y) * v.(y) = 0).
  { rewrite H7. lia. }
  nia.
Qed.

Lemma left_equal_same_dir_l: forall v1 v2 v,
  parallel v1 v2 ->
  forward_dir v1 v2 ->
  left_equal v1 v ->
  left_equal v2 v.
Proof.
  unfold parallel, forward_dir, left_equal, cross_prod, dot_prod.
  intros.
  assert ((v1.(x) * v.(y) - v.(x) * v1.(y)) * v2.(y) * v2.(y) <= 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(y) * v2.(y) = 0).
  { rewrite H. lia. }
  assert ((v2.(x) * v.(y) - v.(x) * v2.(y)) * (v1.(y) * v2.(y)) <= 0).
  { nia. }
  assert ((v1.(x) * v.(y) - v.(x) * v1.(y)) * v2.(x) * v2.(x) <= 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(x) * v2.(x) = 0).
  { rewrite H. lia. }
  assert ((v2.(x) * v.(y) - v.(x) * v2.(y)) * (v1.(x) * v2.(x)) <= 0).
  { nia. }
  assert ((v2.(x) * v.(y) - v.(x) * v2.(y)) * (v1.(x) * v2.(x) + v1.(y) * v2.(y)) <= 0).
  { nia. }
  nia.
Qed.

Lemma left_than_same_dir_l: forall v1 v2 v,
  parallel v1 v2 ->
  forward_dir v1 v2 ->
  left_than v1 v ->
  left_than v2 v.
Proof.
  intros.
  pose proof fwd_nonzero _ _ H0 as [? ?].
  unfold parallel, forward_dir, left_than in *.
  rewrite nonzero_iff in H2, H3.
  assert (cross_prod v1 v * dot_prod v2 v2 <= 0) by nia.
  unfold dot_prod, cross_prod in *.
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(y) * v2.(y) = 0).
  { rewrite H. lia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(x) * v2.(x) = 0).
  { rewrite H. lia. }
  assert ((v2.(x) * v.(y) - v.(x) * v2.(y)) * (v1.(x) * v2.(x) + v1.(y) * v2.(y)) < 0).
  { nia. }
  nia.
Qed.

Lemma left_equal_same_dir_r: forall v1 v2 v,
  parallel v1 v2 ->
  forward_dir v1 v2 ->
  left_equal v v1 ->
  left_equal v v2.
Proof.
  unfold parallel, forward_dir, left_than, left_equal, cross_prod, dot_prod.
  intros.
  assert ((v.(x) * v1.(y) - v1.(x) * v.(y)) * v2.(y) * v2.(y) <= 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(y) * v2.(y) = 0).
  { rewrite H. lia. }
  assert ((v.(x) * v2.(y) - v2.(x) * v.(y)) * (v1.(y) * v2.(y)) <= 0).
  { nia. }
  assert ((v.(x) * v1.(y) - v1.(x) * v.(y)) * v2.(x) * v2.(x) <= 0).
  { nia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(x) * v2.(x) = 0).
  { rewrite H. lia. }
  assert ((v.(x) * v2.(y) - v2.(x) * v.(y)) * (v1.(x) * v2.(x)) <= 0).
  { nia. }
  assert ((v.(x) * v2.(y) - v2.(x) * v.(y)) * (v1.(x) * v2.(x) + v1.(y) * v2.(y)) <= 0).
  { nia. }
  nia.
Qed.

Lemma left_than_same_dir_r: forall v1 v2 v,
  parallel v1 v2 ->
  forward_dir v1 v2 ->
  left_than v v1 ->
  left_than v v2.
Proof.
  intros.
  pose proof fwd_nonzero _ _ H0 as [? ?].
  unfold parallel, forward_dir, left_than in *.
  rewrite nonzero_iff in H2, H3.
  assert (cross_prod v v1 * dot_prod v2 v2 < 0) by nia.
  unfold dot_prod, cross_prod in *.
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(y) * v2.(y) = 0).
  { rewrite H. lia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y)) * v.(x) * v2.(x) = 0).
  { rewrite H. lia. }
  assert ((v.(x) * v2.(y) - v2.(x) * v.(y)) * (v1.(x) * v2.(x) + v1.(y) * v2.(y)) < 0).
  { nia. }
  nia.
Qed.

Lemma left_equal_same_dir_r': forall v1 v2 v,
  parallel v1 v2 ->
  forward_or_perp v1 v2 ->
  left_than v v1 ->
  left_equal v v2.
Proof.
  intros.
  destruct (zero_or_nonzero v2) as [[? ?] | ?].
  1: {
    unfold left_equal, cross_prod.
    rewrite H2, H3; lia.
  }
  pose proof left_than_nonzero2 _ _ H1.
  rewrite forward_or_perp_iff in H0.
  destruct H0.
  + pose proof left_than_same_dir_r v1 v2 v
               ltac:(tauto) ltac:(tauto) ltac:(tauto).
    rewrite left_equal_iff.
    tauto.
  + pose proof perp_parallel _ _ H0 H.
    tauto.
Qed.

Lemma fwd_perp_bwd_dec: forall v1 v2,
  forward_dir v1 v2 \/ perp v1 v2 \/ backward_dir v1 v2.
Proof.
  unfold forward_dir, perp, backward_dir, dot_prod.
  intros.
  destruct (Ztrichotomy_inf (v1.(x) * v2.(x) + v1.(y) * v2.(y)) 0)
    as [[H1 | H1] | H1]; try tauto.
Qed.

Lemma double_left_than_parallel: forall v1 v2 v3,
  parallel v1 v3 ->
  left_than v3 v2 ->
  left_than v2 v1 ->
  backward_dir v1 v3.
Proof.
  intros.
  destruct (fwd_perp_bwd_dec v1 v3) as [? | [? | ?]].
  + pose proof left_than_same_dir_r v1 v3 v2 ltac:(tauto) ltac:(tauto) ltac:(tauto).
    clear - H0 H3.
    unfold left_than, cross_prod in *.
    nia.
  + apply left_than_nonzero1 in H0.
    apply left_than_nonzero2 in H1.
    pose proof perp_parallel v1 v3.
    tauto.
  + tauto.
Qed.

(** Exercise begin *)

Definition left_45deg (v1 v2: vec): Prop :=
  cross_prod v1 v2 + dot_prod v1 v2 = 0.

Lemma double_left_45deg: forall v1 v2 v3,
  left_45deg v1 v2 ->
  left_45deg v2 v3 ->
  nonzero v2 ->
  perp v1 v3.
Proof.
  unfold left_45deg, nonzero, perp, dot_prod, cross_prod.
  intros.
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y) + (v1.(x) * v2.(x) + v1.(y) * v2.(y))) * (v3.(x) + v3.(y)) = 0).
  { rewrite H. lia. }
  assert ((v1.(x) * v2.(y) - v2.(x) * v1.(y) + (v1.(x) * v2.(x) + v1.(y) * v2.(y))) * (v3.(x) - v3.(y)) = 0).
  { rewrite H. lia. }
  assert ((v2.(x) * v3.(y) - v3.(x) * v2.(y) + (v2.(x) * v3.(x) + v2.(y) * v3.(y))) * (v1.(x) + v1.(y)) = 0).
  { rewrite H0. lia. }
  assert ((v2.(x) * v3.(y) - v3.(x) * v2.(y) + (v2.(x) * v3.(x) + v2.(y) * v3.(y))) * (v1.(x) - v1.(y)) = 0).
  { rewrite H0. lia. }
  assert ((v1.(x) * v3.(x) + v1.(y) * v3.(y)) * v2.(y) = 0).
  { nia. }
  assert ((v1.(x) * v3.(x) + v1.(y) * v3.(y)) * v2.(x) = 0).
  { nia. }
  assert ((v1.(x) * v3.(x) + v1.(y) * v3.(y)) * v2.(y) * v2.(y) = 0).
  { rewrite H6. lia. }
  assert ((v1.(x) * v3.(x) + v1.(y) * v3.(y)) * v2.(x) * v2.(x) = 0).
  { rewrite H7. lia. }
  nia.
Qed.

(** Exercise end *)
