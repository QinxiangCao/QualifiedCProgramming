(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From SimpleC.EE.Applications_human.convex_hull Require Export Geo_Vec.
Local Open Scope Z.
Import ListNotations.
(* /COQ-HEAD *)

Record point: Type := {
  point_x: Z;
  point_y: Z;
}.

Module GeoNotations.

Notation "p '.(x)'" := (point_x p) (at level 1, only printing).
Notation "p '.(y)'" := (point_y p) (at level 1, only printing).
Notation "p '.(x)'" := (vec_x p) (at level 1, only printing).
Notation "p '.(y)'" := (vec_y p) (at level 1, only printing).

Ltac get_x p :=
  match type of p with
  | point => exact (point_x p)
  | vec => exact (vec_x p)
  end.

Ltac get_y p :=
  match type of p with
  | point => exact (point_y p)
  | vec => exact (vec_y p)
  end.

Notation "p '.(x)'" := (ltac:(get_x p)) (at level 1, only parsing).
Notation "p '.(y)'" := (ltac:(get_y p)) (at level 1, only parsing).

End GeoNotations.

Import GeoNotations.

Definition build_vec (p_from p_to: point): vec := {|
  vec_x := p_to.(x) - p_from.(x);
  vec_y := p_to.(y) - p_from.(y);
|}.

Lemma nonzero_sym: forall p q,
  nonzero (build_vec p q) ->
  nonzero (build_vec q p).
Proof. unfold nonzero, dot_prod, build_vec; simpl; nia. Qed.

Definition ccw (p q r: point): Prop :=
  left_than (build_vec p r) (build_vec p q).

Definition colinear (p q r: point): Prop :=
  parallel (build_vec p q) (build_vec p r).

Definition at_mid (p q r: point): Prop :=
  backward_or_perp (build_vec p q) (build_vec p r).

Lemma colinear_comm : forall p q r,
  colinear p q r <-> colinear p r q.
Proof.
  unfold colinear, parallel, cross_prod; simpl; nia.
Qed.

Lemma at_mid_comm : forall p q r,
  at_mid p q r <-> at_mid p r q.
Proof.
  unfold at_mid, backward_or_perp, dot_prod; simpl; nia.
Qed.

Ltac into_vec_prod :=
  unfold colinear, parallel in *;
  unfold at_mid, backward_or_perp in *;
  unfold ccw, left_than in *;
  unfold left_equal in *.

Definition g_ccw (p q r: point): Prop :=
  ccw p q r \/ (* ccw *)
  colinear p q r /\ at_mid q p r. (* or colinear p - q - r *)

Lemma ccw_dec : forall (p q r : point),
  {ccw p q r} + {~ ccw p q r}.
Proof.
  unfold ccw, left_than; intros.
  remember (cross_prod (build_vec p r) (build_vec p q)) as a.
  pose proof Ztrichotomy_inf a 0as [[H | H] | H];
  try (left; nia);
  try (right; nia).
Qed.

Definition prop_to_bool (P : Prop) (dec : {P} + {~P}) : bool :=
  if dec then true else false.

Definition ccw_b (p q r: point): bool :=
  prop_to_bool (ccw p q r) (ccw_dec p q r).

Lemma ccw_g_ccw: forall (p q r: point),
  ccw p q r -> g_ccw p q r.
Proof. unfold ccw, g_ccw. tauto. Qed.

Lemma ccw_cyclicity: forall (p q r: point),
  ccw p q r -> ccw q r p.
Proof. unfold ccw, left_than, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_cyclicity_2: forall (p q r: point),
  ccw p q r -> ccw r p q.
Proof. intros. do 2 apply ccw_cyclicity. tauto. Qed.

Lemma ccw_anti_symmetry: forall (p q r: point),
  ccw p q r -> ~ ccw p r q.
Proof. unfold ccw, left_than, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_non_degeneracy: forall (p q r: point),
  ~ colinear p q r -> ccw p q r \/ ccw p r q.
Proof. unfold ccw, colinear, left_than, parallel, cross_prod, build_vec; simpl; intros. nia. Qed.

Ltac elim_ccw_rep H :=
  unfold ccw, left_than, cross_prod, build_vec in H;
  simpl in H; nia.

Lemma colinear_perm132: forall (p q r: point),
  colinear p q r -> colinear p r q.
Proof. unfold colinear, parallel, cross_prod, build_vec; simpl. nia. Qed.

Lemma colinear_perm231: forall (p q r: point),
  colinear p q r -> colinear q r p.
Proof. unfold colinear, parallel, cross_prod, build_vec; simpl. nia. Qed.

Lemma colinear_perm213: forall (p q r: point),
  colinear p q r -> colinear q p r.
Proof. unfold colinear, parallel, cross_prod, build_vec; simpl. nia. Qed.

Lemma colinear_perm312: forall (p q r: point),
  colinear p q r -> colinear r p q.
Proof. unfold colinear, parallel, cross_prod, build_vec; simpl. nia. Qed.

Lemma colinear_perm321: forall (p q r: point),
  colinear p q r -> colinear r q p.
Proof. unfold colinear, parallel, cross_prod, build_vec; simpl. nia. Qed.

Lemma colinear_4p: forall (p q r s: point),
  colinear p q r ->
  colinear p q s ->
  nonzero (build_vec p q) ->
  colinear q r s.
Proof.
  intros.
  apply colinear_perm213 in H.
  apply colinear_perm231 in H0.
  unfold colinear in *.
  apply nonzero_sym in H1.
  pose proof parallel_trans _ _ _ H0 H H1.
  apply parallel_sym.
  tauto.
Qed.

Lemma at_mid_fwd1: forall (p q r: point),
  at_mid q p r ->
  forward_or_perp (build_vec p q) (build_vec p r).
Proof.
  intros.
  pose proof metric_nonneg (build_vec p q).
  unfold at_mid, backward_or_perp, forward_or_perp, dot_prod, build_vec in *.
  simpl in *.
  nia.
Qed.

Lemma at_mid_fwd2: forall (p q r: point),
  at_mid q p r ->
  forward_or_perp (build_vec r q) (build_vec r p).
Proof.
  intros.
  pose proof metric_nonneg (build_vec r q).
  unfold at_mid, backward_or_perp, forward_or_perp, dot_prod, build_vec in *.
  simpl in *.
  nia.
Qed.

Lemma ccw_interiority: forall (p q r t: point),
  ccw t q r -> ccw p t r -> ccw p q t -> ccw p q r.
Proof. unfold ccw, left_than, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_transitivity: forall (p q r s t: point),
  ccw t s p -> ccw t s q -> ccw t s r -> ccw t p q -> ccw t q r ->
  ccw t p r.
Proof. unfold ccw, left_than, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_dual_transitivity: forall (p q r s t: point),
  ccw s t p -> ccw s t q -> ccw s t r -> ccw t p q -> ccw t q r ->
  ccw t p r.
Proof. unfold ccw, left_than, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_skip_head_simple: forall (p q r s t: point),
  ccw p q s \/ colinear p q s ->
  ccw p r s ->
  ccw p s t ->
  ccw q r s ->
  ccw r s t ->
  ccw q s t.
Proof. unfold ccw, colinear, left_than, parallel, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma at_mid_nonzero1: forall p q r,
  at_mid q p r ->
  nonzero (build_vec p q) ->
  nonzero (build_vec p r).
Proof.
  intros.
  rewrite nonzero_iff in H0 |- *.
  pose proof metric_nonneg (build_vec q r).
  unfold at_mid, backward_or_perp, nonzero, dot_prod, build_vec in *.
  simpl in *.
  nia.
Qed.

Lemma at_mid_nonzero2: forall p q r,
  at_mid q p r ->
  nonzero (build_vec q r) ->
  nonzero (build_vec p r).
Proof.
  intros.
  rewrite nonzero_iff in H0 |- *.
  pose proof metric_nonneg (build_vec p q).
  unfold at_mid, backward_or_perp, nonzero, dot_prod, build_vec in *.
  simpl in *.
  nia.
Qed.

Lemma ccw_ccw_colinear_shorter_impossible: forall p q r s,
  ccw p q r -> ccw p r s ->
  colinear p q s ->
  at_mid q p s ->
  False.
Proof.
  intros.
  apply at_mid_fwd1 in H2.
  unfold colinear in H1.
  rewrite forward_or_perp_iff in H2.
  destruct H2.
  + unfold ccw in *.
    pose proof left_than_same_dir_r _ _ _ H1 H2 H.
    clear - H0 H3.
    unfold left_than, cross_prod in *.
    lia.
  + pose proof left_than_nonzero2 _ _ H.
    pose proof left_than_nonzero1 _ _ H0.
    pose proof perp_parallel _ _ H2 H1 ltac:(tauto) ltac:(tauto).
    tauto.
Qed.

Lemma ccw_colinear_shorter_impossible: forall p q r s,
  ccw p q r ->
  colinear p r s ->
  at_mid r p s ->
  ccw q r s ->
  False.
Proof.
  intros p q r s ? Hp_par Hmid ?.
  pose proof colinear_perm312 _ _ _ Hp_par as Hs_par.
  unfold ccw in H.
  pose proof left_than_nonzero1 _ _ H as Hnz_pr.
  pose proof at_mid_nonzero1 _ _ _ Hmid Hnz_pr as Hnz_ps.
  assert (nonzero (build_vec s p)) as Hnz_sp
    by (revert Hnz_ps; unfold nonzero, dot_prod, build_vec; simpl; nia).
  pose proof at_mid_fwd1 _ _ _ Hmid as Hp.
  rewrite forward_or_perp_iff in Hp.
  destruct Hp as [Hp | Hp].
  2: {
    pose proof perp_parallel _ _ Hp Hp_par ltac:(tauto) ltac:(tauto).
    tauto.
  }
  pose proof at_mid_fwd2 _ _ _ Hmid as Hs.
  apply forward_or_perp_symm in Hs.
  pose proof left_than_same_dir_l _ _ _ Hp_par Hp H.
  fold (ccw p q s) in H1.
  apply ccw_cyclicity_2 in H1.
  unfold ccw in H1.
  pose proof left_equal_same_dir_r' _ _ _ Hs_par Hs H1.
  clear - H0 H2.
  apply ccw_cyclicity_2 in H0.
  unfold ccw in H0.
  unfold left_than, left_equal, cross_prod in *.
  lia.
Qed.

Lemma ccw_skip_head: forall (p q r s t: point),
  g_ccw p q r -> g_ccw p q s -> g_ccw p q t ->
  g_ccw p r s -> g_ccw p r t -> g_ccw p s t ->
  ccw q r s -> ccw r s t -> ccw q s t.
Proof.
  unfold ccw, g_ccw.
  intros p q r s t Hqr Hqs Hqt Hrs Hrt Hst Hqrs Hrst.
  destruct Hrs as [Hrs | [Hrs0 Hrs]].
  + destruct Hst as [Hst | [Hst0 Hst]].
    - apply (ccw_skip_head_simple p q r s t); unfold ccw, colinear; tauto.
    - pose proof ccw_colinear_shorter_impossible _ _ _ _
                 Hrs Hst0 Hst Hrst.
      tauto.
  + destruct Hqr as [Hqr | [Hqr0 Hqr]].
    - pose proof ccw_colinear_shorter_impossible _ _ _ _
                 Hqr Hrs0 Hrs Hqrs.
      tauto.
    - pose proof left_than_nonzero2 _ _ Hqrs.
      pose proof at_mid_nonzero2 _ _ _ Hqr H.
      pose proof colinear_perm132 _ _ _ Hqr0.
      pose proof colinear_4p _ _ _ _ H1 Hrs0 H0.
      clear - H2 Hqrs.
      apply colinear_perm231 in H2.
      unfold colinear, left_than, parallel, cross_prod in *.
      lia.
Qed.

(* p q r
   p q s
   p q t
   p r t *)
Lemma ccw_skip_tail_simple: forall (p q r s t: point),
  ccw p q r \/ colinear p q r ->
  ccw p r s -> ccw p r t -> ccw p s t ->
  ccw q r s -> ccw r s t -> ccw q r t.
Proof. unfold ccw, colinear, left_than, parallel, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_skip_tail: forall (p q r s t: point),
  g_ccw p q r -> g_ccw p q s -> g_ccw p q t ->
  g_ccw p r s -> g_ccw p r t -> g_ccw p s t ->
  ccw q r s -> ccw r s t -> ccw q r t.
Proof.
  unfold ccw, g_ccw.
  intros p q r s t Hqr Hqs Hqt Hrs Hrt Hst Hqrs Hrst.
  destruct Hrs as [Hrs | [Hrs0 Hrs]].
  + destruct Hst as [Hst | [Hst0 Hst]].
    - destruct Hrt as [Hrt | [Hrt0 Hrt]].
      * apply (ccw_skip_tail_simple p q r s t); try tauto.
      * pose proof ccw_ccw_colinear_shorter_impossible p r s t.
        tauto.
    - pose proof ccw_colinear_shorter_impossible _ _ _ _
                 Hrs Hst0 Hst Hrst.
      tauto.
  + destruct Hqr as [Hqr | [Hqr0 Hqr]].
    - pose proof ccw_colinear_shorter_impossible _ _ _ _
                 Hqr Hrs0 Hrs Hqrs.
      tauto.
    - pose proof left_than_nonzero2 _ _ Hqrs.
      pose proof at_mid_nonzero2 _ _ _ Hqr H.
      pose proof colinear_perm132 _ _ _ Hqr0.
      pose proof colinear_4p _ _ _ _ H1 Hrs0 H0.
      clear - H2 Hqrs.
      apply colinear_perm231 in H2.
      unfold colinear, left_than, parallel, cross_prod in *.
      lia.
Qed.

Lemma ccw_trichotomy : forall (p q r : point),
  {ccw p q r} + {colinear p q r} + {ccw p r q}.
Proof.
  intros.
  destruct (ccw_dec p q r) as [H0 | H0].
  - left. left. assumption.
  - assert ({colinear p q r} + {~ colinear p q r}) as [Hcol | Hncol].
    { unfold colinear, parallel.
      remember (cross_prod (build_vec p q) (build_vec p r)) as a.
      pose proof Z_dec a 0 as [[Hlt | Heq] | Hgt];
      try (left; assumption);
      try (right; intros H'; nia). }
    + left. right. assumption.
    + right. pose proof (ccw_non_degeneracy p q r Hncol).
      destruct H; try contradiction; try assumption.
Qed.

(** Properties *)
(* all point in P are right to p->q *)
