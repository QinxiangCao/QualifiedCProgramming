Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import MonotonicList int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.sort_point Require Import sort_point_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_lib.
Local Open Scope sac.


(** Range wrappers are used only as compatibility facts inside proofs; the C
    interface exposes the individual Forall and scalar range conditions. *)
Ltac point_pose T tac :=
  match goal with
  | _ : T |- _ => fail 1
  | _ => let HH := fresh "Hpoint" in assert T as HH by tac
  end.
Ltac point_prepare :=
  repeat first
  [ multimatch goal with
    | H1 : Forall (Z.le (-10000)) (map point_x ?pts),
      H2 : Forall (Z.ge 10000) (map point_x ?pts),
      H3 : Forall (Z.le (-10000)) (map point_y ?pts),
      H4 : Forall (Z.ge 10000) (map point_y ?pts) |- _ =>
      point_pose (PointCoordsBound pts)
        ltac:(apply (proj2 (PointCoordsBound_fields pts)); auto)
    end
  | multimatch goal with
    | H : PointCoordsBound (?p :: ?pts) |- _ =>
      point_pose (PointCoordsBound pts)
        ltac:(exact (proj2 (PointCoordsBound_cons_parts p pts H)))
    end
  | multimatch goal with
    | H : PointCoordsBound (?p :: ?pts) |- _ =>
      point_pose (CoordInBounds (point_x p) /\ CoordInBounds (point_y p))
        ltac:(exact (proj1 (PointCoordsBound_cons_parts p pts H)))
    end
  | multimatch goal with
    | H : PointRangeSortResult ?gp ?flat ?out ?lo ?hi,
      HF : FlatPoints ?flat ?before |- _ =>
      point_pose (PointPermutation before out) ltac:(exact (proj1 (H before HF)))
    end
  | multimatch goal with
    | HP : PointPermutation ?before ?after, HB : PointCoordsBound ?before |- _ =>
      point_pose (PointCoordsBound after)
        ltac:(eapply PointCoordsBound_permutation; [exact HP | exact HB])
    end
  | multimatch goal with
    | HP : PointPermutation ?before ?after, HB : PointCoordsBound (?gp :: ?before) |- _ =>
      point_pose (PointCoordsBound (gp :: after))
        ltac:(eapply PointCoordsBound_permutation; [apply perm_skip; exact HP | exact HB])
    end
  | multimatch goal with
    | HP : PointPermutation ?before ?after |- _ =>
      point_pose (Zlength before = Zlength after)
        ltac:(rewrite !Zlength_correct; rewrite (Permutation_length HP); reflexivity)
    end
  | multimatch goal with
    | HE : mk_point ?x ?y = Znth ?index ?pts default_point,
      HB : PointCoordsBound ?pts |- _ =>
      point_pose (CoordInBounds x /\ CoordInBounds y)
        ltac:(pose proof (point_coords_bound_lookup pts index ltac:(lia) HB) as HH;
              rewrite <- HE in HH; exact HH)
    end
  | multimatch goal with
    | HF : FlatPoints ?flat ?pts |- _ =>
      point_pose (Zlength flat = 2 * Zlength pts) ltac:(exact (proj1 HF))
    end
  | multimatch goal with
    | HF : FlatPoints ?flat ?pts, HB : PointCoordsBound ?pts |- _ =>
      point_pose (Forall (Z.le (-10000)) flat)
        ltac:(exact (proj1 (proj1 (PointCoordsBound_flat flat pts HF) HB)))
    end
  | multimatch goal with
    | HF : FlatPoints ?flat ?pts, HB : PointCoordsBound ?pts |- _ =>
      point_pose (Forall (Z.ge 10000) flat)
        ltac:(exact (proj2 (proj1 (PointCoordsBound_flat flat pts HF) HB)))
    end
  | multimatch goal with
    | HF : FlatPoints ?flat ?pts,
      HL : Forall (Z.le (-10000)) ?flat,
      HU : Forall (Z.ge 10000) ?flat |- _ =>
      point_pose (PointCoordsBound pts)
        ltac:(apply (proj2 (PointCoordsBound_flat flat pts HF)); auto)
    end
  | multimatch goal with
    | HB : PointCoordsBound ?pts |- _ =>
      point_pose (Forall (Z.le (-10000)) (map point_x pts))
        ltac:(exact (proj1 (proj1 (PointCoordsBound_fields pts) HB)))
    end
  | multimatch goal with
    | HB : PointCoordsBound ?pts |- _ =>
      point_pose (Forall (Z.ge 10000) (map point_x pts))
        ltac:(exact (proj1 (proj2 (proj1 (PointCoordsBound_fields pts) HB))))
    end
  | multimatch goal with
    | HB : PointCoordsBound ?pts |- _ =>
      point_pose (Forall (Z.le (-10000)) (map point_y pts))
        ltac:(exact (proj1 (proj2 (proj2 (proj1 (PointCoordsBound_fields pts) HB)))))
    end
  | multimatch goal with
    | HB : PointCoordsBound ?pts |- _ =>
      point_pose (Forall (Z.ge 10000) (map point_y pts))
        ltac:(exact (proj2 (proj2 (proj2 (proj1 (PointCoordsBound_fields pts) HB)))))
    end
  | multimatch goal with
    | H : PolarCmpResult ?gp ?a ?b ?ret |- _ =>
      point_pose (-1 <= ret <= 1) ltac:(eapply PolarCmpResult_range; exact H)
    end
  ].
Ltac point_ranges :=
  try dump_pre_spatial;
  point_prepare;
  first [assumption | idtac];
  try match goal with
  | |- PointMemoryModel (mk_point ?gx ?gy) ?flat ?n =>
      eapply PointFlatModel_safe_legacy; [eassumption | lia | lia | lia | eassumption | eassumption]
  | HF : FlatPoints ?flat ?pts |- PointFlatModel ?flat =>
      exists pts; exact HF
  | |- CoordInBounds _ => unfold CoordInBounds
  end;
  repeat match goal with
  | H : CoordInBounds _ |- _ => unfold CoordInBounds in H
  | H : CoordInBounds _ /\ CoordInBounds _ |- _ => unfold CoordInBounds in H; destruct H
  end;
  repeat match goal with
  | H : @Forall Z ?P ?l |- _ => rewrite (Forall_Znth P 0 l) in H
  end;
  repeat match goal with
  | H : forall index : Z, _ -> ?P (Znth index ?l 0) |- context [Znth ?index ?l 0] =>
      let T := constr:(P (Znth index l 0)) in
      point_pose T ltac:(apply H; lia)
  end;
  cbn [point_x point_y mk_point] in *; try lia; try tauto.
Ltac point_scan_goal :=
  match goal with
  | |- PointPartitionScanInv ?gp ?before ?cur ?lo ?hi ?pivot ?i ?j =>
      apply (proj2 (PointPartitionScanInv_index gp before cur lo hi pivot i j
        ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(try rewrite Zlength_point_swap_points; lia)))
  end.

Lemma proof_of_cmp_polar_values_return_wit_1 : cmp_polar_values_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y; simpl.
      assert (Heqy : a_y_pre = b_y_pre) by lia.
      assert (Heqx : a_x_pre = b_x_pre) by lia.
      subst b_y_pre b_x_pre.
      repeat right.
      repeat split; try reflexivity; try ring.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_2 : cmp_polar_values_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y; simpl.
      assert (Heqy : a_y_pre = b_y_pre) by lia.
      assert (Heqx : a_x_pre = b_x_pre) by lia.
      subst b_y_pre b_x_pre.
      repeat right.
      repeat split; try reflexivity; try ring.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_3 : cmp_polar_values_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y; simpl.
      assert (Heqy : a_y_pre = b_y_pre) by lia.
      assert (Heqx : a_x_pre = b_x_pre) by lia.
      subst b_y_pre b_x_pre.
      repeat right.
      repeat split; try reflexivity; try ring.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_4 : cmp_polar_values_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y; simpl.
      assert (Heqy : a_y_pre = b_y_pre) by lia.
      assert (Heqx : a_x_pre = b_x_pre) by lia.
      subst b_y_pre b_x_pre.
      repeat right.
      repeat split; try reflexivity; try ring.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_5 : cmp_polar_values_return_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      do 9 right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
      * unfold point_dist2. cbn. nia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_6 : cmp_polar_values_return_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      do 9 right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_true_of_zero_y_nonneg_x gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
      * unfold point_dist2. cbn. nia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_7_split_goal_1 : cmp_polar_values_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.


  split_pures; try dump_pre_spatial; try lia; try nia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_7 : cmp_polar_values_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmp_polar_values_return_wit_7_split_goal_1.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_8 : cmp_polar_values_return_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      do 8 right; left.
      cbn.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
      * unfold point_dist2. cbn. nia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_9 : cmp_polar_values_return_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pures; try dump_pre_spatial; auto; try lia; try nia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_10 : cmp_polar_values_return_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      do 8 right; left.
      cbn.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
      * unfold point_dist2. cbn. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_11 : cmp_polar_values_return_wit_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_12 : cmp_polar_values_return_wit_12.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_13 : cmp_polar_values_return_wit_13.
Proof.
  (LLM_pre_process ltac:(int_auto));
     try
       (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
        simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_14 : cmp_polar_values_return_wit_14.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_15 : cmp_polar_values_return_wit_15.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_16 : cmp_polar_values_return_wit_16.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_17 : cmp_polar_values_return_wit_17.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_18 : cmp_polar_values_return_wit_18.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_19 : cmp_polar_values_return_wit_19.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_20 : cmp_polar_values_return_wit_20.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_21 : cmp_polar_values_return_wit_21.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_22 : cmp_polar_values_return_wit_22.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_23 : cmp_polar_values_return_wit_23.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_24 : cmp_polar_values_return_wit_24.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_25 : cmp_polar_values_return_wit_25.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_26 : cmp_polar_values_return_wit_26.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_27 : cmp_polar_values_return_wit_27.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_28 : cmp_polar_values_return_wit_28.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *;
       split_pure_spatial;
       [ cancel
       | split_pures; try dump_pre_spatial; auto; try lia; try nia ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_29 : cmp_polar_values_return_wit_29.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try (
      split_pure_spatial;
      [ cancel
      | repeat split_pures; try solve [dump_pre_spatial; lia];
        dump_pre_spatial;
        unfold PolarCmpResult;
      first
        [ do 2 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_30 : cmp_polar_values_return_wit_30.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try (
      split_pure_spatial;
      [ cancel
      | repeat split_pures; try solve [dump_pre_spatial; lia];
        dump_pre_spatial;
        unfold PolarCmpResult;
      first
        [ do 2 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_31 : cmp_polar_values_return_wit_31.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try (
      split_pure_spatial;
      [ cancel
      | repeat split_pures; try solve [dump_pre_spatial; lia];
        dump_pre_spatial;
        unfold PolarCmpResult;
      first
        [ do 2 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_32 : cmp_polar_values_return_wit_32.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try (
      split_pure_spatial;
      [ cancel
      | repeat split_pures; try solve [dump_pre_spatial; lia];
        dump_pre_spatial;
        unfold PolarCmpResult;
      first
        [ do 2 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_33 : cmp_polar_values_return_wit_33.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try (
      split_pure_spatial;
      [ cancel
      | repeat split_pures; try solve [dump_pre_spatial; lia];
        dump_pre_spatial;
        unfold PolarCmpResult;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_34 : cmp_polar_values_return_wit_34.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try (
      split_pure_spatial;
      [ cancel
      | repeat split_pures; try solve [dump_pre_spatial; lia];
        dump_pre_spatial;
        unfold PolarCmpResult;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_35 : cmp_polar_values_return_wit_35.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try (
      split_pure_spatial;
      [ cancel
      | repeat split_pures; try solve [dump_pre_spatial; lia];
        dump_pre_spatial;
        unfold PolarCmpResult;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_36 : cmp_polar_values_return_wit_36.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try (
      split_pure_spatial;
      [ cancel
      | repeat split_pures; try solve [dump_pre_spatial; lia];
        dump_pre_spatial;
        unfold PolarCmpResult;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_37 : cmp_polar_values_return_wit_37.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try (
      split_pure_spatial;
      [ cancel
      | repeat split_pures; try solve [dump_pre_spatial; lia];
        dump_pre_spatial;
        unfold PolarCmpResult;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_38 : cmp_polar_values_return_wit_38.
Proof.
  (LLM_pre_process ltac:(int_auto));
    try (
      split_pure_spatial;
      [ cancel
      | repeat split_pures; try solve [dump_pre_spatial; lia];
        dump_pre_spatial;
        unfold PolarCmpResult;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_39 : cmp_polar_values_return_wit_39.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      do 2 right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_40 : cmp_polar_values_return_wit_40.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      do 2 right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_zero_y_nonneg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_41 : cmp_polar_values_return_wit_41.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      do 2 right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_zero_y_neg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_42 : cmp_polar_values_return_wit_42.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      do 2 right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_43 : cmp_polar_values_return_wit_43.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_zero_y_neg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_44 : cmp_polar_values_return_wit_44.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_45 : cmp_polar_values_return_wit_45.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_zero_y_neg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_true_of_zero_y_nonneg_x gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_46 : cmp_polar_values_return_wit_46.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_true_of_zero_y_nonneg_x gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_47 : cmp_polar_values_return_wit_47.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_false_of_zero_y_neg_x gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_48 : cmp_polar_values_return_wit_48.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_zero_y_nonneg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_false_of_zero_y_neg_x gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_49 : cmp_polar_values_return_wit_49.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_50 : cmp_polar_values_return_wit_50.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.

  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_zero_y_nonneg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
Qed.

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.
  assert (OldPreH9 : (PointCoordsBound pts_l )) by point_ranges.

  pose proof PreH8 as Hflat.
  destruct PreH8 as [Hflat_len _].
  replace
    (replace_Znth (2 * j_pre + 1) (Znth (2 * i_pre + 1) flat 0)
      (replace_Znth (2 * j_pre) (Znth (2 * i_pre) flat 0)
        (replace_Znth (2 * i_pre + 1)
          (Znth (2 * j_pre + 1)
            (replace_Znth (2 * i_pre) (Znth (2 * j_pre) flat 0) flat) 0)
          (replace_Znth (2 * i_pre) (Znth (2 * j_pre) flat 0) flat))))
    with (point_swap_flat flat i_pre j_pre).
  2:{
    symmetry.
    apply point_swap_flat_preprocess_form with (n := n_pre); try lia.
  }
  split_pure_spatial.
  - cancel.
  - split_pures; try dump_pre_spatial.
    + apply FlatPoints_swap_points.
      * exact Hflat.
      * lia.
      * lia.
    + apply PointPermutation_swap_points_any; lia.
Qed.

Lemma proof_of_partition_points_entail_wit_1 : partition_points_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.
  assert (OldPreH8 : (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) )) by point_ranges.

  assert (Hhigh : 0 <= high_pre < Zlength pts_l).
  { rewrite PreH6. lia. }
  assert (Hpts_bound : PointCoordsBound pts_l).
  { unfold PointCoordsBound in OldPreH8 |- *.
    inversion OldPreH8; subst.
    assumption.
  }
  pose proof (flat_points_lookup_point flat pts_l high_pre Hhigh PreH7) as Hpivot.
  Exists flat. Exists pts_l.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    all: try solve [point_ranges].
    + dump_pre_spatial.
      point_scan_goal; unfold PointPartitionScanIndexed.
      rewrite PointSameOutsideRange_unfold.
      repeat split.
      * apply Permutation_refl.
      * symmetry. exact Hpivot.
      * intros k Hk. exfalso. lia.
      * intros k Hk. exfalso. lia.
Qed.

Lemma proof_of_partition_points_entail_wit_2_1 : partition_points_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.
  assert (OldPreH22 : (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur_2)) )) by point_ranges.
  assert (OldPreH3 : (PointCoordsBound (point_swap_points (pts_cur_2) ((i + 1 )) (j)) )) by point_ranges.
  assert (IndexedPreH23 : (PointPartitionScanIndexed (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j )) by
    (apply (proj1 (PointPartitionScanInv_index (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))); exact PreH26).

  assert (Hjrange : 0 <= j < Zlength pts_cur_2) by (rewrite PreH15; lia).
  assert (Hi1 : 0 <= i + 1 < Zlength pts_cur_2) by (rewrite PreH15; lia).
  assert (Hhighrange : 0 <= high_pre < Zlength pts_cur_2) by (rewrite PreH15; lia).
  assert (
    Hjpt :
      Znth j pts_cur_2 default_point =
      mk_point (Znth (2 * j) flat_cur_2 0) (Znth (2 * j + 1) flat_cur_2 0)
  ) by (apply FlatPoints_Znth_point; auto).
  assert (
    Hjle_cur :
      PolarLe
        (mk_point gx_pre gy_pre)
        (Znth j pts_cur_2 default_point)
        (mk_point pivot_x pivot_y)
  ).
  {
    pose proof (PolarCmpResult_nonpos_le _ _ _ _ PreH4 PreH3) as Hle.
    rewrite <- Hjpt in Hle.
    exact Hle.
  }
  assert (Hgxy : CoordInBounds gx_pre /\ CoordInBounds gy_pre).
  {
    inversion OldPreH22; subst; auto.
  }
  destruct IndexedPreH23 as [Hperm [Hsame [Hpivot [Hleft Hmid]]]].
  rewrite PointSameOutsideRange_unfold in Hsame.
  destruct Hsame as [Hsame_len Hsame].
  assert (Hpivot_after : mk_point pivot_x pivot_y =
    Znth high_pre (point_swap_points pts_cur_2 (i + 1) j) default_point).
  { rewrite Znth_point_swap_points_other; try assumption; lia. }
  Exists (point_swap_flat flat_cur_2 (i + 1) j).
  Exists (point_swap_points pts_cur_2 (i + 1) j).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: try solve [point_ranges].
    dump_pre_spatial.
    point_scan_goal; unfold PointPartitionScanIndexed.
    rewrite PointSameOutsideRange_unfold.
      repeat split.
      * eapply Permutation_trans.
        -- exact Hperm.
        -- exact PreH2.
      * rewrite Zlength_point_swap_points.
        lia.
      * intros k Hk Hout.
        replace (Znth k (point_swap_points pts_cur_2 (i + 1) j) default_point)
          with (Znth k pts_cur_2 default_point).
        -- apply Hsame; auto.
        -- symmetry.
           apply Znth_point_swap_points_other.
           ++ exact Hi1.
           ++ exact Hjrange.
           ++ rewrite Hsame_len in Hk.
              exact Hk.
           ++ destruct Hout as [Hlt | Hgt]; lia.
           ++ destruct Hout as [Hlt | Hgt]; lia.
      * replace (Znth high_pre (point_swap_points pts_cur_2 (i + 1) j) default_point)
          with (Znth high_pre pts_cur_2 default_point).
        -- exact Hpivot.
        -- symmetry.
           apply Znth_point_swap_points_other.
           ++ exact Hi1.
           ++ exact Hjrange.
           ++ exact Hhighrange.
           ++ lia.
           ++ lia.
      * intros k Hk.
        destruct (Z.eq_dec k (i + 1)) as [-> | Hneq].
        -- rewrite Znth_point_swap_points_left.
           ++ exact Hjle_cur.
           ++ exact Hi1.
           ++ exact Hjrange.
        -- replace (Znth k (point_swap_points pts_cur_2 (i + 1) j) default_point)
             with (Znth k pts_cur_2 default_point).
           ++ apply Hleft.
              lia.
           ++ symmetry.
              apply Znth_point_swap_points_other.
              ** exact Hi1.
              ** exact Hjrange.
               ** rewrite PreH15.
                 lia.
              ** exact Hneq.
              ** lia.
      * intros k Hk.
        destruct (Z.eq_dec k j) as [-> | Hneq].
        -- rewrite Znth_point_swap_points_right.
           ++ apply Hmid.
              lia.
           ++ exact Hi1.
           ++ exact Hjrange.
        -- replace (Znth k (point_swap_points pts_cur_2 (i + 1) j) default_point)
             with (Znth k pts_cur_2 default_point).
           ++ apply Hmid.
              lia.
           ++ symmetry.
              apply Znth_point_swap_points_other.
              ** exact Hi1.
              ** exact Hjrange.
               ** rewrite PreH15.
                 lia.
              ** lia.
              ** exact Hneq.
Qed.

Lemma proof_of_partition_points_entail_wit_2_2 : partition_points_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.
  assert (IndexedPreH20 : (PointPartitionScanIndexed (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j )) by
    (apply (proj1 (PointPartitionScanInv_index (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))); exact PreH24).
  assert (OldPreH18 : (PointCoordsBound pts_cur_2 )) by point_ranges.
  assert (OldPreH19 : (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur_2)) )) by point_ranges.

  assert (Hret1 : retval = 1) by lia.
  assert (Hjrange : 0 <= j < Zlength pts_cur_2) by (rewrite PreH13; lia).
  assert (
    Hjpt :
      Znth j pts_cur_2 default_point =
      mk_point (Znth (2 * j) flat_cur_2 0) (Znth (2 * j + 1) flat_cur_2 0)
  ) by (apply FlatPoints_Znth_point; auto).
  assert (
    Hjgt :
      PolarLt
        (mk_point gx_pre gy_pre)
        (mk_point pivot_x pivot_y)
        (Znth j pts_cur_2 default_point)
  ).
  {
    rewrite Hret1 in PreH2.
    pose proof (PolarCmpResult_one_implies_PolarLt_flip _ _ _ PreH2) as Hlt.
    rewrite <- Hjpt in Hlt.
    exact Hlt.
  }
  destruct IndexedPreH20 as [Hperm [Hsame [Hpivot [Hleft Hmid]]]].
  rewrite PointSameOutsideRange_unfold in Hsame.
  destruct Hsame as [Hsame_len Hsame_out].
  Exists flat_cur_2.
  Exists pts_cur_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: try solve [point_ranges].
    dump_pre_spatial.
    point_scan_goal; unfold PointPartitionScanIndexed.
    rewrite PointSameOutsideRange_unfold.
      repeat split.
      * exact Hperm.
      * exact Hsame_len.
      * exact Hsame_out.
      * exact Hpivot.
      * exact Hleft.
      * intros k Hk.
        destruct (Z.eq_dec k j) as [-> | Hneq].
        -- exact Hjgt.
        -- apply Hmid.
           lia.
Qed.

Lemma proof_of_partition_points_return_wit_1 : partition_points_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.
  assert (OldPreH3 : (PointCoordsBound (point_swap_points (pts_cur) ((i + 1 )) (high_pre)) )) by point_ranges.
  assert (IndexedPreH19 : (PointPartitionScanIndexed (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j )) by
    (apply (proj1 (PointPartitionScanInv_index (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))); exact PreH24).

  assert (Hj : j = high_pre) by lia.
  subst j.
  assert (Hgpbound : CoordInBounds gx_pre /\ CoordInBounds gy_pre).
  {
    match goal with
    | Hbound : PointCoordsBound (cons (mk_point gx_pre gy_pre) pts_cur) |- _ =>
        inversion Hbound; subst; assumption
    end.
  }
  Exists (point_swap_flat flat_cur (i + 1) high_pre).
  Exists (point_swap_points pts_cur (i + 1) high_pre).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; try solve [dump_pre_spatial; lia].
    + dump_pre_spatial.
      exact PreH1.
    + dump_pre_spatial.
      pose proof IndexedPreH19 as Hscan.
      destruct Hscan as [Hperm_scan _].
      eapply Permutation_trans.
      * exact Hperm_scan.
      * exact PreH2.
    + dump_pre_spatial.
      pose proof IndexedPreH19 as Hscan.
      destruct Hscan as [_ [Hsame _]].
      eapply PointSameOutsideRange_trans.
      * exact Hsame.
      * apply PointSameOutsideRange_swap_inside; lia.
    + dump_pre_spatial.
      eapply PointPartitionedAt_after_final_swap; eauto; lia.
Qed.

Lemma proof_of_partition_points_partial_solve_wit_5_pure : partition_points_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: repeat split_pures; point_ranges.
Qed.

Lemma proof_of_quicksort_points_range_entail_wit_1 : quicksort_points_range_entail_wit_1.
Proof.
  intros.
  LLM_pre_process ltac:(int_auto).
  point_prepare.
  assert (OldPreH7 : (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre )) by point_ranges.

  unfold PointMemoryModel in OldPreH7.
  destruct OldPreH7 as [pts_l [Hlen [Hflat Hbound]]].
  Exists pts_l.
  split_pure_spatial.
  - cancel.
  - split_pures; point_ranges.
Qed.

Lemma proof_of_quicksort_points_range_return_wit_1 : quicksort_points_range_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.
  assert (OldPreH2 : (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_4)) )) by point_ranges.

  prop_apply (IntArray.full_length coords_pre (2 * n_pre) flat_out_4).
  Intros.
  Exists flat_out_4.
  Exists pts_out_4.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + { dump_pre_spatial.
        match goal with
    | Hflat4 : FlatPoints flat_out_4 pts_out_4 |- _ =>
        destruct Hflat4 as [Hlenflat4 _]
    end.
    assert (Hlen2 : Zlength pts_out_2 = n_pre).
    {
      rewrite <- PreH26.
      repeat rewrite Zlength_correct.
      rewrite <- (Permutation_length PreH10).
      reflexivity.
    }
    assert (Hlen4 : Zlength pts_out_4 = n_pre).
    {
      match goal with
      | Hlen_full : Z.of_nat (Datatypes.length flat_out_4) = 2 * n_pre |- _ =>
          rewrite <- Zlength_correct in Hlen_full;
          rewrite Hlenflat4 in Hlen_full;
          lia
      end.
    }
    unfold PointRangeSortResult.
    intros pts_in Hflat_in.
    assert (pts_in = pts_l) by (eapply FlatPoints_functional; eauto).
    subst pts_in.
    specialize (PreH5 pts_out_2 PreH9).
    destruct PreH5 as [Hperm23 [Hsame23 Hsorted23]].
    specialize (PreH2 pts_out_3 PreH4).
    destruct PreH2 as [Hperm34 [Hsame34 Hsorted34]].
    assert (Hlen3 : Zlength pts_out_3 = n_pre).
    {
      rewrite <- Hlen2.
      repeat rewrite Zlength_correct.
      rewrite <- (Permutation_length Hperm23).
      reflexivity.
    }
    split.
    + eapply Permutation_trans.
      * exact PreH10.
      * eapply Permutation_trans; [exact Hperm23 | exact Hperm34].
    + split.
      * assert (Hsame23_full : PointSameOutsideRange pts_out_2 pts_out_3 left_pre right_pre).
        {
          eapply (PointSameOutsideRange_weaken
                    pts_out_2 pts_out_3 left_pre (retval - 1) left_pre right_pre).
          - lia.
          - lia.
          - exact Hsame23.
        }
        assert (Hsame34_full : PointSameOutsideRange pts_out_3 pts_out_4 left_pre right_pre).
        {
          eapply (PointSameOutsideRange_weaken
                    pts_out_3 pts_out_4 (retval + 1) right_pre left_pre right_pre).
          - lia.
          - lia.
          - exact Hsame34.
        }
        eapply PointSameOutsideRange_trans.
        -- eapply PointSameOutsideRange_trans; [exact PreH11 | exact Hsame23_full].
        -- exact Hsame34_full.
      * assert (Hpart3 : PointPartitionedAt (mk_point gx_pre gy_pre) pts_out_3 left_pre right_pre retval).
        {
          eapply PointPartitionedAt_preserved_by_left.
          - exact Hperm23.
          - lia.
          - exact Hsame23.
          - rewrite Hlen2. lia.
          - exact PreH12.
        }
        assert (Hpart4 : PointPartitionedAt (mk_point gx_pre gy_pre) pts_out_4 left_pre right_pre retval).
        {
          eapply PointPartitionedAt_preserved_by_right.
          - exact Hperm34.
          - lia.
          - exact Hsame34.
          - rewrite Hlen3. lia.
          - exact Hpart3.
        }
        assert (Hsorted_left4 :
          PointSortedRange (mk_point gx_pre gy_pre) pts_out_4 left_pre (retval - 1)).
        {
          eapply PointSortedRange_ext with (l := pts_out_3).
          - lia.
          - rewrite Hlen3. lia.
          - rewrite Hlen3, Hlen4. reflexivity.
          - intros k Hk.
            rewrite PointSameOutsideRange_unfold in Hsame34.
            destruct Hsame34 as [_ Heq34].
            apply Heq34.
            + rewrite Hlen3. lia.
            + left. lia.
          - exact Hsorted23.
        }
        eapply PointSortedRange_from_middle_partition with (p := retval).
        -- lia.
        -- lia.
        -- lia.
        -- rewrite Hlen4. lia.
        -- exact Hpart4.
        -- exact Hsorted_left4.
        -- exact Hsorted34. }
Qed.

Lemma proof_of_quicksort_points_range_return_wit_2 : quicksort_points_range_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.
  assert (OldPreH2 : (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_3)) )) by point_ranges.

  prop_apply (IntArray.full_length coords_pre (2 * n_pre) flat_out_3).
  Intros.
  assert (Hretval : retval = left_pre) by lia.
  subst retval.
  Exists flat_out_3.
  Exists pts_out_3.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + { dump_pre_spatial.
        match goal with
    | Hflat3 : FlatPoints flat_out_3 pts_out_3 |- _ =>
        destruct Hflat3 as [Hlenflat3 _]
    end.
    assert (Hlen3 : Zlength pts_out_3 = n_pre).
    {
      match goal with
      | Hflat_len : Z.of_nat (Datatypes.length flat_out_3) = 2 * n_pre |- _ =>
          rewrite <- Zlength_correct in Hflat_len;
          rewrite Hlenflat3 in Hflat_len; lia
      end.
    }
    assert (Hlen2 : Zlength pts_out_2 = n_pre).
    {
      assert (Hperm_len := Permutation_length PreH8).
      assert (Hperm_zlen : Zlength pts_l = Zlength pts_out_2).
      { repeat rewrite Zlength_correct. rewrite Hperm_len. reflexivity. }
      lia.
    }
    unfold PointRangeSortResult.
    intros pts_in Hflat_in.
    assert (pts_in = pts_l) by (eapply FlatPoints_functional; eauto).
    subst pts_in.
    specialize (PreH2 pts_out_2 PreH7).
    destruct PreH2 as [Hperm23 [Hsame23 Hsorted23]].
    split.
    + eapply Permutation_trans; [exact PreH8 | exact Hperm23].
    + split.
      * assert (Hsame23_full : PointSameOutsideRange pts_out_2 pts_out_3 left_pre right_pre).
        {
          eapply (PointSameOutsideRange_weaken
                    pts_out_2 pts_out_3 (left_pre + 1) right_pre left_pre right_pre).
          - lia.
          - lia.
          - exact Hsame23.
        }
        eapply PointSameOutsideRange_trans; [exact PreH9 | exact Hsame23_full].
      * assert (Hpart3 : PointPartitionedAt (mk_point gx_pre gy_pre) pts_out_3 left_pre right_pre left_pre).
        {
          eapply PointPartitionedAt_preserved_by_right.
          - exact Hperm23.
          - lia.
          - exact Hsame23.
          - rewrite Hlen2. lia.
          - exact PreH10.
        }
        eapply PointSortedRange_from_right_boundary with (p := left_pre).
        -- lia.
        -- lia.
        -- rewrite Hlen3. lia.
        -- exact Hpart3.
        -- exact Hsorted23. }
Qed.

Lemma proof_of_quicksort_points_range_return_wit_3 : quicksort_points_range_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.
  assert (OldPreH3 : (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_3)) )) by point_ranges.

  prop_apply (IntArray.full_length coords_pre (2 * n_pre) flat_out_3).
  Intros.
  assert (Hretval : retval = right_pre) by lia.
  subst retval.
  Exists flat_out_3.
  Exists pts_out_3.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH2.
    + { dump_pre_spatial.
        match goal with
    | Hflat3 : FlatPoints flat_out_3 pts_out_3 |- _ =>
        destruct Hflat3 as [Hlenflat3 _]
    end.
    assert (Hlen3 : Zlength pts_out_3 = n_pre).
    {
      match goal with
      | Hlen_full : Z.of_nat (Datatypes.length flat_out_3) = 2 * n_pre |- _ =>
          rewrite <- Zlength_correct in Hlen_full;
          rewrite Hlenflat3 in Hlen_full;
          lia
      end.
    }
    assert (Hlen2 : Zlength pts_out_2 = n_pre).
    {
      rewrite <- PreH24.
      repeat rewrite Zlength_correct.
      rewrite (Permutation_length PreH8).
      reflexivity.
    }
    unfold PointRangeSortResult.
    intros pts_in Hflat_in.
    assert (pts_in = pts_l) by (eapply FlatPoints_functional; eauto).
    subst pts_in.
    specialize (PreH3 pts_out_2 PreH7).
    destruct PreH3 as [Hperm23 [Hsame23 Hsorted23]].
    split.
    + eapply Permutation_trans; [exact PreH8 | exact Hperm23].
    + split.
      * assert (Hsame23_full : PointSameOutsideRange pts_out_2 pts_out_3 left_pre right_pre).
        {
          eapply (PointSameOutsideRange_weaken
                    pts_out_2 pts_out_3 left_pre (right_pre - 1) left_pre right_pre).
          - lia.
          - lia.
          - exact Hsame23.
        }
        eapply PointSameOutsideRange_trans; [exact PreH9 | exact Hsame23_full].
      * assert (Hpart3 : PointPartitionedAt (mk_point gx_pre gy_pre) pts_out_3 left_pre right_pre right_pre).
        {
          eapply PointPartitionedAt_preserved_by_left.
          - exact Hperm23.
          - lia.
          - exact Hsame23.
          - rewrite Hlen2. lia.
          - exact PreH10.
        }
        eapply PointSortedRange_from_left_boundary with (p := right_pre).
        -- lia.
        -- lia.
        -- rewrite Hlen3. lia.
        -- exact Hpart3.
        -- exact Hsorted23. }
Qed.

Lemma proof_of_quicksort_points_range_return_wit_4 : quicksort_points_range_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.
  assert (OldPreH7 : (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre )) by point_ranges.

  assert (Hge : left_pre >= right_pre) by lia.
  destruct OldPreH7 as [pts_l [Hlen [Hflat_mem Hbound_mem]]].
  Exists flat. Exists pts_l.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + exact Hflat_mem.
    + unfold PointRangeSortResult.
      intros pts_in Hflat_in.
      assert (pts_in = pts_l) by (eapply FlatPoints_functional; eauto).
      subst pts_in.
      split.
      * apply Permutation_refl.
      * split.
        -- apply PointSameOutsideRange_refl.
        -- apply PointSortedRange_degenerate. exact Hge.
Qed.

Lemma proof_of_quicksort_points_range_partial_solve_wit_2_pure : quicksort_points_range_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: repeat split_pures; point_ranges.
Qed.

Lemma proof_of_quicksort_points_range_partial_solve_wit_3_pure : quicksort_points_range_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: repeat split_pures; point_ranges.
Qed.

Lemma proof_of_quicksort_points_range_partial_solve_wit_4_pure : quicksort_points_range_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: repeat split_pures; point_ranges.
Qed.

Lemma proof_of_sort_return_wit_1 : sort_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  point_prepare.
  assert (OldPreH2 : (PointCoordsBound (cons ((mk_point (gx) (gy))) (pts_out_2)) )) by point_ranges.

  Exists flat_out_2. Exists pts_out_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial.
      destruct (PreH2 pts_l PreH6) as [Hperm _].
      exact Hperm.
    + dump_pre_spatial.
      destruct (PreH2 pts_l PreH6) as [Hperm [_ Hsorted]].
      unfold PolarSorted.
      intros i j Hi Hij Hj.
      assert (HZlen : Zlength pts_out_2 = n_pre).
      {
        rewrite <- PreH5.
        rewrite !Zlength_correct.
        rewrite <- (Permutation_length Hperm).
        reflexivity.
      }
      eapply Hsorted; lia.
Qed.

Lemma proof_of_sort_partial_solve_wit_1_pure : sort_partial_solve_wit_1_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: repeat split_pures; point_ranges.
Qed.

