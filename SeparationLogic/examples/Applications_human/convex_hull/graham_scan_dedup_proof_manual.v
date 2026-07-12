Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.convex_hull Require Import graham_scan_dedup_goal.
From SimpleC.EE.Applications_human.convex_hull Require Import graham_scan_dedup_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.convex_hull.convex_hull_lib.
Require Import SimpleC.EE.QCP_demos_LLM.sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.

Ltac open_generated_wit name :=
  unfold name; try left.

Lemma proof_of_leftdown_dedup_return_wit_1_split_goal_1 : leftdown_dedup_return_wit_1_split_goal_1.
Proof.
  unfold leftdown_dedup_return_wit_1_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_leftdown_dedup_return_wit_1 : leftdown_dedup_return_wit_1.
Proof.
  open_generated_wit leftdown_dedup_return_wit_1.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_dedup_return_wit_2_split_goal_1 : leftdown_dedup_return_wit_2_split_goal_1.
Proof.
  unfold leftdown_dedup_return_wit_2_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_leftdown_dedup_return_wit_2 : leftdown_dedup_return_wit_2.
Proof.
  open_generated_wit leftdown_dedup_return_wit_2.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_dedup_return_wit_3_split_goal_1 : leftdown_dedup_return_wit_3_split_goal_1.
Proof.
  unfold leftdown_dedup_return_wit_3_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_leftdown_dedup_return_wit_3 : leftdown_dedup_return_wit_3.
Proof.
  open_generated_wit leftdown_dedup_return_wit_3.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_dedup_return_wit_4_split_goal_1 : leftdown_dedup_return_wit_4_split_goal_1.
Proof.
  unfold leftdown_dedup_return_wit_4_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_leftdown_dedup_return_wit_4 : leftdown_dedup_return_wit_4.
Proof.
  open_generated_wit leftdown_dedup_return_wit_4.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_dedup_return_wit_5_split_goal_1 : leftdown_dedup_return_wit_5_split_goal_1.
Proof.
  unfold leftdown_dedup_return_wit_5_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_leftdown_dedup_return_wit_5 : leftdown_dedup_return_wit_5.
Proof.
  open_generated_wit leftdown_dedup_return_wit_5.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_cross_prod_safety_wit_1_split_goal_1 : cross_prod_safety_wit_1_split_goal_1.
Proof.
  unfold cross_prod_safety_wit_1_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_1_split_goal_2 : cross_prod_safety_wit_1_split_goal_2.
Proof.
  unfold cross_prod_safety_wit_1_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_1 : cross_prod_safety_wit_1.
Proof.
  open_generated_wit cross_prod_safety_wit_1.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  all: assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_2_split_goal_1 : cross_prod_safety_wit_2_split_goal_1.
Proof.
  unfold cross_prod_safety_wit_2_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_2_split_goal_2 : cross_prod_safety_wit_2_split_goal_2.
Proof.
  unfold cross_prod_safety_wit_2_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_2 : cross_prod_safety_wit_2.
Proof.
  open_generated_wit cross_prod_safety_wit_2.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_3_split_goal_1 : cross_prod_safety_wit_3_split_goal_1.
Proof.
  unfold cross_prod_safety_wit_3_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_3_split_goal_2 : cross_prod_safety_wit_3_split_goal_2.
Proof.
  unfold cross_prod_safety_wit_3_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_3 : cross_prod_safety_wit_3.
Proof.
  open_generated_wit cross_prod_safety_wit_3.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_4_split_goal_1 : cross_prod_safety_wit_4_split_goal_1.
Proof.
  unfold cross_prod_safety_wit_4_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_4_split_goal_2 : cross_prod_safety_wit_4_split_goal_2.
Proof.
  unfold cross_prod_safety_wit_4_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_4 : cross_prod_safety_wit_4.
Proof.
  open_generated_wit cross_prod_safety_wit_4.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_5_split_goal_1 : cross_prod_safety_wit_5_split_goal_1.
Proof.
  unfold cross_prod_safety_wit_5_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_5_split_goal_2 : cross_prod_safety_wit_5_split_goal_2.
Proof.
  unfold cross_prod_safety_wit_5_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_5 : cross_prod_safety_wit_5.
Proof.
  open_generated_wit cross_prod_safety_wit_5.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_6_split_goal_1 : cross_prod_safety_wit_6_split_goal_1.
Proof.
  unfold cross_prod_safety_wit_6_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_6_split_goal_2 : cross_prod_safety_wit_6_split_goal_2.
Proof.
  unfold cross_prod_safety_wit_6_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_6 : cross_prod_safety_wit_6.
Proof.
  open_generated_wit cross_prod_safety_wit_6.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_7_split_goal_1 : cross_prod_safety_wit_7_split_goal_1.
Proof.
  unfold cross_prod_safety_wit_7_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_7_split_goal_2 : cross_prod_safety_wit_7_split_goal_2.
Proof.
  unfold cross_prod_safety_wit_7_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_safety_wit_7 : cross_prod_safety_wit_7.
Proof.
  open_generated_wit cross_prod_safety_wit_7.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_cross_prod_return_wit_1_split_goal_1 : cross_prod_return_wit_1_split_goal_1.
Proof.
  unfold cross_prod_return_wit_1_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cross_prod_return_wit_1 : cross_prod_return_wit_1.
Proof.
  open_generated_wit cross_prod_return_wit_1.
  intros.
  entailer!.
Qed.

Lemma proof_of_dot_prod_safety_wit_1_split_goal_1 : dot_prod_safety_wit_1_split_goal_1.
Proof.
  unfold dot_prod_safety_wit_1_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_1_split_goal_2 : dot_prod_safety_wit_1_split_goal_2.
Proof.
  unfold dot_prod_safety_wit_1_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_1 : dot_prod_safety_wit_1.
Proof.
  open_generated_wit dot_prod_safety_wit_1.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  all: assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_2_split_goal_1 : dot_prod_safety_wit_2_split_goal_1.
Proof.
  unfold dot_prod_safety_wit_2_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_2_split_goal_2 : dot_prod_safety_wit_2_split_goal_2.
Proof.
  unfold dot_prod_safety_wit_2_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_2 : dot_prod_safety_wit_2.
Proof.
  open_generated_wit dot_prod_safety_wit_2.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_3_split_goal_1 : dot_prod_safety_wit_3_split_goal_1.
Proof.
  unfold dot_prod_safety_wit_3_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_3_split_goal_2 : dot_prod_safety_wit_3_split_goal_2.
Proof.
  unfold dot_prod_safety_wit_3_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_3 : dot_prod_safety_wit_3.
Proof.
  open_generated_wit dot_prod_safety_wit_3.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_4_split_goal_1 : dot_prod_safety_wit_4_split_goal_1.
Proof.
  unfold dot_prod_safety_wit_4_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_4_split_goal_2 : dot_prod_safety_wit_4_split_goal_2.
Proof.
  unfold dot_prod_safety_wit_4_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_4 : dot_prod_safety_wit_4.
Proof.
  open_generated_wit dot_prod_safety_wit_4.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_5_split_goal_1 : dot_prod_safety_wit_5_split_goal_1.
Proof.
  unfold dot_prod_safety_wit_5_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_5_split_goal_2 : dot_prod_safety_wit_5_split_goal_2.
Proof.
  unfold dot_prod_safety_wit_5_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_5 : dot_prod_safety_wit_5.
Proof.
  open_generated_wit dot_prod_safety_wit_5.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_6_split_goal_1 : dot_prod_safety_wit_6_split_goal_1.
Proof.
  unfold dot_prod_safety_wit_6_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_6_split_goal_2 : dot_prod_safety_wit_6_split_goal_2.
Proof.
  unfold dot_prod_safety_wit_6_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_6 : dot_prod_safety_wit_6.
Proof.
  open_generated_wit dot_prod_safety_wit_6.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_7_split_goal_1 : dot_prod_safety_wit_7_split_goal_1.
Proof.
  unfold dot_prod_safety_wit_7_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_7_split_goal_2 : dot_prod_safety_wit_7_split_goal_2.
Proof.
  unfold dot_prod_safety_wit_7_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_safety_wit_7 : dot_prod_safety_wit_7.
Proof.
  open_generated_wit dot_prod_safety_wit_7.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_return_wit_1_split_goal_1 : dot_prod_return_wit_1_split_goal_1.
Proof.
  unfold dot_prod_return_wit_1_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dot_prod_return_wit_1 : dot_prod_return_wit_1.
Proof.
  open_generated_wit dot_prod_return_wit_1.
  intros.
  entailer!.
Qed.

Lemma proof_of_cmp_polar_entail_wit_2_split_goal_1 : cmp_polar_entail_wit_2_split_goal_1.
Proof.
  unfold cmp_polar_entail_wit_2_split_goal_1.
  intros.
  entailer!.
  unfold point_colinear.
  rewrite <- point_cross_by_value_point.
  simpl in *.
  nia.
Qed.

Lemma proof_of_cmp_polar_entail_wit_2_split_goal_2 : cmp_polar_entail_wit_2_split_goal_2.
Proof.
  unfold cmp_polar_entail_wit_2_split_goal_2.
  intros.
  entailer!.
  rewrite <- point_cross_by_value_point.
  simpl in *.
  nia.
Qed.

Lemma proof_of_cmp_polar_entail_wit_2 : cmp_polar_entail_wit_2.
Proof.
  open_generated_wit cmp_polar_entail_wit_2.
  intros.
  entailer!.
  all: unfold point_colinear in *.
  all: rewrite <- point_cross_by_value_point; simpl in *; nia.
Qed.

Lemma proof_of_cmp_polar_entail_wit_3_split_goal_1 : cmp_polar_entail_wit_3_split_goal_1.
Proof.
  unfold cmp_polar_entail_wit_3_split_goal_1.
  intros.
  entailer!.
Qed.

Lemma proof_of_cmp_polar_entail_wit_3 : cmp_polar_entail_wit_3.
Proof.
  open_generated_wit cmp_polar_entail_wit_3.
  intros.
  entailer!.
  all: try (apply point_at_mid_by_value; reflexivity).
Qed.

Lemma proof_of_cmp_polar_return_wit_1_split_goal_1 : cmp_polar_return_wit_1_split_goal_1.
Proof.
  unfold cmp_polar_return_wit_1_split_goal_1.
  intros.
  entailer!.
  unfold point_cmp_polar.
  unfold point_colinear in PreH5.
  rewrite PreH5.
  destruct (Z_gt_dec 0 0); [nia |].
  destruct (Z_lt_dec 0 0); [nia |].
  rewrite <- PreH3.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [nia |].
  assert (Hmid0 :
    point_at_mid (point_mk gp_x_pre gp_y_pre)
      (point_mk a_x_pre a_y_pre) (point_mk b_x_pre b_y_pre) = 0) by nia.
  pose proof (PreH9 PreH5 Hmid0) as Hxy.
  rewrite Hxy.
  reflexivity.
Qed.

Lemma proof_of_cmp_polar_return_wit_1 : cmp_polar_return_wit_1.
Proof.
  open_generated_wit cmp_polar_return_wit_1.
  intros.
  entailer!.
  unfold point_cmp_polar.
  unfold point_colinear in PreH5.
  rewrite PreH5.
  destruct (Z_gt_dec 0 0); [nia |].
  destruct (Z_lt_dec 0 0); [nia |].
  rewrite <- PreH3.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [nia |].
  assert (Hmid0 :
    point_at_mid (point_mk gp_x_pre gp_y_pre)
      (point_mk a_x_pre a_y_pre) (point_mk b_x_pre b_y_pre) = 0) by nia.
  pose proof (PreH9 PreH5 Hmid0) as Hxy.
  rewrite Hxy.
  reflexivity.
Qed.

Lemma proof_of_cmp_polar_return_wit_2_split_goal_1 : cmp_polar_return_wit_2_split_goal_1.
Proof.
  unfold cmp_polar_return_wit_2_split_goal_1.
  intros.
  entailer!.
  unfold point_cmp_polar.
  unfold point_colinear in PreH5.
  rewrite PreH5.
  destruct (Z_gt_dec 0 0); [nia |].
  destruct (Z_lt_dec 0 0); [nia |].
  rewrite <- PreH3.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [reflexivity | nia].
Qed.

Lemma proof_of_cmp_polar_return_wit_2 : cmp_polar_return_wit_2.
Proof.
  open_generated_wit cmp_polar_return_wit_2.
  intros.
  entailer!.
  unfold point_cmp_polar.
  unfold point_colinear in PreH5.
  rewrite PreH5.
  destruct (Z_gt_dec 0 0); [nia |].
  destruct (Z_lt_dec 0 0); [nia |].
  rewrite <- PreH3.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [reflexivity | nia].
Qed.

Lemma proof_of_cmp_polar_return_wit_3_split_goal_1 : cmp_polar_return_wit_3_split_goal_1.
Proof.
  unfold cmp_polar_return_wit_3_split_goal_1.
  intros.
  entailer!.
  unfold point_cmp_polar.
  unfold point_colinear in PreH4.
  rewrite PreH4.
  destruct (Z_gt_dec 0 0); [nia |].
  destruct (Z_lt_dec 0 0); [nia |].
  rewrite <- PreH2.
  destruct (Z_gt_dec mid 0); [reflexivity | nia].
Qed.

Lemma proof_of_cmp_polar_return_wit_3 : cmp_polar_return_wit_3.
Proof.
  open_generated_wit cmp_polar_return_wit_3.
  intros.
  entailer!.
  unfold point_cmp_polar.
  unfold point_colinear in PreH4.
  rewrite PreH4.
  destruct (Z_gt_dec 0 0); [nia |].
  destruct (Z_lt_dec 0 0); [nia |].
  rewrite <- PreH2.
  destruct (Z_gt_dec mid 0); [reflexivity | nia].
Qed.

Lemma proof_of_cmp_polar_return_wit_4_split_goal_1 : cmp_polar_return_wit_4_split_goal_1.
Proof.
  unfold cmp_polar_return_wit_4_split_goal_1.
  intros.
  entailer!.
  unfold point_cmp_polar.
  replace (point_cross (point_mk gp_x_pre gp_y_pre)
             (point_mk a_x_pre a_y_pre) (point_mk b_x_pre b_y_pre))
    with retval.
  - destruct (Z_gt_dec retval 0); [nia |].
    destruct (Z_lt_dec retval 0); nia.
  - rewrite <- point_cross_by_value_point.
    simpl.
    nia.
Qed.

Lemma proof_of_cmp_polar_return_wit_4 : cmp_polar_return_wit_4.
Proof.
  open_generated_wit cmp_polar_return_wit_4.
  intros.
  entailer!.
  unfold point_cmp_polar.
  replace (point_cross (point_mk gp_x_pre gp_y_pre)
             (point_mk a_x_pre a_y_pre) (point_mk b_x_pre b_y_pre))
    with retval.
  - destruct (Z_gt_dec retval 0); [nia |].
    destruct (Z_lt_dec retval 0); nia.
  - rewrite <- point_cross_by_value_point.
    simpl.
    nia.
Qed.

Lemma proof_of_cmp_polar_return_wit_5_split_goal_1 : cmp_polar_return_wit_5_split_goal_1.
Proof.
  unfold cmp_polar_return_wit_5_split_goal_1.
  intros.
  entailer!.
  unfold point_cmp_polar.
  replace (point_cross (point_mk gp_x_pre gp_y_pre)
             (point_mk a_x_pre a_y_pre) (point_mk b_x_pre b_y_pre))
    with retval.
  - destruct (Z_gt_dec retval 0); nia.
  - rewrite <- point_cross_by_value_point.
    simpl.
    nia.
Qed.

Lemma proof_of_cmp_polar_return_wit_5 : cmp_polar_return_wit_5.
Proof.
  open_generated_wit cmp_polar_return_wit_5.
  intros.
  entailer!.
  unfold point_cmp_polar.
  replace (point_cross (point_mk gp_x_pre gp_y_pre)
             (point_mk a_x_pre a_y_pre) (point_mk b_x_pre b_y_pre))
    with retval.
  - destruct (Z_gt_dec retval 0); nia.
  - rewrite <- point_cross_by_value_point.
    simpl.
    nia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_1 : cmp_polar_partial_solve_wit_1_pure_split_goal_1.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_2 : cmp_polar_partial_solve_wit_1_pure_split_goal_2.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_3 : cmp_polar_partial_solve_wit_1_pure_split_goal_3.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_3; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_4 : cmp_polar_partial_solve_wit_1_pure_split_goal_4.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_4; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_5 : cmp_polar_partial_solve_wit_1_pure_split_goal_5.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_5; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_6 : cmp_polar_partial_solve_wit_1_pure_split_goal_6.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_6; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_7 : cmp_polar_partial_solve_wit_1_pure_split_goal_7.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_7; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_8 : cmp_polar_partial_solve_wit_1_pure_split_goal_8.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_8; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_9 : cmp_polar_partial_solve_wit_1_pure_split_goal_9.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_9; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_10 : cmp_polar_partial_solve_wit_1_pure_split_goal_10.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_10; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_11 : cmp_polar_partial_solve_wit_1_pure_split_goal_11.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_11; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_12 : cmp_polar_partial_solve_wit_1_pure_split_goal_12.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure_split_goal_12; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure : cmp_polar_partial_solve_wit_1_pure.
Proof.
  open_generated_wit cmp_polar_partial_solve_wit_1_pure.
  intros.
  entailer!.
  all: unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_1 : cmp_polar_partial_solve_wit_2_pure_split_goal_1.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_2 : cmp_polar_partial_solve_wit_2_pure_split_goal_2.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_2; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_3 : cmp_polar_partial_solve_wit_2_pure_split_goal_3.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_3; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_4 : cmp_polar_partial_solve_wit_2_pure_split_goal_4.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_4; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_5 : cmp_polar_partial_solve_wit_2_pure_split_goal_5.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_5; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_6 : cmp_polar_partial_solve_wit_2_pure_split_goal_6.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_6; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_7 : cmp_polar_partial_solve_wit_2_pure_split_goal_7.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_7; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_8 : cmp_polar_partial_solve_wit_2_pure_split_goal_8.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_8; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_9 : cmp_polar_partial_solve_wit_2_pure_split_goal_9.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_9; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_10 : cmp_polar_partial_solve_wit_2_pure_split_goal_10.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_10; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_11 : cmp_polar_partial_solve_wit_2_pure_split_goal_11.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_11; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure_split_goal_12 : cmp_polar_partial_solve_wit_2_pure_split_goal_12.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure_split_goal_12; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_2_pure : cmp_polar_partial_solve_wit_2_pure.
Proof.
  unfold cmp_polar_partial_solve_wit_2_pure; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_entail_wit_1 : build_hull_from_sorted_tail_dedup_entail_wit_1.
Proof.
  open_generated_wit build_hull_from_sorted_tail_dedup_entail_wit_1.
  intros.
  Exists (pivot0_low_level_spec :: nil).
  simpl.
  unfold store_point.
  entailer!.
  - simpl.
    replace (hull_pre + 0 * sizeof("Point")) with hull_pre.
    2: lia.
    change (0 + 1) with 1.
    sep_apply_r_atomic (PointArray.seg_single hull_pre 0 pivot0_low_level_spec).
    unfold StorePointAsElement.storeA, store_point.
    replace (hull_pre + 0 * sizeof("Point")) with hull_pre.
    2: lia.
    repeat match goal with
    | |- context [hull_pre + 0] => replace (hull_pre + 0) with hull_pre; [|lia]
    end.
    entailer!.
  - match goal with
    | Hsafe : safeExec _ (build_hull _ _) _ |- _ =>
        unfold build_hull in Hsafe at 1;
        unfold Graham_Scan_M.build_hull in Hsafe
    end.
    unfold build_hull_c_iter.
    rewrite sublist_self.
    2: reflexivity.
    match goal with
    | Hsafe : safeExec _ (_ ;; _) _ |- _ =>
        eapply safeExec_update'_bind in Hsafe
    end.
    eapply safeExec_conseq.
    + match goal with
      | Hsafe : safeExec _ _ _ |- _ => exact Hsafe
      end.
    + intros s [s0 [Hs _]]. subst s. reflexivity.
  - simpl. unfold points_in_bound. constructor; auto.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_entail_wit_2 : build_hull_from_sorted_tail_dedup_entail_wit_2.
Proof.
  open_generated_wit build_hull_from_sorted_tail_dedup_entail_wit_2.
  intros.
  Exists stk_2.
  entailer!.
  match goal with
  | Hsafe : safeExec _ (build_hull_c_iter _ _) _ |- _ =>
      unfold build_hull_c_iter in Hsafe at 1;
      rewrite (sublist_split i (Zlength l_low_level_spec) (i + 1) l_low_level_spec) in Hsafe
  end.
  2: lia.
  match goal with
  | Hsafe : safeExec _ _ _ |- _ =>
      rewrite (sublist_single default_point i l_low_level_spec) in Hsafe
  end.
  2: lia.
  all: try lia.
  match goal with
  | Hsafe : safeExec _ _ _ |- _ =>
      simpl in Hsafe;
      unfold Graham_Scan_M.step_p at 1 in Hsafe
  end.
  unfold build_hull_c_step, build_hull_c_next, build_hull_c_iter.
  eapply safeExec_proequiv.
  - eapply bind_equiv.
    + reflexivity.
    + intros []. reflexivity.
  - match goal with
    | Hsafe : safeExec _ _ _ |- _ => exact Hsafe
    end.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_entail_wit_3 : build_hull_from_sorted_tail_dedup_entail_wit_3.
Proof.
  open_generated_wit build_hull_from_sorted_tail_dedup_entail_wit_3.
  intros.
  pre_process.
  match goal with
  | Hlen : top + 1 = Zlength (rev stk_2) |- _ =>
      pose proof Hlen as Hstk_len
  | Hlen : Zlength (rev stk_2) = top + 1 |- _ =>
      pose proof eq_sym Hlen as Hstk_len
  end.
  destruct stk_2 as [| t [| s T]].
  - simpl in Hstk_len. rewrite Zlength_nil in Hstk_len. lia.
  - simpl in Hstk_len. rewrite Zlength_cons, Zlength_nil in Hstk_len. lia.
  - pose proof (rev_stack_pop_top t s T top Hstk_len) as Htop_pop.
    Exists (s :: T).
    split_pure_spatial.
    + change (rev (t :: s :: T)) with (rev (s :: T) ++ t :: nil).
      replace (top - 1 + 1) with top by lia.
      sep_apply_l_atomic (store_point_fold pivot_pre pivot0_low_level_spec).
	      cancel (store_point pivot_pre pivot0_low_level_spec).
	      cancel (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec).
	      cancel (PointArray.undef_seg hull_pre (tail_n_pre + 1)
	                n_full_low_level_spec).
	      assert (Htail_hi : top + 1 <= tail_n_pre + 1) by lia.
	      apply (point_array_seg_pop_tail hull_pre top (tail_n_pre + 1)
	               (rev (s :: T)) t Htop_pop Htail_hi).
    + repeat split_pures.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
	      * dump_pre_spatial. lia.
	      * dump_pre_spatial. lia.
	      * dump_pre_spatial. lia.
	      * dump_pre_spatial. exact PreH9.
	      * dump_pre_spatial. lia.
	      * dump_pre_spatial. exact PreH11.
	      * dump_pre_spatial. exact PreH12.
	      * dump_pre_spatial. exact PreH13.
	      * dump_pre_spatial. exact PreH14.
	      * dump_pre_spatial.
	        apply points_in_bound_app_l with (l2 := t :: nil).
	        match goal with
	        | Hpoints_stk : points_in_bound (rev (t :: s :: T)) |- _ =>
	            change (rev (t :: s :: T)) with (rev (s :: T) ++ t :: nil) in Hpoints_stk;
	            exact Hpoints_stk
	        end.
	      * dump_pre_spatial.
	      assert (Hnccw : ~ ccw s t (Znth i l_low_level_spec default_point)).
	      { match goal with
	        | Hcross : retval =
	                   point_cross_by_value
	                     (point_x (Znth (top - 1 - 0) (rev (t :: s :: T)) __default_Point))
	                     (point_y (Znth (top - 1 - 0) (rev (t :: s :: T)) __default_Point))
	                     (point_x (Znth (top - 0) (rev (t :: s :: T)) __default_Point))
	                     (point_y (Znth (top - 0) (rev (t :: s :: T)) __default_Point))
	                     (point_x (Znth i l_low_level_spec __default_Point))
	                     (point_y (Znth i l_low_level_spec __default_Point)) |- _ =>
	            rewrite (Znth_rev_stack_prev __default_Point t s T top Hstk_len) in Hcross;
	            rewrite (Znth_rev_stack_top __default_Point t s T top Hstk_len) in Hcross;
	            rewrite (Znth_indep l_low_level_spec i __default_Point default_point) in Hcross by lia;
	            rewrite point_cross_by_value_point in Hcross
	        end.
	        apply point_cross_le_0_not_ccw_local.
	        lia. }
	      eapply safeExec_build_hull_c_step_pop.
	      -- exact Hnccw.
	      -- match goal with
	         | Hsafe : safeExec (equiv (t :: s :: T))
	                      (build_hull_c_step l_low_level_spec i) X_low_level_spec |- _ =>
	             exact Hsafe
	         end.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_entail_wit_4_1 : build_hull_from_sorted_tail_dedup_entail_wit_4_1.
Proof.
  open_generated_wit build_hull_from_sorted_tail_dedup_entail_wit_4_1.
  intros.
  pre_process.
  match goal with
  | Hlen : top + 1 = Zlength (rev stk_2) |- _ =>
      pose proof Hlen as Hstk_len
  | Hlen : Zlength (rev stk_2) = top + 1 |- _ =>
      pose proof eq_sym Hlen as Hstk_len
  end.
  destruct stk_2 as [| t [| s T]].
  - change (Zlength (rev nil)) with 0 in Hstk_len.
    Exists (Znth i l_low_level_spec __default_Point :: nil).
    split_pure_spatial.
    + change (rev (Znth i l_low_level_spec __default_Point :: nil))
        with (rev nil ++ Znth i l_low_level_spec __default_Point :: nil).
      assert (Hhi_nonneg : 0 <= top + 1) by lia.
      assert (Hhi_bound : top + 1 + 1 <= tail_n_pre + 1) by lia.
      sep_apply_l_atomic (store_point_fold pivot_pre pivot0_low_level_spec).
      cancel (store_point pivot_pre pivot0_low_level_spec).
      cancel (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec).
	      sep_apply_l_atomic
	        (store_point_fold
	           (hull_pre + (top + 1) * sizeof("Point"))
	           (Znth i l_low_level_spec __default_Point)).
	      cancel (PointArray.undef_seg hull_pre (tail_n_pre + 1)
	                n_full_low_level_spec).
	      eapply (point_array_seg_snoc_store_undef hull_pre (top + 1)
	               (tail_n_pre + 1) (rev nil)
	               (Znth i l_low_level_spec __default_Point));
        [exact Hhi_nonneg | exact Hhi_bound].
    + repeat split_pures.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. assumption.
      * dump_pre_spatial.
        change (rev (Znth i l_low_level_spec __default_Point :: nil))
          with (rev nil ++ Znth i l_low_level_spec __default_Point :: nil).
        rewrite Zlength_app, Zlength_cons, Zlength_nil.
        rewrite Hstk_len.
        change (Zlength nil) with 0.
        lia.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial.
	        change (rev (Znth i l_low_level_spec __default_Point :: nil))
	          with (rev nil ++ Znth i l_low_level_spec __default_Point :: nil).
        apply points_in_bound_snoc_Znth; try assumption; lia.
      * dump_pre_spatial.
        rewrite (Znth_indep l_low_level_spec i __default_Point default_point) by lia.
        apply safeExec_build_hull_c_step_nil_push.
        assumption.
  - change (Zlength (rev (t :: nil))) with 1 in Hstk_len.
    Exists (Znth i l_low_level_spec __default_Point :: t :: nil).
    split_pure_spatial.
    + change (rev (Znth i l_low_level_spec __default_Point :: t :: nil))
        with (rev (t :: nil) ++ Znth i l_low_level_spec __default_Point :: nil).
      assert (Hhi_nonneg : 0 <= top + 1) by lia.
      assert (Hhi_bound : top + 1 + 1 <= tail_n_pre + 1) by lia.
      sep_apply_l_atomic (store_point_fold pivot_pre pivot0_low_level_spec).
      cancel (store_point pivot_pre pivot0_low_level_spec).
      cancel (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec).
	      sep_apply_l_atomic
	        (store_point_fold
	           (hull_pre + (top + 1) * sizeof("Point"))
	           (Znth i l_low_level_spec __default_Point)).
	      cancel (PointArray.undef_seg hull_pre (tail_n_pre + 1)
	                n_full_low_level_spec).
	      eapply (point_array_seg_snoc_store_undef hull_pre (top + 1)
	               (tail_n_pre + 1) (rev (t :: nil))
	               (Znth i l_low_level_spec __default_Point));
        [exact Hhi_nonneg | exact Hhi_bound].
    + repeat split_pures.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. assumption.
      * dump_pre_spatial.
        change (rev (Znth i l_low_level_spec __default_Point :: t :: nil))
          with (rev (t :: nil) ++ Znth i l_low_level_spec __default_Point :: nil).
        rewrite Zlength_app.
        change (Zlength (rev (t :: nil))) with 1.
        rewrite Zlength_cons, Zlength_nil.
        rewrite Hstk_len.
        change (Zlength nil) with 0.
        lia.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial.
	        change (rev (Znth i l_low_level_spec __default_Point :: t :: nil))
	          with (rev (t :: nil) ++ Znth i l_low_level_spec __default_Point :: nil).
        apply points_in_bound_snoc_Znth; try assumption; lia.
      * dump_pre_spatial.
        rewrite (Znth_indep l_low_level_spec i __default_Point default_point) by lia.
        apply safeExec_build_hull_c_step_single_push.
        assumption.
  - pose proof (rev_stack_two_len_ge t s T).
    lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_entail_wit_4_2 : build_hull_from_sorted_tail_dedup_entail_wit_4_2.
Proof.
  open_generated_wit build_hull_from_sorted_tail_dedup_entail_wit_4_2.
  intros.
  pre_process.
  match goal with
  | Hlen : top + 1 = Zlength (rev stk_2) |- _ =>
      pose proof Hlen as Hstk_len
  | Hlen : Zlength (rev stk_2) = top + 1 |- _ =>
      pose proof eq_sym Hlen as Hstk_len
  end.
  destruct stk_2 as [| t [| s T]].
  - simpl in Hstk_len. rewrite Zlength_nil in Hstk_len. lia.
  - simpl in Hstk_len. rewrite Zlength_cons, Zlength_nil in Hstk_len. lia.
  - Exists (Znth i l_low_level_spec __default_Point :: t :: s :: T).
    split_pure_spatial.
    + change (rev (Znth i l_low_level_spec __default_Point :: t :: s :: T))
        with (rev (t :: s :: T) ++ Znth i l_low_level_spec __default_Point :: nil).
      sep_apply_l_atomic (store_point_fold pivot_pre pivot0_low_level_spec).
      cancel (store_point pivot_pre pivot0_low_level_spec).
      cancel (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec).
	      sep_apply_l_atomic
	        (store_point_fold
	           (hull_pre + (top + 1) * sizeof("Point"))
	           (Znth i l_low_level_spec __default_Point)).
	      cancel (PointArray.undef_seg hull_pre (tail_n_pre + 1)
	                n_full_low_level_spec).
	      apply (point_array_seg_snoc_store_undef hull_pre (top + 1)
	               (tail_n_pre + 1) (rev (t :: s :: T))
	               (Znth i l_low_level_spec __default_Point)); lia.
    + repeat split_pures.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. assumption.
      * dump_pre_spatial.
        change (rev (Znth i l_low_level_spec __default_Point :: t :: s :: T))
          with (rev (t :: s :: T) ++ Znth i l_low_level_spec __default_Point :: nil).
        rewrite Zlength_app, Zlength_cons, Zlength_nil.
        lia.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial. assumption.
	      * dump_pre_spatial.
	        change (rev (Znth i l_low_level_spec __default_Point :: t :: s :: T))
	          with (rev (t :: s :: T) ++ Znth i l_low_level_spec __default_Point :: nil).
        apply points_in_bound_snoc_Znth; try assumption; lia.
      * dump_pre_spatial.
        assert (Hccw : ccw s t (Znth i l_low_level_spec default_point)).
        { match goal with
          | Hcross : retval =
                     point_cross_by_value
                       (point_x (Znth (top - 1 - 0) (rev (t :: s :: T)) __default_Point))
                       (point_y (Znth (top - 1 - 0) (rev (t :: s :: T)) __default_Point))
                       (point_x (Znth (top - 0) (rev (t :: s :: T)) __default_Point))
                       (point_y (Znth (top - 0) (rev (t :: s :: T)) __default_Point))
                       (point_x (Znth i l_low_level_spec __default_Point))
                       (point_y (Znth i l_low_level_spec __default_Point)) |- _ =>
              rewrite (Znth_rev_stack_prev __default_Point t s T top Hstk_len) in Hcross;
              rewrite (Znth_rev_stack_top __default_Point t s T top Hstk_len) in Hcross;
              rewrite (Znth_indep l_low_level_spec i __default_Point default_point) in Hcross by lia;
              rewrite point_cross_by_value_point in Hcross
          end.
          apply point_cross_gt_0_ccw_local.
          lia. }
        rewrite (Znth_indep l_low_level_spec i __default_Point default_point) by lia.
        eapply safeExec_build_hull_c_step_ccw_push.
        -- exact Hccw.
        -- assumption.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_return_wit_1 : build_hull_from_sorted_tail_dedup_return_wit_1.
Proof.
  open_generated_wit build_hull_from_sorted_tail_dedup_return_wit_1.
  intros.
  Exists stk_2.
  entailer!.
  match goal with
  | Hsafe : safeExec _ (build_hull_c_iter _ _) _ |- _ =>
      unfold build_hull_c_iter in Hsafe at 1;
      replace i with (Zlength l_low_level_spec) in Hsafe
  end.
  2: lia.
  match goal with
  | Hsafe : safeExec _ _ _ |- _ =>
      rewrite (@Zsublist_nil Point l_low_level_spec
                 (Zlength l_low_level_spec) (Zlength l_low_level_spec)) in Hsafe
  end.
  2: lia.
  match goal with
  | Hsafe : safeExec _ _ _ |- _ =>
      simpl in Hsafe;
      exact Hsafe
  end.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_1 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_1.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_1.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_2 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_2.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_2.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_3 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_3.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_3.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_4 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_4.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_4.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_5 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_5.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_5.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_6 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_6.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_6.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_7 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_7.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_7.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_8 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_8.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_8.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_9 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_9.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_9.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_10 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_10.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_10.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_11 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_11.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_11.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_12 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_12.
Proof.
  unfold build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_12.
  intros.
  entailer!.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound,
    Point_Order.point_bound, Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure.
Proof.
  open_generated_wit build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure.
  intros.
  entailer!.
  all: match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  all: unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: lia.
Qed.

Lemma proof_of_swap_points_return_wit_1_split_goal_1 : swap_points_return_wit_1_split_goal_1.
Proof.
  unfold swap_points_return_wit_1_split_goal_1.
  intros.
  entailer!.
  rewrite (Znth_indep pts_l i_pre __default_Point default_point) by lia.
  rewrite (Znth_indep pts_l j_pre __default_Point default_point) by lia.
  unfold point_swap.
  repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
  repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
  repeat rewrite replace_Znth_Znth by lia.
  repeat rewrite replace_Znth_twice by (rewrite ?Zlength_replace_Znth; lia).
  rewrite (Znth_indep pts_l j_pre __default_Point default_point) by lia.
  destruct (Znth i_pre pts_l default_point).
  destruct (Znth j_pre pts_l default_point).
  reflexivity.
Qed.

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof.
  open_generated_wit swap_points_return_wit_1.
  intros.
  entailer!.
  rewrite (Znth_indep pts_l i_pre __default_Point default_point) by lia.
  rewrite (Znth_indep pts_l j_pre __default_Point default_point) by lia.
  unfold point_swap.
  repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
  repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
  repeat rewrite replace_Znth_Znth by lia.
  repeat rewrite replace_Znth_twice by (rewrite ?Zlength_replace_Znth; lia).
  rewrite (Znth_indep pts_l j_pre __default_Point default_point) by lia.
  destruct (Znth i_pre pts_l default_point).
  destruct (Znth j_pre pts_l default_point).
  simpl.
  entailer!.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_1_split_goal_1 : partition_polar_points_entail_wit_1_split_goal_1.
Proof.
  unfold partition_polar_points_entail_wit_1_split_goal_1.
  intros.
  entailer!.
  unfold point_polar_partition_scan_inv.
  unfold point_permutation.
  unfold point_same_outside_range.
  split.
  - apply Permutation_refl.
  - split.
    + split.
      * reflexivity.
      * intros k Hk _. reflexivity.
    + split.
      * rewrite (Znth_indep pts_l high_pre __default_Point default_point) by lia.
        destruct (Znth high_pre pts_l default_point); reflexivity.
      * split; intros k Hk; lia.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_1_split_goal_2 : partition_polar_points_entail_wit_1_split_goal_2.
Proof.
  unfold partition_polar_points_entail_wit_1_split_goal_2.
  intros.
  entailer!.
  eapply points_in_bound_Znth_point_mk; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_1_split_goal_3 : partition_polar_points_entail_wit_1_split_goal_3.
Proof.
  unfold partition_polar_points_entail_wit_1_split_goal_3.
  intros.
  entailer!.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_1_split_goal_4 : partition_polar_points_entail_wit_1_split_goal_4.
Proof.
  unfold partition_polar_points_entail_wit_1_split_goal_4.
  intros.
  entailer!.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_1 : partition_polar_points_entail_wit_1.
Proof.
  open_generated_wit partition_polar_points_entail_wit_1.
  intros.
  Exists pts_l.
  entailer!.
  - unfold point_polar_partition_scan_inv.
    unfold point_permutation.
    unfold point_same_outside_range.
    split.
    + apply Permutation_refl.
    + split.
      * split.
        -- reflexivity.
        -- intros k Hk _.
           reflexivity.
      * split.
        -- rewrite (Znth_indep pts_l high_pre __default_Point default_point) by lia.
           destruct (Znth high_pre pts_l default_point); reflexivity.
        -- split; intros k Hk; lia.
  - eapply points_in_bound_Znth_point_mk; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_1 : partition_polar_points_entail_wit_2_1_split_goal_1.
Proof.
  unfold partition_polar_points_entail_wit_2_1_split_goal_1.
  intros.
  entailer!.
  unfold point_polar_partition_scan_inv in *.
  match goal with
  | Hscan : point_permutation _ _ /\ _ |- _ =>
      destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
  end.
  split.
  - eapply Permutation_trans.
    + exact Hperm.
    + eapply point_swap_permutation; lia.
  - split.
    + eapply point_same_outside_range_point_swap_inside; eauto; lia.
    + split.
      * rewrite point_swap_Znth_other_index by lia.
        exact Hpivot.
      * split.
        -- intros k Hk.
           destruct (Z.eq_dec k (i + 1)) as [Hki | Hki].
           ++ subst k.
              rewrite point_swap_Znth_left_index by lia.
              replace (Znth j pts_cur_2 default_point)
                with (point_mk (point_x (Znth j pts_cur_2 __default_Point))
                               (point_y (Znth j pts_cur_2 __default_Point))).
              2:{
                rewrite (Znth_indep pts_cur_2 j __default_Point default_point)
                  by lia.
                destruct (Znth j pts_cur_2 default_point); reflexivity.
              }
              rewrite <- PreH4.
              exact PreH3.
           ++ rewrite point_swap_Znth_other_index by lia.
              apply Hle. lia.
        -- intros k Hk.
           destruct (Z.eq_dec k j) as [Hkj | Hkj].
           ++ subst k.
              rewrite point_swap_Znth_right_index by lia.
              apply Hgt. lia.
           ++ rewrite point_swap_Znth_other_index by lia.
              apply Hgt. lia.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_2 : partition_polar_points_entail_wit_2_1_split_goal_2.
Proof.
  unfold partition_polar_points_entail_wit_2_1_split_goal_2.
  intros.
  entailer!.
  eapply point_polar_cmp_safe_range_point_swap; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_3 : partition_polar_points_entail_wit_2_1_split_goal_3.
Proof.
  unfold partition_polar_points_entail_wit_2_1_split_goal_3.
  intros.
  entailer!.
  eapply leftmost_permutation.
  - eapply point_swap_permutation; lia.
  - assumption.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_4 : partition_polar_points_entail_wit_2_1_split_goal_4.
Proof.
  unfold partition_polar_points_entail_wit_2_1_split_goal_4.
  intros.
  entailer!.
  eapply points_in_bound_point_swap; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_5 : partition_polar_points_entail_wit_2_1_split_goal_5.
Proof.
  unfold partition_polar_points_entail_wit_2_1_split_goal_5.
  intros.
  entailer!.
  rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j)
            high_pre __default_Point default_point)
    by (rewrite Zlength_point_swap; lia).
  rewrite point_swap_Znth_other_index by lia.
  rewrite <- (Znth_indep pts_cur_2 high_pre __default_Point default_point)
    by lia.
  assumption.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_6 : partition_polar_points_entail_wit_2_1_split_goal_6.
Proof.
  unfold partition_polar_points_entail_wit_2_1_split_goal_6.
  intros.
  entailer!.
  rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j)
            high_pre __default_Point default_point)
    by (rewrite Zlength_point_swap; lia).
  rewrite point_swap_Znth_other_index by lia.
  rewrite <- (Znth_indep pts_cur_2 high_pre __default_Point default_point)
    by lia.
  assumption.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_7 : partition_polar_points_entail_wit_2_1_split_goal_7.
Proof.
  unfold partition_polar_points_entail_wit_2_1_split_goal_7.
  intros.
  entailer!.
  rewrite Zlength_point_swap. assumption.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1 : partition_polar_points_entail_wit_2_1.
Proof.
  open_generated_wit partition_polar_points_entail_wit_2_1.
  intros.
  Exists (point_swap pts_cur_2 (i + 1) j).
  entailer!.
  - unfold point_polar_partition_scan_inv in *.
    match goal with
    | Hscan : point_permutation _ _ /\ _ |- _ =>
        destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
    end.
    split.
    + eapply Permutation_trans.
      * exact Hperm.
      * eapply point_swap_permutation; lia.
    + split.
      * eapply point_same_outside_range_point_swap_inside; eauto; lia.
      * split.
        -- rewrite point_swap_Znth_other_index by lia.
           exact Hpivot.
        -- split.
           ++ intros k Hk.
              destruct (Z.eq_dec k (i + 1)) as [Hki | Hki].
              ** subst k.
                 rewrite point_swap_Znth_left_index by lia.
                 replace (Znth j pts_cur_2 default_point)
                   with (point_mk (point_x (Znth j pts_cur_2 __default_Point))
                                  (point_y (Znth j pts_cur_2 __default_Point))).
	                 2:{
	                   rewrite (Znth_indep pts_cur_2 j __default_Point default_point)
	                     by lia.
	                   destruct (Znth j pts_cur_2 default_point); reflexivity.
	                 }
	                 match goal with
	                 | Hret_le : retval <= 0,
	                   Hret_eq : retval =
	                     point_cmp_polar (point_mk gx_pre gy_pre)
	                       (point_mk (point_x (Znth j pts_cur_2 __default_Point))
	                                 (point_y (Znth j pts_cur_2 __default_Point)))
	                       (point_mk pivot_x pivot_y) |- _ =>
	                     rewrite <- Hret_eq; exact Hret_le
	                 end.
              ** rewrite point_swap_Znth_other_index by lia.
                 apply Hle. lia.
           ++ intros k Hk.
              destruct (Z.eq_dec k j) as [Hkj | Hkj].
              ** subst k.
                 rewrite point_swap_Znth_right_index by lia.
                 apply Hgt. lia.
              ** rewrite point_swap_Znth_other_index by lia.
                 apply Hgt. lia.
  - eapply point_polar_cmp_safe_range_point_swap; eauto; lia.
  - eapply leftmost_permutation.
	    + eapply point_swap_permutation; lia.
	    + assumption.
  - eapply points_in_bound_point_swap; eauto; lia.
  - rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j)
              high_pre __default_Point default_point)
      by (rewrite Zlength_point_swap; lia).
	    rewrite point_swap_Znth_other_index by lia.
	    rewrite <- (Znth_indep pts_cur_2 high_pre __default_Point default_point)
	      by lia.
	    assumption.
  - rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j)
              high_pre __default_Point default_point)
      by (rewrite Zlength_point_swap; lia).
	    rewrite point_swap_Znth_other_index by lia.
	    rewrite <- (Znth_indep pts_cur_2 high_pre __default_Point default_point)
	      by lia.
	    assumption.
	  - rewrite Zlength_point_swap. assumption.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_2_split_goal_1 : partition_polar_points_entail_wit_2_2_split_goal_1.
Proof.
  unfold partition_polar_points_entail_wit_2_2_split_goal_1.
  intros.
  entailer!.
  unfold point_polar_partition_scan_inv in *.
  match goal with
  | Hscan : point_permutation _ _ /\ _ |- _ =>
      destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
  end.
  split; [exact Hperm|].
  split; [exact Hsame|].
  split; [exact Hpivot|].
  split.
  - intros k Hk.
    destruct (Z_lt_ge_dec k (i + 1)) as [Hklt | Hkge].
    + apply Hle. lia.
    + assert (k = i + 1) by lia.
      subst k.
      rewrite PreH1.
      replace (Znth j pts_cur_2 default_point)
        with (point_mk (point_x (Znth j pts_cur_2 __default_Point))
                       (point_y (Znth j pts_cur_2 __default_Point))).
      2:{
        rewrite (Znth_indep pts_cur_2 j __default_Point default_point) by lia.
        destruct (Znth j pts_cur_2 default_point); reflexivity.
      }
      rewrite <- PreH3.
      exact PreH2.
  - intros k Hk.
    lia.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_2 : partition_polar_points_entail_wit_2_2.
Proof.
  open_generated_wit partition_polar_points_entail_wit_2_2.
  intros.
  Exists pts_cur_2.
  entailer!.
  unfold point_polar_partition_scan_inv in *.
  match goal with
  | Hscan : point_permutation _ _ /\ _ |- _ =>
      destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
  end.
  split; [exact Hperm|].
  split; [exact Hsame|].
  split; [exact Hpivot|].
  split.
  - intros k Hk.
    destruct (Z_lt_ge_dec k (i + 1)) as [Hklt | Hkge].
    + apply Hle. lia.
    + assert (k = i + 1) by lia.
      subst k.
      match goal with
      | Hij : i + 1 = j |- _ => rewrite Hij
      end.
      replace (Znth j pts_cur_2 default_point)
        with (point_mk (point_x (Znth j pts_cur_2 __default_Point))
                       (point_y (Znth j pts_cur_2 __default_Point))).
	      2:{
	        rewrite (Znth_indep pts_cur_2 j __default_Point default_point) by lia.
	        destruct (Znth j pts_cur_2 default_point); reflexivity.
	      }
	      match goal with
	      | Hret_le : retval <= 0,
	        Hret_eq : retval =
	          point_cmp_polar (point_mk gx_pre gy_pre)
	            (point_mk (point_x (Znth j pts_cur_2 __default_Point))
	                      (point_y (Znth j pts_cur_2 __default_Point)))
	            (point_mk pivot_x pivot_y) |- _ =>
	          rewrite <- Hret_eq; exact Hret_le
	      end.
  - intros k Hk.
    lia.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_3_split_goal_1 : partition_polar_points_entail_wit_2_3_split_goal_1.
Proof.
  unfold partition_polar_points_entail_wit_2_3_split_goal_1.
  intros.
  entailer!.
  unfold point_polar_partition_scan_inv in *.
  match goal with
  | Hscan : point_permutation _ _ /\ _ |- _ =>
      destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
  end.
  split; [exact Hperm|].
  split; [exact Hsame|].
  split; [exact Hpivot|].
  split.
  - intros k Hk.
    apply Hle. lia.
  - intros k Hk.
    destruct (Z.eq_dec k j) as [Hkj | Hkj].
    + subst k.
      rewrite <- Hpivot.
      replace (Znth j pts_cur_2 default_point)
        with (point_mk (point_x (Znth j pts_cur_2 __default_Point))
                       (point_y (Znth j pts_cur_2 __default_Point))).
      2:{
        rewrite (Znth_indep pts_cur_2 j __default_Point default_point) by lia.
        destruct (Znth j pts_cur_2 default_point); reflexivity.
      }
      eapply point_cmp_polar_gt_flip_under_leftmost
        with (l := pts_cur_2).
      * eassumption.
      * replace (point_mk (point_x (Znth j pts_cur_2 __default_Point))
                         (point_y (Znth j pts_cur_2 __default_Point)))
          with (Znth j pts_cur_2 default_point).
        -- apply Znth_In_range. lia.
        -- rewrite (Znth_indep pts_cur_2 j __default_Point default_point)
             by lia.
           destruct (Znth j pts_cur_2 default_point); reflexivity.
      * apply Znth_In_range. lia.
      * rewrite Hpivot.
        rewrite <- PreH2.
        exact PreH1.
    + apply Hgt. lia.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_3 : partition_polar_points_entail_wit_2_3.
Proof.
  open_generated_wit partition_polar_points_entail_wit_2_3.
  intros.
  Exists pts_cur_2.
  entailer!.
  unfold point_polar_partition_scan_inv in *.
  match goal with
  | Hscan : point_permutation _ _ /\ _ |- _ =>
      destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
  end.
  split; [exact Hperm|].
  split; [exact Hsame|].
  split; [exact Hpivot|].
  split.
  - intros k Hk.
    apply Hle. lia.
  - intros k Hk.
    destruct (Z.eq_dec k j) as [Hkj | Hkj].
    + subst k.
      rewrite <- Hpivot.
      replace (Znth j pts_cur_2 default_point)
        with (point_mk (point_x (Znth j pts_cur_2 __default_Point))
                       (point_y (Znth j pts_cur_2 __default_Point))).
      2:{
        rewrite (Znth_indep pts_cur_2 j __default_Point default_point) by lia.
        destruct (Znth j pts_cur_2 default_point); reflexivity.
      }
      eapply point_cmp_polar_gt_flip_under_leftmost
        with (l := pts_cur_2).
      * eassumption.
      * replace (point_mk (point_x (Znth j pts_cur_2 __default_Point))
                         (point_y (Znth j pts_cur_2 __default_Point)))
          with (Znth j pts_cur_2 default_point).
        -- apply Znth_In_range. lia.
        -- rewrite (Znth_indep pts_cur_2 j __default_Point default_point)
             by lia.
           destruct (Znth j pts_cur_2 default_point); reflexivity.
	      * apply Znth_In_range. lia.
	      * rewrite Hpivot.
	        match goal with
	        | Hret_gt : retval > 0,
	          Hret_eq : retval =
	            point_cmp_polar (point_mk gx_pre gy_pre)
	              (point_mk (point_x (Znth j pts_cur_2 __default_Point))
	                        (point_y (Znth j pts_cur_2 __default_Point)))
	              (point_mk pivot_x pivot_y) |- _ =>
	            rewrite <- Hret_eq; exact Hret_gt
	        end.
    + apply Hgt. lia.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_1 : partition_polar_points_return_wit_1_split_goal_1.
Proof.
  unfold partition_polar_points_return_wit_1_split_goal_1.
  intros.
  entailer!.
  unfold point_polar_partition_scan_inv in PreH21.
  destruct PreH21 as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  unfold point_polar_partitioned_at.
  assert (Hj_high : j = high_pre) by lia.
  subst j.
  rewrite point_swap_Znth_left_index by lia.
  rewrite Hpivot.
  repeat split; try lia.
  - apply Forall_Znth_intro with (d := default_point).
    intros k Hk.
    rewrite Zlength_sublist in Hk by (try rewrite Zlength_point_swap; lia).
    rewrite Znth_sublist by (try rewrite Zlength_point_swap; lia).
    rewrite point_swap_Znth_other_index by lia.
    apply Hle. lia.
  - apply Forall_Znth_intro with (d := default_point).
    intros k Hk.
    rewrite Zlength_sublist in Hk by (try rewrite Zlength_point_swap; lia).
    rewrite Znth_sublist by (try rewrite Zlength_point_swap; lia).
    destruct (Z.eq_dec (i + 1 + 1 + k) high_pre) as [Hkh | Hkh].
    + replace (k + (i + 1 + 1)) with high_pre by lia.
      rewrite point_swap_Znth_right_index by lia.
      apply Hgt. lia.
    + rewrite point_swap_Znth_other_index by lia.
      apply Hgt. lia.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_2 : partition_polar_points_return_wit_1_split_goal_2.
Proof.
  unfold partition_polar_points_return_wit_1_split_goal_2.
  intros.
  entailer!.
  eapply point_polar_cmp_safe_range_point_swap; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_3 : partition_polar_points_return_wit_1_split_goal_3.
Proof.
  unfold partition_polar_points_return_wit_1_split_goal_3.
  intros.
  entailer!.
  unfold point_polar_partition_scan_inv in PreH21.
  destruct PreH21 as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  eapply point_same_outside_range_point_swap_inside; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_4 : partition_polar_points_return_wit_1_split_goal_4.
Proof.
  unfold partition_polar_points_return_wit_1_split_goal_4.
  intros.
  entailer!.
  unfold point_polar_partition_scan_inv in PreH21.
  destruct PreH21 as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  eapply Permutation_trans; [exact Hperm |].
  eapply point_swap_permutation; lia.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_5 : partition_polar_points_return_wit_1_split_goal_5.
Proof.
  unfold partition_polar_points_return_wit_1_split_goal_5.
  intros.
  entailer!.
  eapply leftmost_permutation.
  - eapply point_swap_permutation; lia.
  - eauto.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_6 : partition_polar_points_return_wit_1_split_goal_6.
Proof.
  unfold partition_polar_points_return_wit_1_split_goal_6.
  intros.
  entailer!.
  eapply points_in_bound_point_swap; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_7 : partition_polar_points_return_wit_1_split_goal_7.
Proof.
  unfold partition_polar_points_return_wit_1_split_goal_7.
  intros.
  entailer!.
  rewrite Zlength_point_swap. assumption.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1 : partition_polar_points_return_wit_1.
Proof.
  open_generated_wit partition_polar_points_return_wit_1.
  intros.
  Exists (point_swap pts_cur (i + 1) high_pre).
  entailer!.
  - unfold point_polar_partition_scan_inv in PreH21.
    destruct PreH21 as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
    unfold point_polar_partitioned_at.
    assert (Hj_high : j = high_pre) by lia.
    subst j.
    rewrite point_swap_Znth_left_index by lia.
    rewrite Hpivot.
    repeat split; try lia.
    + apply Forall_Znth_intro with (d := default_point).
      intros k Hk.
      rewrite Zlength_sublist in Hk by (try rewrite Zlength_point_swap; lia).
      rewrite Znth_sublist by (try rewrite Zlength_point_swap; lia).
      rewrite point_swap_Znth_other_index by lia.
      apply Hle. lia.
    + apply Forall_Znth_intro with (d := default_point).
      intros k Hk.
      rewrite Zlength_sublist in Hk by (try rewrite Zlength_point_swap; lia).
      rewrite Znth_sublist by (try rewrite Zlength_point_swap; lia).
      destruct (Z.eq_dec (i + 1 + 1 + k) high_pre) as [Hkh | Hkh].
      * replace (k + (i + 1 + 1)) with high_pre by lia.
        rewrite point_swap_Znth_right_index by lia.
        apply Hgt. lia.
      * rewrite point_swap_Znth_other_index by lia.
        apply Hgt. lia.
  - eapply point_polar_cmp_safe_range_point_swap; eauto; lia.
  - unfold point_polar_partition_scan_inv in PreH21.
    destruct PreH21 as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
    eapply point_same_outside_range_point_swap_inside; eauto; lia.
  - unfold point_polar_partition_scan_inv in PreH21.
    destruct PreH21 as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
    eapply Permutation_trans; [exact Hperm |].
    eapply point_swap_permutation; lia.
  - eapply leftmost_permutation.
    + eapply point_swap_permutation; lia.
    + eauto.
  - eapply points_in_bound_point_swap; eauto; lia.
  - rewrite Zlength_point_swap. assumption.
Qed.

Lemma proof_of_partition_polar_points_return_wit_2_split_goal_1 : partition_polar_points_return_wit_2_split_goal_1.
Proof.
  unfold partition_polar_points_return_wit_2_split_goal_1.
  intros.
  entailer!.
  unfold point_polar_partition_scan_inv in PreH20.
  destruct PreH20 as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  unfold point_polar_partitioned_at.
  assert (Hj_high : j = high_pre) by lia.
  assert (Hpivot_idx : i + 1 = high_pre) by lia.
  rewrite Hpivot_idx.
  rewrite Hpivot.
  repeat split; try lia.
  - apply Forall_Znth_intro with (d := default_point).
    intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist by lia.
    apply Hle.
    lia.
  - rewrite (@Zsublist_nil Point pts_cur (high_pre + 1) (high_pre + 1))
      by lia.
    constructor.
Qed.

Lemma proof_of_partition_polar_points_return_wit_2_split_goal_2 : partition_polar_points_return_wit_2_split_goal_2.
Proof.
  unfold partition_polar_points_return_wit_2_split_goal_2.
  intros.
  entailer!.
  unfold point_polar_partition_scan_inv in PreH20.
  destruct PreH20 as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  exact Hsame.
Qed.

Lemma proof_of_partition_polar_points_return_wit_2_split_goal_3 : partition_polar_points_return_wit_2_split_goal_3.
Proof.
  unfold partition_polar_points_return_wit_2_split_goal_3.
  intros.
  entailer!.
  unfold point_polar_partition_scan_inv in PreH20.
  destruct PreH20 as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  exact Hperm.
Qed.

Lemma proof_of_partition_polar_points_return_wit_2 : partition_polar_points_return_wit_2.
Proof.
  open_generated_wit partition_polar_points_return_wit_2.
  intros.
  Exists pts_cur.
  entailer!;
    unfold point_polar_partition_scan_inv in *;
    match goal with
    | Hscan : point_permutation _ _ /\ _ |- _ =>
        destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
    end;
    try exact Hperm; try exact Hsame.
  unfold point_polar_partitioned_at.
  assert (Hj_high : j = high_pre) by lia.
  assert (Hpivot_idx : i + 1 = high_pre) by lia.
  rewrite Hpivot_idx.
  rewrite Hpivot.
  repeat split; try lia.
  - apply Forall_Znth_intro with (d := default_point).
    intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist by lia.
    apply Hle.
    lia.
  - rewrite (@Zsublist_nil Point pts_cur (high_pre + 1) (high_pre + 1))
      by lia.
    constructor.
Qed.

Lemma proof_of_partition_polar_points_partial_solve_wit_5_pure_split_goal_1 : partition_polar_points_partial_solve_wit_5_pure_split_goal_1.
Proof.
  unfold partition_polar_points_partial_solve_wit_5_pure_split_goal_1.
  intros.
  entailer!.
  eapply points_in_bound_Znth_point_mk; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_partial_solve_wit_5_pure_split_goal_2 : partition_polar_points_partial_solve_wit_5_pure_split_goal_2.
Proof.
  unfold partition_polar_points_partial_solve_wit_5_pure_split_goal_2.
  intros.
  entailer!.
  assert (Hj_range : low_pre <= j <= high_pre) by lia.
  assert (Hhi_range : low_pre <= high_pre <= high_pre) by lia.
  specialize (PreH40 j high_pre Hj_range Hhi_range).
  rewrite (Znth_indep pts_cur j __default_Point default_point) by lia.
  replace (point_mk
             (point_x (Znth j pts_cur default_point))
             (point_y (Znth j pts_cur default_point)))
    with (Znth j pts_cur default_point)
    by (destruct (Znth j pts_cur default_point); reflexivity).
  replace (point_mk pivot_x pivot_y)
    with (Znth high_pre pts_cur default_point).
  - exact PreH40.
  - rewrite <- PreH33, <- PreH34.
    rewrite (Znth_indep pts_cur high_pre __default_Point default_point) by lia.
    destruct (Znth high_pre pts_cur default_point); reflexivity.
Qed.

Lemma proof_of_partition_polar_points_partial_solve_wit_5_pure : partition_polar_points_partial_solve_wit_5_pure.
Proof.
  open_generated_wit partition_polar_points_partial_solve_wit_5_pure.
  intros.
  entailer!.
  - eapply points_in_bound_Znth_point_mk; eauto; lia.
  - assert (Hj_range : low_pre <= j <= high_pre) by lia.
    assert (Hhi_range : low_pre <= high_pre <= high_pre) by lia.
    specialize (PreH18 j high_pre Hj_range Hhi_range).
    rewrite (Znth_indep pts_cur j __default_Point default_point) by lia.
    replace (point_mk
               (point_x (Znth j pts_cur default_point))
               (point_y (Znth j pts_cur default_point)))
      with (Znth j pts_cur default_point)
      by (destruct (Znth j pts_cur default_point); reflexivity).
    replace (point_mk pivot_x pivot_y)
      with (Znth high_pre pts_cur default_point).
    + exact PreH18.
    + rewrite <- PreH11, <- PreH12.
      rewrite (Znth_indep pts_cur high_pre __default_Point default_point) by lia.
      destruct (Znth high_pre pts_cur default_point); reflexivity.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_1_split_goal_1 : quicksort_polar_points_return_wit_1_split_goal_1.
Proof.
  unfold quicksort_polar_points_return_wit_1_split_goal_1.
  intros.
  entailer!.
  assert (Hpart3 :
    point_polar_partitioned_at (point_mk gx_pre gy_pre)
      pts_out_3 left_pre right_pre retval).
  {
    eapply point_polar_partitioned_at_preserved_by_left;
      [eassumption | lia | eassumption | lia | eassumption].
  }
  assert (Hpart4 :
    point_polar_partitioned_at (point_mk gx_pre gy_pre)
      pts_out_4 left_pre right_pre retval).
  {
    eapply point_polar_partitioned_at_preserved_by_right;
      [eassumption | lia | eassumption | lia | exact Hpart3].
  }
  assert (Hleft_sorted4 :
    point_sorted_range (point_mk gx_pre gy_pre)
      pts_out_4 left_pre (retval - 1)).
  {
    eapply point_sorted_range_ext with (l := pts_out_3).
    - lia.
    - lia.
    - assert (Hsame34 :
          point_same_outside_range pts_out_3 pts_out_4
            (retval + 1) right_pre) by assumption.
      destruct Hsame34 as [Hlen34 _].
      exact Hlen34.
    - intros k Hk.
      assert (Hsame34 :
          point_same_outside_range pts_out_3 pts_out_4
            (retval + 1) right_pre) by assumption.
      destruct Hsame34 as [_ Hsame34].
      apply Hsame34; [lia | left; lia].
    - assumption.
  }
  eapply point_sorted_range_partition_merge with (p := retval);
    try eassumption; lia.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_1_split_goal_2 : quicksort_polar_points_return_wit_1_split_goal_2.
Proof.
  unfold quicksort_polar_points_return_wit_1_split_goal_2.
  intros.
  entailer!.
  assert (Hsafe3 :
    point_polar_cmp_safe_range (point_mk gx_pre gy_pre)
      pts_out_3 left_pre right_pre).
  {
    eapply point_polar_cmp_safe_range_subrange_permutation
      with (l := pts_out_2) (sublo := left_pre) (subhi := retval - 1);
      try eassumption; lia.
  }
  eapply point_polar_cmp_safe_range_subrange_permutation
    with (l := pts_out_3) (sublo := retval + 1) (subhi := right_pre);
    try eassumption; lia.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_1_split_goal_3 : quicksort_polar_points_return_wit_1_split_goal_3.
Proof.
  unfold quicksort_polar_points_return_wit_1_split_goal_3.
  intros.
  entailer!.
  assert (Hsame23_full :
    point_same_outside_range pts_out_2 pts_out_3 left_pre right_pre).
  {
    eapply (point_same_outside_range_weaken
              pts_out_2 pts_out_3 left_pre (retval - 1)
      left_pre right_pre);
      [lia | lia | assumption].
  }
  assert (Hsame34_full :
    point_same_outside_range pts_out_3 pts_out_4 left_pre right_pre).
  {
    eapply (point_same_outside_range_weaken
              pts_out_3 pts_out_4 (retval + 1) right_pre
      left_pre right_pre);
      [lia | lia | assumption].
  }
  change (point_same_outside_range pts_l pts_out_4 left_pre right_pre).
  eapply (point_same_outside_range_trans
            pts_l pts_out_3 pts_out_4 left_pre right_pre);
    [| exact Hsame34_full].
  eapply (point_same_outside_range_trans
            pts_l pts_out_2 pts_out_3 left_pre right_pre);
    [assumption | exact Hsame23_full].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_1_split_goal_4 : quicksort_polar_points_return_wit_1_split_goal_4.
Proof.
  unfold quicksort_polar_points_return_wit_1_split_goal_4.
  intros.
  entailer!.
  unfold point_permutation in *.
  eapply Permutation_trans; [eassumption |].
  eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_1 : quicksort_polar_points_return_wit_1.
Proof.
  open_generated_wit quicksort_polar_points_return_wit_1.
  intros.
  Exists pts_out_4.
  entailer!.
  - assert (Hpart3 :
      point_polar_partitioned_at (point_mk gx_pre gy_pre)
        pts_out_3 left_pre right_pre retval).
    {
      eapply point_polar_partitioned_at_preserved_by_left;
        [eassumption | lia | eassumption | lia | eassumption].
    }
    assert (Hpart4 :
      point_polar_partitioned_at (point_mk gx_pre gy_pre)
        pts_out_4 left_pre right_pre retval).
    {
      eapply point_polar_partitioned_at_preserved_by_right;
        [eassumption | lia | eassumption | lia | exact Hpart3].
    }
    assert (Hleft_sorted4 :
      point_sorted_range (point_mk gx_pre gy_pre)
        pts_out_4 left_pre (retval - 1)).
    {
      eapply point_sorted_range_ext with (l := pts_out_3).
      - lia.
      - lia.
      - assert (Hsame34 :
            point_same_outside_range pts_out_3 pts_out_4
              (retval + 1) right_pre) by assumption.
        destruct Hsame34 as [Hlen34 _].
        exact Hlen34.
      - intros k Hk.
        assert (Hsame34 :
            point_same_outside_range pts_out_3 pts_out_4
              (retval + 1) right_pre) by assumption.
        destruct Hsame34 as [_ Hsame34].
        apply Hsame34; [lia | left; lia].
      - assumption.
    }
    eapply point_sorted_range_partition_merge with (p := retval);
      try eassumption; lia.
  - assert (Hsafe3 :
      point_polar_cmp_safe_range (point_mk gx_pre gy_pre)
        pts_out_3 left_pre right_pre).
    {
      eapply point_polar_cmp_safe_range_subrange_permutation
        with (l := pts_out_2) (sublo := left_pre) (subhi := retval - 1);
        try eassumption; lia.
    }
    eapply point_polar_cmp_safe_range_subrange_permutation
      with (l := pts_out_3) (sublo := retval + 1) (subhi := right_pre);
      try eassumption; lia.
  - assert (Hsame23_full :
      point_same_outside_range pts_out_2 pts_out_3 left_pre right_pre).
    {
      eapply (point_same_outside_range_weaken
                pts_out_2 pts_out_3 left_pre (retval - 1)
        left_pre right_pre);
        [lia | lia | assumption].
    }
    assert (Hsame34_full :
      point_same_outside_range pts_out_3 pts_out_4 left_pre right_pre).
    {
      eapply (point_same_outside_range_weaken
                pts_out_3 pts_out_4 (retval + 1) right_pre
        left_pre right_pre);
        [lia | lia | assumption].
    }
    change (point_same_outside_range pts_l pts_out_4 left_pre right_pre).
    eapply (point_same_outside_range_trans
              pts_l pts_out_3 pts_out_4 left_pre right_pre);
      [| exact Hsame34_full].
    eapply (point_same_outside_range_trans
              pts_l pts_out_2 pts_out_3 left_pre right_pre);
      [assumption | exact Hsame23_full].
  - unfold point_permutation in *.
    eapply Permutation_trans; [eassumption |].
    eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_2_split_goal_1 : quicksort_polar_points_return_wit_2_split_goal_1.
Proof.
  unfold quicksort_polar_points_return_wit_2_split_goal_1.
  intros.
  entailer!.
  assert (Hpart3 :
    point_polar_partitioned_at (point_mk gx_pre gy_pre)
      pts_out_3 left_pre right_pre retval).
  {
    eapply point_polar_partitioned_at_preserved_by_right;
      [eassumption | lia | eassumption | lia | eassumption].
  }
  eapply point_sorted_range_from_right_boundary with (p := retval);
    [lia | lia | lia | exact Hpart3 | assumption].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_2_split_goal_2 : quicksort_polar_points_return_wit_2_split_goal_2.
Proof.
  unfold quicksort_polar_points_return_wit_2_split_goal_2.
  intros.
  entailer!.
  eapply point_polar_cmp_safe_range_subrange_permutation
    with (l := pts_out_2) (sublo := retval + 1) (subhi := right_pre);
    try eassumption; lia.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_2_split_goal_3 : quicksort_polar_points_return_wit_2_split_goal_3.
Proof.
  unfold quicksort_polar_points_return_wit_2_split_goal_3.
  intros.
  entailer!.
  assert (Hsame1_full :
    point_same_outside_range pts_out_2 pts_out_3 left_pre right_pre).
  {
    eapply (point_same_outside_range_weaken
              pts_out_2 pts_out_3 (retval + 1) right_pre
      left_pre right_pre);
      [lia | lia | assumption].
  }
  change (point_same_outside_range pts_l pts_out_3 left_pre right_pre).
  eapply (point_same_outside_range_trans
            pts_l pts_out_2 pts_out_3 left_pre right_pre);
    [assumption | exact Hsame1_full].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_2_split_goal_4 : quicksort_polar_points_return_wit_2_split_goal_4.
Proof.
  unfold quicksort_polar_points_return_wit_2_split_goal_4.
  intros.
  entailer!.
  unfold point_permutation in *.
  eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_2 : quicksort_polar_points_return_wit_2.
Proof.
  open_generated_wit quicksort_polar_points_return_wit_2.
  intros.
  Exists pts_out_3.
  entailer!.
  - assert (Hpart3 :
      point_polar_partitioned_at (point_mk gx_pre gy_pre)
        pts_out_3 left_pre right_pre retval).
    {
      eapply point_polar_partitioned_at_preserved_by_right;
        [eassumption | lia | eassumption | lia | eassumption].
    }
    eapply point_sorted_range_from_right_boundary with (p := retval);
      [lia | lia | lia | exact Hpart3 | assumption].
  - eapply point_polar_cmp_safe_range_subrange_permutation
      with (l := pts_out_2) (sublo := retval + 1) (subhi := right_pre);
      try eassumption; lia.
  - assert (Hsame1_full :
      point_same_outside_range pts_out_2 pts_out_3 left_pre right_pre).
    {
      eapply (point_same_outside_range_weaken
                pts_out_2 pts_out_3 (retval + 1) right_pre
        left_pre right_pre);
        [lia | lia | assumption].
    }
    change (point_same_outside_range pts_l pts_out_3 left_pre right_pre).
    eapply (point_same_outside_range_trans
              pts_l pts_out_2 pts_out_3 left_pre right_pre);
      [assumption | exact Hsame1_full].
  - unfold point_permutation in *.
    eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_3_split_goal_1 : quicksort_polar_points_return_wit_3_split_goal_1.
Proof.
  unfold quicksort_polar_points_return_wit_3_split_goal_1.
  intros.
  entailer!.
  assert (Hpart3 :
    point_polar_partitioned_at (point_mk gx_pre gy_pre)
      pts_out_3 left_pre right_pre retval).
  {
    eapply point_polar_partitioned_at_preserved_by_left;
      [eassumption | lia | eassumption | lia | eassumption].
  }
  eapply point_sorted_range_from_left_boundary with (p := retval);
    [lia | lia | lia | exact Hpart3 | assumption].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_3_split_goal_2 : quicksort_polar_points_return_wit_3_split_goal_2.
Proof.
  unfold quicksort_polar_points_return_wit_3_split_goal_2.
  intros.
  entailer!.
  eapply point_polar_cmp_safe_range_subrange_permutation
    with (l := pts_out_2) (sublo := left_pre) (subhi := retval - 1);
    try eassumption; lia.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_3_split_goal_3 : quicksort_polar_points_return_wit_3_split_goal_3.
Proof.
  unfold quicksort_polar_points_return_wit_3_split_goal_3.
  intros.
  entailer!.
  assert (Hsame1_full :
    point_same_outside_range pts_out_2 pts_out_3 left_pre right_pre).
  {
    eapply (point_same_outside_range_weaken
              pts_out_2 pts_out_3 left_pre (retval - 1)
      left_pre right_pre);
      [lia | lia | assumption].
  }
  change (point_same_outside_range pts_l pts_out_3 left_pre right_pre).
  eapply (point_same_outside_range_trans
            pts_l pts_out_2 pts_out_3 left_pre right_pre);
    [assumption | exact Hsame1_full].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_3_split_goal_4 : quicksort_polar_points_return_wit_3_split_goal_4.
Proof.
  unfold quicksort_polar_points_return_wit_3_split_goal_4.
  intros.
  entailer!.
  unfold point_permutation in *.
  eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_3 : quicksort_polar_points_return_wit_3.
Proof.
  open_generated_wit quicksort_polar_points_return_wit_3.
  intros.
  Exists pts_out_3.
  entailer!.
  - assert (Hpart3 :
      point_polar_partitioned_at (point_mk gx_pre gy_pre)
        pts_out_3 left_pre right_pre retval).
    {
      eapply point_polar_partitioned_at_preserved_by_left;
        [eassumption | lia | eassumption | lia | eassumption].
    }
    eapply point_sorted_range_from_left_boundary with (p := retval);
      [lia | lia | lia | exact Hpart3 | assumption].
  - eapply point_polar_cmp_safe_range_subrange_permutation
      with (l := pts_out_2) (sublo := left_pre) (subhi := retval - 1);
      try eassumption; lia.
  - assert (Hsame1_full :
      point_same_outside_range pts_out_2 pts_out_3 left_pre right_pre).
    {
      eapply (point_same_outside_range_weaken
                pts_out_2 pts_out_3 left_pre (retval - 1)
        left_pre right_pre);
        [lia | lia | assumption].
    }
    change (point_same_outside_range pts_l pts_out_3 left_pre right_pre).
    eapply (point_same_outside_range_trans
              pts_l pts_out_2 pts_out_3 left_pre right_pre);
      [assumption | exact Hsame1_full].
  - unfold point_permutation in *.
    eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_4_split_goal_1 : quicksort_polar_points_return_wit_4_split_goal_1.
Proof.
  unfold quicksort_polar_points_return_wit_4_split_goal_1.
  intros.
  entailer!.
  eapply point_sorted_range_degenerate; lia.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_4_split_goal_2 : quicksort_polar_points_return_wit_4_split_goal_2.
Proof.
  unfold quicksort_polar_points_return_wit_4_split_goal_2.
  intros.
  entailer!.
  unfold point_same_outside_range.
  split; [reflexivity|]. intros; reflexivity.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_4_split_goal_3 : quicksort_polar_points_return_wit_4_split_goal_3.
Proof.
  unfold quicksort_polar_points_return_wit_4_split_goal_3.
  intros.
  entailer!.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_4 : quicksort_polar_points_return_wit_4.
Proof.
  open_generated_wit quicksort_polar_points_return_wit_4.
  intros.
  Exists pts_l.
  entailer!.
  - unfold point_sorted_range. intros.
    assert (i = j) as Hij.
    { lia. }
    subst.
    rewrite point_cmp_polar_refl. lia.
  - unfold point_same_outside_range.
    split; [reflexivity|]. intros; reflexivity.
Qed.

Lemma proof_of_quicksort_polar_points_partial_solve_wit_2_pure_split_goal_1 : quicksort_polar_points_partial_solve_wit_2_pure_split_goal_1.
Proof.
  unfold quicksort_polar_points_partial_solve_wit_2_pure_split_goal_1.
  intros.
  entailer!.
  unfold point_polar_cmp_safe_range in *.
  intros a b Ha Hb.
  apply PreH21; lia.
Qed.

Lemma proof_of_quicksort_polar_points_partial_solve_wit_2_pure : quicksort_polar_points_partial_solve_wit_2_pure.
Proof.
  unfold quicksort_polar_points_partial_solve_wit_2_pure; try left.
  intros.
  entailer!.
  unfold point_polar_cmp_safe_range in *.
  intros a b Ha Hb.
  apply PreH9; lia.
Qed.

Lemma proof_of_quicksort_polar_points_partial_solve_wit_3_pure_split_goal_1 : quicksort_polar_points_partial_solve_wit_3_pure_split_goal_1.
Proof.
  unfold quicksort_polar_points_partial_solve_wit_3_pure_split_goal_1.
  intros.
  entailer!.
  assert (Hsafe_full :
    point_polar_cmp_safe_range (point_mk gx_pre gy_pre)
      pts_out left_pre right_pre).
  {
    eapply point_polar_cmp_safe_range_subrange_permutation
      with (l := pts_out_2) (sublo := left_pre) (subhi := retval - 1);
      try eassumption; lia.
  }
  unfold point_polar_cmp_safe_range in *.
  intros a b Ha Hb.
  apply Hsafe_full; lia.
Qed.

Lemma proof_of_quicksort_polar_points_partial_solve_wit_3_pure : quicksort_polar_points_partial_solve_wit_3_pure.
Proof.
  unfold quicksort_polar_points_partial_solve_wit_3_pure; try left.
  intros.
  entailer!.
  assert (Hsafe_full :
    point_polar_cmp_safe_range (point_mk gx_pre gy_pre)
      pts_out left_pre right_pre).
  {
    eapply point_polar_cmp_safe_range_subrange_permutation
      with (l := pts_out_2) (sublo := left_pre) (subhi := retval - 1);
      try eassumption; lia.
  }
  unfold point_polar_cmp_safe_range in *.
  intros a b Ha Hb.
  apply Hsafe_full; lia.
Qed.

Lemma proof_of_quicksort_polar_points_partial_solve_wit_4_pure_split_goal_1 : quicksort_polar_points_partial_solve_wit_4_pure_split_goal_1.
Proof.
  unfold quicksort_polar_points_partial_solve_wit_4_pure_split_goal_1.
  intros.
  entailer!.
  unfold point_polar_cmp_safe_range in *.
  intros a b Ha Hb.
  apply PreH22; lia.
Qed.

Lemma proof_of_quicksort_polar_points_partial_solve_wit_4_pure : quicksort_polar_points_partial_solve_wit_4_pure.
Proof.
  unfold quicksort_polar_points_partial_solve_wit_4_pure; try left.
  intros.
  entailer!.
  unfold point_polar_cmp_safe_range in *.
  intros a b Ha Hb.
  apply PreH10; lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_1_split_goal_1 : dedup_points_and_find_leftmost_entail_wit_1_split_goal_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_1_split_goal_1.
  intros.
  entailer!.
  unfold point_dedup_scan_inv, point_no_dup_prefix,
    point_prefix_represents_range.
  repeat split; try lia; try apply Permutation_refl;
    try (intros; lia);
    try (left; reflexivity).
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_1 : dedup_points_and_find_leftmost_entail_wit_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_1.
  left.
  intros.
  Exists pivot0 pts_l.
  entailer!.
  unfold point_dedup_scan_inv, point_no_dup_prefix,
    point_prefix_represents_range.
  repeat split; try lia; try apply Permutation_refl;
    try (intros; lia);
    try (left; reflexivity).
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_2_split_goal_1 : dedup_points_and_find_leftmost_entail_wit_2_split_goal_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_2_split_goal_1; try left.
  intros.
  entailer!;
    try (unfold point_cmp_leftdown, point_cmp_polar, point_cmp_xy,
      point_mk, point_cross, point_cross_by_value, point_dot_by_value,
      point_at_mid, point_colinear in *; simpl in *);
    try (unfold point_bound, Point_Order.point_bound,
      point_in_bound, Point_Order.point_in_bound, points_in_bound,
      point_polar_cmp_safe_pair, point_same, point_no_dup_prefix,
      point_prefix_has_same, point_dedup_inner_scan_inv,
      point_prefix_represents_range, point_unique_prefix_represents_all,
      point_dedup_scan_inv, point_dedup_result,
      point_dedup_hull_result in *; simpl in *);
    try (repeat match goal with H : _ /\ _ |- _ => destruct H end);
    try (repeat match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
    | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b); try nia
    | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b); try nia
    end);
    try lia; try nia; eauto.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_2 : dedup_points_and_find_leftmost_entail_wit_2.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_2.
  left.
  intros.
  Exists pivot_cur_2 pts_cur_2.
  entailer!.
  unfold point_dedup_inner_scan_inv.
  left; split; [reflexivity | intros; lia].
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_3_1_split_goal_1 : dedup_points_and_find_leftmost_entail_wit_3_1_split_goal_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_3_1_split_goal_1.
  intros.
  entailer!.
  unfold point_dedup_inner_scan_inv in *.
  destruct PreH17 as [[Hdup Hnone] | [Hdup Hsame]].
  - left. split; [exact Hdup |].
    intros k Hk Hpt.
    assert (Hcase : k < scan \/ k = scan) by lia.
    destruct Hcase as [Hlt | ->].
    + apply (Hnone k); [lia | exact Hpt].
    + unfold point_same in Hpt.
      destruct Hpt as [Hx _].
      rewrite (Znth_indep pts_cur_2 scan default_point __default_Point) in Hx by lia.
      rewrite (Znth_indep pts_cur_2 read default_point __default_Point) in Hx by lia.
      exact (PreH1 Hx).
  - right. split; assumption.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_3_1 : dedup_points_and_find_leftmost_entail_wit_3_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_3_1.
  left.
  intros.
  Exists pivot_cur_2 pts_cur_2.
  entailer!.
  unfold point_dedup_inner_scan_inv in *.
  destruct PreH17 as [[Hdup Hnone] | [Hdup Hsame]].
  - left. split; [exact Hdup |].
    intros k Hk Hpt.
    assert (Hcase : k < scan \/ k = scan) by lia.
    destruct Hcase as [Hlt | ->].
    + apply (Hnone k); [lia | exact Hpt].
    + unfold point_same in Hpt.
      destruct Hpt as [Hx _].
      rewrite (Znth_indep pts_cur_2 scan default_point __default_Point) in Hx by lia.
      rewrite (Znth_indep pts_cur_2 read default_point __default_Point) in Hx by lia.
      exact (PreH1 Hx).
  - right. split; assumption.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_3_2_split_goal_1 : dedup_points_and_find_leftmost_entail_wit_3_2_split_goal_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_3_2_split_goal_1.
  intros.
  entailer!.
  unfold point_dedup_inner_scan_inv in *.
  destruct PreH18 as [[Hdup Hnone] | [Hdup Hsame]].
  - left. split; [exact Hdup |].
    intros k Hk Hpt.
    assert (Hcase : k < scan \/ k = scan) by lia.
    destruct Hcase as [Hlt | ->].
    + apply (Hnone k); [lia | exact Hpt].
    + unfold point_same in Hpt.
      destruct Hpt as [_ Hy].
      rewrite (Znth_indep pts_cur_2 scan default_point __default_Point) in Hy by lia.
      rewrite (Znth_indep pts_cur_2 read default_point __default_Point) in Hy by lia.
      exact (PreH1 Hy).
  - right. split; assumption.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_3_2 : dedup_points_and_find_leftmost_entail_wit_3_2.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_3_2.
  left.
  intros.
  Exists pivot_cur_2 pts_cur_2.
  entailer!.
  unfold point_dedup_inner_scan_inv in *.
  destruct PreH18 as [[Hdup Hnone] | [Hdup Hsame]].
  - left. split; [exact Hdup |].
    intros k Hk Hpt.
    assert (Hcase : k < scan \/ k = scan) by lia.
    destruct Hcase as [Hlt | ->].
    + apply (Hnone k); [lia | exact Hpt].
    + unfold point_same in Hpt.
      destruct Hpt as [_ Hy].
      rewrite (Znth_indep pts_cur_2 scan default_point __default_Point) in Hy by lia.
      rewrite (Znth_indep pts_cur_2 read default_point __default_Point) in Hy by lia.
      exact (PreH1 Hy).
  - right. split; assumption.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_4_1 : dedup_points_and_find_leftmost_entail_wit_4_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_4_1.
  intros.
  assert (Hnodup_next :
    point_no_dup_prefix pts_cur_2 (unique_n + 1)).
  {
    eapply point_no_dup_prefix_extend_from_inner; eauto; lia.
  }
  assert (Hrepr_next :
    point_prefix_represents_range pts_cur_2
      (unique_n + 1) (unique_n + 1) (read + 1)).
  {
    subst read.
    unfold point_dedup_scan_inv in PreH16.
    destruct PreH16 as [Hlen [Huniq_read [Hread_len
      [Hperm [Hnodup [Hrepr Hpiv]]]]]].
    unfold point_prefix_represents_range in *.
    destruct Hrepr as [Huniq_lo [Hlo_hi Hrepr]].
    repeat split; lia.
  }
  unfold point_dedup_scan_inv in PreH16.
  destruct PreH16 as [Hlen [Huniq_read [Hread_len
    [Hperm [Hnodup [Hrepr Hpiv]]]]]].
  destruct Hpiv as [Hempty | Hleft].
  - Left.
    Exists pivot_cur_2 pts_cur_2.
    entailer!.
  - Right.
    Exists pivot_cur_2 pts_cur_2.
    entailer!.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_4_2 : dedup_points_and_find_leftmost_entail_wit_4_2.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_4_2.
  intros.
  assert (Hswap_len :
    Zlength (point_swap pts_cur_2 unique_n read) = n_pre).
  {
    rewrite Zlength_point_swap; lia.
  }
  assert (Hread_len : read < Zlength pts_cur_2) by lia.
  assert (Huniq_len : unique_n < Zlength pts_cur_2) by lia.
  assert (Hperm_swap :
    point_permutation pts_l (point_swap pts_cur_2 unique_n read)).
  {
    pose proof PreH17 as Hscan_perm.
    unfold point_dedup_scan_inv in Hscan_perm.
    destruct Hscan_perm as [_ [_ [_ [Hperm_cur _]]]].
    eapply Permutation_trans.
    - exact Hperm_cur.
    - apply point_swap_permutation; lia.
  }
  assert (Hbound_swap : points_in_bound (point_swap pts_cur_2 unique_n read)).
  {
    apply points_in_bound_point_swap; [exact PreH16 | lia | lia].
  }
  assert (Hnodup_swap :
    point_no_dup_prefix (point_swap pts_cur_2 unique_n read) (unique_n + 1)).
  {
    eapply point_no_dup_prefix_point_swap_extend_from_inner; eauto; lia.
  }
  assert (Hrepr_swap :
    point_prefix_represents_range (point_swap pts_cur_2 unique_n read)
      (unique_n + 1) (unique_n + 1) (read + 1)).
  {
    eapply point_prefix_represents_range_point_swap_accept; eauto; lia.
  }
  unfold point_dedup_scan_inv in PreH17.
  destruct PreH17 as [Hlen [Huniq_read [Hread_le
    [Hperm [Hnodup [Hrepr Hpiv]]]]]].
  destruct Hpiv as [Hempty | Hleft].
  - Left.
    Exists pivot_cur_2 (point_swap pts_cur_2 unique_n read).
    entailer!.
  - Right.
    assert (Hleft_swap :
      point_leftmost_prefix (point_swap pts_cur_2 unique_n read)
        pivot_cur_2 unique_n).
    {
      eapply point_leftmost_prefix_point_swap_preserve_before; eauto; lia.
    }
    Exists pivot_cur_2 (point_swap pts_cur_2 unique_n read).
    entailer!.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_1_split_goal_1 : dedup_points_and_find_leftmost_entail_wit_5_1_split_goal_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_1_split_goal_1.
  intros.
  entailer!.
  eapply point_dedup_accept_transition_scan_inv; eauto; try lia.
  subst unique_n.
  apply point_leftmost_prefix_init; lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_1 : dedup_points_and_find_leftmost_entail_wit_5_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_1.
  left.
  intros.
  Exists unique_n pts_cur_2.
  entailer!.
  eapply point_dedup_accept_transition_scan_inv; eauto; try lia.
  subst unique_n.
  apply point_leftmost_prefix_init; lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_2_split_goal_1 : dedup_points_and_find_leftmost_entail_wit_5_2_split_goal_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_2_split_goal_1.
  intros.
  entailer!.
  eapply point_dedup_accept_transition_scan_inv; eauto; try lia.
  subst unique_n.
  apply point_leftmost_prefix_init; lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_2 : dedup_points_and_find_leftmost_entail_wit_5_2.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_2.
  left.
  intros.
  Exists unique_n pts_cur_2.
  entailer!.
  eapply point_dedup_accept_transition_scan_inv; eauto; try lia.
  subst unique_n.
  apply point_leftmost_prefix_init; lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_3_split_goal_1 : dedup_points_and_find_leftmost_entail_wit_5_3_split_goal_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_3_split_goal_1.
  intros.
  entailer!.
  eapply point_dedup_accept_transition_scan_inv; eauto; try lia.
  eapply point_leftmost_prefix_step_update; eauto; try lia.
  apply point_cmp_leftdown_lt_point_leftdown.
  repeat rewrite (Znth_indep pts_cur_2 unique_n default_point __default_Point) by lia.
  repeat rewrite (Znth_indep pts_cur_2 pivot_cur_2 default_point __default_Point) by lia.
  rewrite PreH2 in PreH1.
  repeat rewrite (Znth_indep pts_cur_2 unique_n default_point __default_Point) in PreH1 by lia.
  repeat rewrite (Znth_indep pts_cur_2 pivot_cur_2 default_point __default_Point) in PreH1 by lia.
  repeat rewrite point_mk_eta in PreH1.
  lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_3 : dedup_points_and_find_leftmost_entail_wit_5_3.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_3.
  left.
  intros.
  Exists unique_n pts_cur_2.
  entailer!.
  eapply point_dedup_accept_transition_scan_inv; eauto; try lia.
  eapply point_leftmost_prefix_step_update; eauto; try lia.
  apply point_cmp_leftdown_lt_point_leftdown.
  repeat rewrite (Znth_indep pts_cur_2 unique_n default_point __default_Point) by lia.
  repeat rewrite (Znth_indep pts_cur_2 pivot_cur_2 default_point __default_Point) by lia.
  rewrite PreH2 in PreH1.
  repeat rewrite (Znth_indep pts_cur_2 unique_n default_point __default_Point) in PreH1 by lia.
  repeat rewrite (Znth_indep pts_cur_2 pivot_cur_2 default_point __default_Point) in PreH1 by lia.
  repeat rewrite point_mk_eta in PreH1.
  lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_4_split_goal_1 : dedup_points_and_find_leftmost_entail_wit_5_4_split_goal_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_4_split_goal_1.
  intros.
  entailer!.
  eapply point_dedup_accept_transition_scan_inv; eauto; try lia.
  eapply point_leftmost_prefix_step_keep; eauto; try lia.
  apply point_cmp_leftdown_nonneg_point_leftdown_flip.
  repeat rewrite (Znth_indep pts_cur_2 unique_n default_point __default_Point) by lia.
  repeat rewrite (Znth_indep pts_cur_2 pivot_cur_2 default_point __default_Point) by lia.
  rewrite PreH2 in PreH1.
  repeat rewrite (Znth_indep pts_cur_2 unique_n default_point __default_Point) in PreH1 by lia.
  repeat rewrite (Znth_indep pts_cur_2 pivot_cur_2 default_point __default_Point) in PreH1 by lia.
  repeat rewrite point_mk_eta in PreH1.
  lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_4 : dedup_points_and_find_leftmost_entail_wit_5_4.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_4.
  left.
  intros.
  Exists pivot_cur_2 pts_cur_2.
  entailer!.
  eapply point_dedup_accept_transition_scan_inv; eauto; try lia.
  eapply point_leftmost_prefix_step_keep; eauto; try lia.
  apply point_cmp_leftdown_nonneg_point_leftdown_flip.
  repeat rewrite (Znth_indep pts_cur_2 unique_n default_point __default_Point) by lia.
  repeat rewrite (Znth_indep pts_cur_2 pivot_cur_2 default_point __default_Point) by lia.
  rewrite PreH2 in PreH1.
  repeat rewrite (Znth_indep pts_cur_2 unique_n default_point __default_Point) in PreH1 by lia.
  repeat rewrite (Znth_indep pts_cur_2 pivot_cur_2 default_point __default_Point) in PreH1 by lia.
  repeat rewrite point_mk_eta in PreH1.
  lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_5_split_goal_1 : dedup_points_and_find_leftmost_entail_wit_5_5_split_goal_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_5_split_goal_1.
  intros.
  entailer!.
  eapply point_dedup_duplicate_seen_advance_scan_inv; eauto; lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_5 : dedup_points_and_find_leftmost_entail_wit_5_5.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_5.
  left.
  intros.
  Exists pivot_cur_2 pts_cur_2.
  entailer!.
  eapply point_dedup_duplicate_seen_advance_scan_inv; eauto; lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_6_split_goal_1 : dedup_points_and_find_leftmost_entail_wit_5_6_split_goal_1.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_6_split_goal_1.
  intros.
  assert (Hsame :
    point_same (Znth scan pts_cur_2 default_point)
      (Znth read pts_cur_2 default_point)).
  {
    unfold point_same.
    split.
    - rewrite (Znth_indep pts_cur_2 scan default_point __default_Point) by lia.
      rewrite (Znth_indep pts_cur_2 read default_point __default_Point) by lia.
      exact PreH2.
    - rewrite (Znth_indep pts_cur_2 scan default_point __default_Point) by lia.
      rewrite (Znth_indep pts_cur_2 read default_point __default_Point) by lia.
      exact PreH1.
  }
  entailer!.
  eapply point_dedup_duplicate_advance_scan_inv; eauto; lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_entail_wit_5_6 : dedup_points_and_find_leftmost_entail_wit_5_6.
Proof.
  unfold dedup_points_and_find_leftmost_entail_wit_5_6.
  left.
  intros.
  assert (Hsame :
    point_same (Znth scan pts_cur_2 default_point)
      (Znth read pts_cur_2 default_point)).
  {
    unfold point_same.
    split.
    - rewrite (Znth_indep pts_cur_2 scan default_point __default_Point) by lia.
      rewrite (Znth_indep pts_cur_2 read default_point __default_Point) by lia.
      exact PreH2.
    - rewrite (Znth_indep pts_cur_2 scan default_point __default_Point) by lia.
      rewrite (Znth_indep pts_cur_2 read default_point __default_Point) by lia.
      exact PreH1.
  }
  Exists pivot_cur_2 pts_cur_2.
  entailer!.
  eapply point_dedup_duplicate_advance_scan_inv; eauto; lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_return_wit_1_split_goal_1 : dedup_points_and_find_leftmost_return_wit_1_split_goal_1.
Proof.
  unfold dedup_points_and_find_leftmost_return_wit_1_split_goal_1; try left.
  intros.
  pose proof (point_dedup_scan_inv_finish_result
    pts_l pts_cur read unique_n pivot_cur PreH13) as [Hresult _];
    try lia.
  entailer!.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_return_wit_1_split_goal_2 : dedup_points_and_find_leftmost_return_wit_1_split_goal_2.
Proof.
  unfold dedup_points_and_find_leftmost_return_wit_1_split_goal_2; try left.
  intros.
  pose proof (point_dedup_scan_inv_finish_result
    pts_l pts_cur read unique_n pivot_cur PreH13) as [_ [Hpiv _]];
    try lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_return_wit_1_split_goal_3 : dedup_points_and_find_leftmost_return_wit_1_split_goal_3.
Proof.
  unfold dedup_points_and_find_leftmost_return_wit_1_split_goal_3; try left.
  intros.
  pose proof (point_dedup_scan_inv_finish_result
    pts_l pts_cur read unique_n pivot_cur PreH13) as [_ [_ H1le]];
    try lia.
Qed.

Lemma proof_of_dedup_points_and_find_leftmost_return_wit_1 : dedup_points_and_find_leftmost_return_wit_1.
Proof.
  unfold dedup_points_and_find_leftmost_return_wit_1; try left.
  intros.
  pose proof (point_dedup_scan_inv_finish_result
    pts_l pts_cur read unique_n pivot_cur PreH13) as [Hresult [Hpiv H1le]];
    try lia.
  Exists pivot_cur pts_cur.
  entailer!.
Qed.

Lemma proof_of_graham_scan_dedup_entail_wit_1_split_goal_1 : graham_scan_dedup_entail_wit_1_split_goal_1.
Proof.
  unfold graham_scan_dedup_entail_wit_1_split_goal_1.
  intros.
  eapply dedup_not_all_same_unique_n_ge_2; eauto.
Qed.

Lemma proof_of_graham_scan_dedup_entail_wit_1 : graham_scan_dedup_entail_wit_1.
Proof.
  unfold graham_scan_dedup_entail_wit_1.
  left.
  intros.
  Exists pts_out.
  entailer!;
    try eauto;
    try (eapply dedup_not_all_same_unique_n_ge_2; eauto).
Qed.

Lemma proof_of_graham_scan_dedup_entail_wit_2_1 : graham_scan_dedup_entail_wit_2_1.
Proof.
  unfold graham_scan_dedup_entail_wit_2_1.
  right.
  intros.
  subst pivot_out.
  pose proof PreH9 as Hresult.
  destruct PreH9 as [Hscan [_ [Hleft _]]].
  unfold point_dedup_scan_inv in Hscan.
  destruct Hscan as [_ [_ [_ [_ [Hnodup _]]]]].
  assert (Hleft_sub :
    leftmost
      (point_mk (point_x (Znth 0 pts_dedup __default_Point))
        (point_y (Znth 0 pts_dedup __default_Point)))
      (sublist 0 unique_n pts_dedup)).
  {
    rewrite point_mk_eta.
    rewrite (Znth_indep pts_dedup 0 __default_Point default_point) by lia.
    unfold point_leftmost_prefix in Hleft.
    destruct Hleft as [_ [Hretval_len Hmin]].
    unfold leftmost.
    apply Forall_Znth_intro with (d := default_point).
    intros i Hi.
    rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia.
    replace (i + 0) with i by lia.
    apply Hmin.
    lia.
  }
  Exists pts_dedup.
  repeat rewrite point_swap_0_0.
  sep_apply_l_atomic (PointArray.full_split_to_seg pts_pre unique_n n_pre pts_dedup).
  1:{ entailer!. }
  sep_apply_l_atomic (PointArray.seg_to_full pts_pre 0 unique_n
    (sublist 0 unique_n pts_dedup)).
  replace (pts_pre + 0 * sizeof("Point")) with pts_pre by lia.
  replace (unique_n - 0) with unique_n by lia.
  entailer!;
    try (rewrite Zlength_sublist; lia);
    try (eapply points_in_bound_sublist; eauto; lia);
    try (eapply points_in_bound_Znth_point_mk; eauto; lia);
    try exact Hresult;
    try exact Hnodup;
    try exact Hleft_sub;
    try lia; try nia; eauto.
  unfold point_polar_cmp_safe_range.
  intros i j Hi Hj.
  unfold point_polar_cmp_safe_pair.
  rewrite (Znth_indep pts_dedup 0 __default_Point default_point) by lia.
  rewrite point_mk_eta.
  rewrite !Znth_sublist by lia.
  replace (i + 0) with i by lia.
  replace (j + 0) with j by lia.
  intros Hcol Hmid.
  unfold point_no_dup_prefix in Hnodup.
  destruct Hnodup as [_ Hnodup_no].
  destruct (Z.eq_dec i j) as [Hij_eq | Hij_neq].
  - subst j.
    apply point_cmp_xy_eq; reflexivity.
  - assert (Hnot_pivot_i :
      ~ point_same (Znth 0 pts_dedup default_point)
        (Znth i pts_dedup default_point)).
    { apply Hnodup_no; lia. }
    destruct (Znth 0 pts_dedup default_point) as [gx gy] eqn:Hgp.
    destruct (Znth i pts_dedup default_point) as [ax ay] eqn:Ha.
    destruct (Znth j pts_dedup default_point) as [bx by0] eqn:Hb.
    unfold point_colinear in Hcol.
    rewrite point_cross_unfold in Hcol.
    simpl in Hcol.
    unfold point_at_mid in Hmid.
    rewrite point_dot_unfold in Hmid.
    simpl in Hmid.
    change ((ax - gx) * (by0 - gy) - (ay - gy) * (bx - gx) = 0)
      in Hcol.
    change ((bx - ax) * (gx - ax) + (by0 - ay) * (gy - ay) = 0)
      in Hmid.
    assert (Hcross' :
      (ax - gx) * (by0 - ay) - (ay - gy) * (bx - ax) = 0).
    {
      replace ((ax - gx) * (by0 - ay) - (ay - gy) * (bx - ax))
        with ((ax - gx) * (by0 - gy) - (ay - gy) * (bx - gx))
        by ring.
      exact Hcol.
    }
    assert (Hdot' :
      (bx - ax) * (ax - gx) + (by0 - ay) * (ay - gy) = 0).
    {
      replace ((bx - ax) * (ax - gx) + (by0 - ay) * (ay - gy))
        with (- ((bx - ax) * (gx - ax) + (by0 - ay) * (gy - ay)))
        by ring.
      lia.
    }
    assert (Hnorm_pos :
      0 < (ax - gx) * (ax - gx) + (ay - gy) * (ay - gy)).
    {
      pose proof (Z.square_nonneg (ax - gx)).
      pose proof (Z.square_nonneg (ay - gy)).
      assert (ax <> gx \/ ay <> gy).
      {
        destruct (Z.eq_dec ax gx) as [Hax | Hax];
          destruct (Z.eq_dec ay gy) as [Hay | Hay]; try tauto.
        exfalso; apply Hnot_pivot_i.
        unfold point_same.
        simpl.
        split; symmetry; assumption.
      }
      nia.
    }
    set (diff := (bx - ax) * (bx - ax) + (by0 - ay) * (by0 - ay)).
    set (norm := (ax - gx) * (ax - gx) + (ay - gy) * (ay - gy)).
    assert (Hid :
      diff * norm =
      ((bx - ax) * (ax - gx) + (by0 - ay) * (ay - gy)) *
      ((bx - ax) * (ax - gx) + (by0 - ay) * (ay - gy)) +
      ((ax - gx) * (by0 - ay) - (ay - gy) * (bx - ax)) *
      ((ax - gx) * (by0 - ay) - (ay - gy) * (bx - ax))).
    { unfold diff, norm. ring. }
    rewrite Hdot', Hcross' in Hid.
    assert (Hprod_zero : diff * norm = 0) by lia.
    assert (Hdiff_nonneg : 0 <= diff).
    {
      unfold diff.
      pose proof (Z.square_nonneg (bx - ax)).
      pose proof (Z.square_nonneg (by0 - ay)).
      lia.
    }
    assert (Hnorm_pos' : 0 < norm) by (unfold norm; exact Hnorm_pos).
    assert (Hdiff_zero : diff = 0).
    {
      destruct (Z.eq_dec diff 0) as [Hz | Hnz]; [exact Hz |].
      assert (0 < diff) by lia.
      pose proof (Z.mul_pos_pos diff norm ltac:(lia) ltac:(lia)).
      lia.
    }
    unfold diff in Hdiff_zero.
    assert (bx = ax).
    {
      pose proof (Z.square_nonneg (bx - ax)).
      pose proof (Z.square_nonneg (by0 - ay)).
      nia.
    }
    assert (by0 = ay).
    {
      pose proof (Z.square_nonneg (bx - ax)).
      pose proof (Z.square_nonneg (by0 - ay)).
      nia.
    }
    subst bx by0.
    apply point_cmp_xy_eq; reflexivity.
Qed.

Lemma proof_of_graham_scan_dedup_entail_wit_2_2 : graham_scan_dedup_entail_wit_2_2.
Proof.
  unfold graham_scan_dedup_entail_wit_2_2.
  right.
  intros.
  pose proof PreH10 as Hresult.
  destruct PreH10 as [Hscan [_ [Hleft _]]].
  unfold point_dedup_scan_inv in Hscan.
  destruct Hscan as [_ [_ [_ [_ [Hnodup _]]]]].
  set (pts_pivoted := point_swap pts_dedup 0 pivot_out).
  assert (Hlen_pivoted : Zlength pts_pivoted = n_pre).
  {
    unfold pts_pivoted.
    rewrite Zlength_point_swap.
    lia.
  }
  assert (Hbound_pivoted : points_in_bound pts_pivoted).
  {
    unfold pts_pivoted.
    eapply points_in_bound_point_swap; eauto; lia.
  }
  assert (Hbound_prefix : points_in_bound (sublist 0 unique_n pts_pivoted)).
  {
    eapply points_in_bound_sublist; eauto; lia.
  }
  assert (Hpivot_bound :
    point_in_bound
      (point_mk (point_x (Znth 0 pts_pivoted __default_Point))
        (point_y (Znth 0 pts_pivoted __default_Point)))).
  {
    eapply points_in_bound_Znth_point_mk; eauto.
    rewrite Hlen_pivoted.
    lia.
  }
  assert (Hlookup : forall k,
    0 <= k < unique_n ->
    exists k',
      0 <= k' < unique_n /\
      Znth k pts_pivoted default_point = Znth k' pts_dedup default_point /\
      ((k = 0 /\ k' = pivot_out) \/
       (k = pivot_out /\ k' = 0) \/
       (k <> 0 /\ k <> pivot_out /\ k' = k))).
  {
    intros k Hk.
    unfold pts_pivoted.
    destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
    - subst k.
      exists pivot_out.
      split; [lia |].
      split.
      + apply point_swap_Znth_left_index; lia.
      + left. split; reflexivity.
    - destruct (Z.eq_dec k pivot_out) as [Hkp | Hkp].
      + subst k.
        exists 0.
        split; [lia |].
        split.
        * apply point_swap_Znth_right_index; lia.
        * right. left. split; reflexivity.
      + exists k.
        split; [lia |].
        split.
        * apply point_swap_Znth_other_index; lia.
        * right. right. repeat split; auto.
  }
  assert (Hnodup_pivoted : point_no_dup_prefix pts_pivoted unique_n).
  {
    unfold point_no_dup_prefix in *.
    destruct Hnodup as [_ Hnodup_no].
    split; [rewrite Hlen_pivoted; lia |].
    intros i j Hij Hj Hsame.
    destruct (Hlookup i ltac:(lia)) as [i' [Hi' [Hi_eq Hi_case]]].
    destruct (Hlookup j ltac:(lia)) as [j' [Hj' [Hj_eq Hj_case]]].
    rewrite Hi_eq in Hsame.
    rewrite Hj_eq in Hsame.
    assert (Hij'_neq : i' <> j').
    {
      destruct Hi_case as [[Hi0 Hi_map] | [[Hip Hi_map] | [Hi0 [Hip Hi_map]]]];
      destruct Hj_case as [[Hj0 Hj_map] | [[Hjp Hj_map] | [Hj0 [Hjp Hj_map]]]];
      subst; lia.
    }
    destruct (Z_lt_ge_dec i' j') as [Hlt | Hge].
    - exact ((Hnodup_no i' j' ltac:(lia) ltac:(lia)) Hsame).
    - assert (Hlt : j' < i') by lia.
      apply (Hnodup_no j' i' ltac:(lia) ltac:(lia)).
      unfold point_same in *.
      destruct Hsame as [Hsame_x Hsame_y].
      split; symmetry; assumption.
  }
  assert (Hleft_sub :
    leftmost
      (point_mk (point_x (Znth 0 pts_pivoted __default_Point))
        (point_y (Znth 0 pts_pivoted __default_Point)))
      (sublist 0 unique_n pts_pivoted)).
  {
    rewrite point_mk_eta.
    rewrite (Znth_indep pts_pivoted 0 __default_Point default_point)
      by (rewrite Hlen_pivoted; lia).
    unfold point_leftmost_prefix in Hleft.
    destruct Hleft as [_ [_ Hmin]].
    unfold leftmost.
    apply Forall_Znth_intro with (d := default_point).
    intros k Hk.
    rewrite Zlength_sublist in Hk by (rewrite Hlen_pivoted; lia).
    rewrite Znth_sublist by lia.
    replace (k + 0) with k by lia.
    unfold pts_pivoted.
    rewrite point_swap_Znth_left_index by lia.
    destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
    - subst k.
      rewrite point_swap_Znth_left_index by lia.
      apply Hmin; lia.
    - destruct (Z.eq_dec k pivot_out) as [Hkp | Hkp].
      + subst k.
        rewrite point_swap_Znth_right_index by lia.
        apply Hmin; lia.
      + rewrite point_swap_Znth_other_index by lia.
        apply Hmin; lia.
  }
  assert (Hpolar_safe :
    point_polar_cmp_safe_range
      (point_mk (point_x (Znth 0 pts_pivoted __default_Point))
        (point_y (Znth 0 pts_pivoted __default_Point)))
      (sublist 0 unique_n pts_pivoted) 1 (unique_n - 1)).
  {
    unfold point_polar_cmp_safe_range.
    intros i j Hi Hj.
    unfold point_polar_cmp_safe_pair.
    rewrite (Znth_indep pts_pivoted 0 __default_Point default_point)
      by (rewrite Hlen_pivoted; lia).
    rewrite point_mk_eta.
    rewrite !Znth_sublist by lia.
    replace (i + 0) with i by lia.
    replace (j + 0) with j by lia.
    intros Hcol Hmid.
    unfold point_no_dup_prefix in Hnodup_pivoted.
    destruct Hnodup_pivoted as [_ Hnodup_no].
    destruct (Z.eq_dec i j) as [Hij_eq | Hij_neq].
    - subst j.
      apply point_cmp_xy_eq; reflexivity.
    - assert (Hnot_pivot_i :
        ~ point_same (Znth 0 pts_pivoted default_point)
          (Znth i pts_pivoted default_point)).
      { apply Hnodup_no; lia. }
      destruct (Znth 0 pts_pivoted default_point) as [gx gy] eqn:Hgp.
      destruct (Znth i pts_pivoted default_point) as [ax ay] eqn:Ha.
      destruct (Znth j pts_pivoted default_point) as [bx by0] eqn:Hb.
      unfold point_colinear in Hcol.
      rewrite point_cross_unfold in Hcol.
      simpl in Hcol.
      unfold point_at_mid in Hmid.
      rewrite point_dot_unfold in Hmid.
      simpl in Hmid.
      change ((ax - gx) * (by0 - gy) - (ay - gy) * (bx - gx) = 0)
        in Hcol.
      change ((bx - ax) * (gx - ax) + (by0 - ay) * (gy - ay) = 0)
        in Hmid.
      assert (Hcross' :
        (ax - gx) * (by0 - ay) - (ay - gy) * (bx - ax) = 0).
      {
        replace ((ax - gx) * (by0 - ay) - (ay - gy) * (bx - ax))
          with ((ax - gx) * (by0 - gy) - (ay - gy) * (bx - gx))
          by ring.
        exact Hcol.
      }
      assert (Hdot' :
        (bx - ax) * (ax - gx) + (by0 - ay) * (ay - gy) = 0).
      {
        replace ((bx - ax) * (ax - gx) + (by0 - ay) * (ay - gy))
          with (- ((bx - ax) * (gx - ax) + (by0 - ay) * (gy - ay)))
          by ring.
        lia.
      }
      assert (Hnorm_pos :
        0 < (ax - gx) * (ax - gx) + (ay - gy) * (ay - gy)).
      {
        pose proof (Z.square_nonneg (ax - gx)).
        pose proof (Z.square_nonneg (ay - gy)).
        assert (ax <> gx \/ ay <> gy).
        {
          destruct (Z.eq_dec ax gx) as [Hax | Hax];
            destruct (Z.eq_dec ay gy) as [Hay | Hay]; try tauto.
          exfalso; apply Hnot_pivot_i.
          unfold point_same.
          simpl.
          split; symmetry; assumption.
        }
        nia.
      }
      set (diff := (bx - ax) * (bx - ax) + (by0 - ay) * (by0 - ay)).
      set (norm := (ax - gx) * (ax - gx) + (ay - gy) * (ay - gy)).
      assert (Hid :
        diff * norm =
        ((bx - ax) * (ax - gx) + (by0 - ay) * (ay - gy)) *
        ((bx - ax) * (ax - gx) + (by0 - ay) * (ay - gy)) +
        ((ax - gx) * (by0 - ay) - (ay - gy) * (bx - ax)) *
        ((ax - gx) * (by0 - ay) - (ay - gy) * (bx - ax))).
      { unfold diff, norm. ring. }
      rewrite Hdot', Hcross' in Hid.
      assert (Hprod_zero : diff * norm = 0) by lia.
      assert (Hdiff_nonneg : 0 <= diff).
      {
        unfold diff.
        pose proof (Z.square_nonneg (bx - ax)).
        pose proof (Z.square_nonneg (by0 - ay)).
        lia.
      }
      assert (Hnorm_pos' : 0 < norm) by (unfold norm; exact Hnorm_pos).
      assert (Hdiff_zero : diff = 0).
      {
        destruct (Z.eq_dec diff 0) as [Hz | Hnz]; [exact Hz |].
        assert (0 < diff) by lia.
        pose proof (Z.mul_pos_pos diff norm ltac:(lia) ltac:(lia)).
        lia.
      }
      unfold diff in Hdiff_zero.
      assert (bx = ax).
      {
        pose proof (Z.square_nonneg (bx - ax)).
        pose proof (Z.square_nonneg (by0 - ay)).
        nia.
      }
      assert (by0 = ay).
      {
        pose proof (Z.square_nonneg (bx - ax)).
        pose proof (Z.square_nonneg (by0 - ay)).
        nia.
      }
      subst bx by0.
      apply point_cmp_xy_eq; reflexivity.
  }
  Exists pts_dedup.
  fold pts_pivoted.
  sep_apply_l_atomic (PointArray.full_split_to_seg pts_pre unique_n n_pre pts_pivoted).
  1:{ entailer!. }
  sep_apply_l_atomic (PointArray.seg_to_full pts_pre 0 unique_n
    (sublist 0 unique_n pts_pivoted)).
  replace (pts_pre + 0 * sizeof("Point")) with pts_pre by lia.
  replace (unique_n - 0) with unique_n by lia.
  entailer!;
    try (rewrite Zlength_sublist; rewrite ?Hlen_pivoted; lia);
    try exact Hlen_pivoted;
    try exact Hbound_pivoted;
    try exact Hbound_prefix;
    try exact Hpivot_bound;
    try exact Hresult;
    try exact Hnodup_pivoted;
    try exact Hleft_sub;
    try exact Hpolar_safe;
    try lia; try nia; eauto.
Qed.

Lemma proof_of_graham_scan_dedup_entail_wit_3 : graham_scan_dedup_entail_wit_3.
Proof.
  unfold graham_scan_dedup_entail_wit_3.
  left.
  intros.
  assert (Hfirst_same :
    Znth 0 pts_out default_point = Znth 0 pts_pivot_2 default_point).
  {
    unfold point_same_outside_range in PreH5.
    destruct PreH5 as [_ Hsame_out].
    specialize (Hsame_out 0 ltac:(rewrite PreH18; lia) ltac:(left; lia)).
    rewrite PreH19 in Hsame_out.
    rewrite Znth_sublist in Hsame_out by lia.
    replace (0 + 0) with 0 in Hsame_out by lia.
    exact Hsame_out.
  }
  assert (Hfirst_x : point_x (Znth 0 pts_out __default_Point) = gx).
  {
    rewrite (Znth_indep pts_out 0 __default_Point default_point) by lia.
    rewrite Hfirst_same.
    rewrite <- (Znth_indep pts_pivot_2 0 __default_Point default_point)
      by lia.
    exact PreH29.
  }
  assert (Hfirst_y : point_y (Znth 0 pts_out __default_Point) = gy).
  {
    rewrite (Znth_indep pts_out 0 __default_Point default_point) by lia.
    rewrite Hfirst_same.
    rewrite <- (Znth_indep pts_pivot_2 0 __default_Point default_point)
      by lia.
    exact PreH30.
  }
  assert (Hpts_out_cons :
    pts_out = point_mk gx gy :: sublist 1 unique_n pts_out).
  {
    eapply point_list_cons_sublist_1_by_fields
      with (n := unique_n) (d := __default_Point).
    - exact PreH1.
    - lia.
    - reflexivity.
    - exact Hfirst_x.
    - exact Hfirst_y.
  }
  assert (Htail_bound : points_in_bound (sublist 1 unique_n pts_out)).
  {
    eapply points_in_bound_sublist; eauto; lia.
  }
  assert (Hpivot_bound : point_in_bound (point_mk gx gy)).
  {
    rewrite <- PreH14.
    exact PreH24.
  }
  assert (Htail_polar_sorted :
    point_polar_sorted (point_mk gx gy) (sublist 1 unique_n pts_out)).
  {
    eapply point_sorted_range_tail_point_polar_sorted; eauto.
  }
  assert (Hleft_rev_tail :
    leftmost (point_mk gx gy) (rev (sublist 1 unique_n pts_out))).
  {
    apply leftmost_rev.
    eapply leftmost_sublist; eauto; lia.
  }
  Exists suffix_2 (sublist 1 unique_n pts_out) unique_prefix_2 pts_out
    pts_dedup_2 pts_pivot_2 (point_mk gx gy).
  sep_apply_l_atomic (PointArray.full_split_to_missing_i pts_pre 0
    unique_n pts_out __default_Point).
  1:{ entailer!; lia. }
  change (StorePointAsElement.storeA pts_pre 0 (Znth 0 pts_out __default_Point))
    with (store_point (pts_pre + 0 * sizeof_Point)
      (Znth 0 pts_out __default_Point)).
  replace (pts_pre + 0 * sizeof_Point) with pts_pre by lia.
  replace (Znth 0 pts_out __default_Point) with (point_mk gx gy).
  2:{
    apply point_eq_by_xy; simpl; symmetry; assumption.
  }
  rewrite Hpts_out_cons at 1.
  sep_apply_l_atomic (PointArray.missing_i_to_seg_head pts_pre 0
    unique_n (point_mk gx gy) (sublist 1 unique_n pts_out)).
  sep_apply_l_atomic (PointArray.seg_to_full pts_pre 1 unique_n
    (sublist 1 unique_n pts_out)).
  replace (pts_pre + 1 * sizeof_Point)
    with (pts_pre + 1 * sizeof("Point")) by lia.
  sep_apply_l_atomic (PointArray.undef_full_split_to_undef_seg
    hull_pre unique_n n_pre).
  1:{ entailer!; lia. }
  replace (unique_n - 1 + 1) with unique_n by lia.
  entailer!;
    try (rewrite Zlength_sublist; lia);
    try exact PreH4;
    try exact PreH7;
    try exact PreH8;
    try exact PreH9;
    try exact PreH10;
    try exact PreH15;
    try exact PreH16;
    try exact PreH18;
    try exact PreH19;
    try exact PreH20;
    try exact PreH25;
    try exact Hfirst_x;
    try exact Hfirst_y;
    try exact Htail_bound;
    try exact Hpivot_bound;
    try exact Htail_polar_sorted;
    try exact Hleft_rev_tail;
    try lia; try nia; eauto.
Qed.

Lemma proof_of_graham_scan_dedup_entail_wit_4 : graham_scan_dedup_entail_wit_4.
Proof.
  unfold graham_scan_dedup_entail_wit_4.
  left.
  intros.
  subst tail.
  replace (unique_n - 1 + 1) with unique_n by lia.
  prop_apply (PointArray.undef_seg_valid hull_pre retval unique_n); Intros.
  assert (Hret_nonneg : 0 <= retval).
  {
    rewrite PreH1.
    apply Zlength_nonneg.
  }
  assert (Hpts_pivot_len : Zlength pts_pivot = n_pre).
  {
    rewrite PreH10.
    rewrite Zlength_point_swap.
    exact PreH11.
  }
  pose proof PreH22 as Hdedup.
  unfold point_dedup_result in Hdedup.
  destruct Hdedup as [Hscan [_ [Hleft Hall]]].
  unfold point_dedup_scan_inv in Hscan.
  destruct Hscan as [_ [_ [_ [Hperm_l_dedup _]]]].
  assert (Hpivot_bounds : 0 <= pivot_idx < unique_n).
  {
    unfold point_leftmost_prefix in Hleft.
    lia.
  }
  assert (Hsorted_cons : pts_sorted = pivot0 :: tail_sorted).
  {
    eapply point_list_cons_sublist_1_by_fields
      with (n := unique_n) (d := __default_Point).
    - exact PreH12.
    - lia.
    - exact PreH16.
    - rewrite PreH9. exact PreH28.
    - rewrite PreH9. exact PreH29.
  }
  unfold point_permutation in PreH24.
  assert (Hprefix_in_unique :
    forall j,
      0 <= j < unique_n ->
      In (Znth j pts_dedup default_point) unique_prefix).
  {
    intros j Hj.
    assert (Hj_len : 0 <= j < Zlength pts_dedup) by lia.
    assert (Hpiv_len : 0 <= pivot_idx < Zlength pts_dedup) by lia.
    destruct (Z.eq_dec j 0) as [Hj0 | Hj0].
    - subst j.
      assert (Hidx : 0 <= pivot_idx < Zlength unique_prefix) by lia.
      pose proof (Znth_In_range unique_prefix pivot_idx default_point Hidx)
        as Hin.
      replace (Znth pivot_idx unique_prefix default_point)
        with (Znth 0 pts_dedup default_point) in Hin.
      + exact Hin.
      + rewrite PreH15.
        rewrite Znth_sublist by lia.
        replace (pivot_idx + 0) with pivot_idx by lia.
        rewrite PreH10.
        symmetry.
        apply point_swap_Znth_right_index; lia.
    - destruct (Z.eq_dec j pivot_idx) as [Hjp | Hjp].
      + subst j.
        assert (Hidx : 0 <= 0 < Zlength unique_prefix) by lia.
        pose proof (Znth_In_range unique_prefix 0 default_point Hidx)
          as Hin.
        replace (Znth 0 unique_prefix default_point)
          with (Znth pivot_idx pts_dedup default_point) in Hin.
        * exact Hin.
        * rewrite PreH15.
          rewrite Znth_sublist by lia.
          replace (0 + 0) with 0 by lia.
          rewrite PreH10.
          symmetry.
          apply point_swap_Znth_left_index; lia.
      + assert (Hidx : 0 <= j < Zlength unique_prefix) by lia.
        pose proof (Znth_In_range unique_prefix j default_point Hidx)
          as Hin.
        replace (Znth j unique_prefix default_point)
          with (Znth j pts_dedup default_point) in Hin.
        * exact Hin.
        * rewrite PreH15.
          rewrite Znth_sublist by lia.
          replace (j + 0) with j by lia.
          rewrite PreH10.
          symmetry.
          apply point_swap_Znth_other_index; lia.
  }
  assert (Hprefix_in_base :
    forall j,
      0 <= j < unique_n ->
      In (Znth j pts_dedup default_point) (pivot0 :: tail_sorted)).
  {
    intros j Hj.
    assert (Hin_sorted : In (Znth j pts_dedup default_point) pts_sorted).
    {
      eapply Permutation_in.
      - exact PreH24.
      - apply Hprefix_in_unique. exact Hj.
    }
    rewrite Hsorted_cons in Hin_sorted.
    exact Hin_sorted.
  }
  assert (Hbase_bound : points_in_bound (pivot0 :: tail_sorted)).
  {
    unfold points_in_bound.
    constructor; assumption.
  }
  assert (Hbase_bound_forall :
    forall p, In p (pivot0 :: tail_sorted) -> point_in_bound p).
  {
    unfold points_in_bound in Hbase_bound.
    rewrite Forall_forall in Hbase_bound.
    exact Hbase_bound.
  }
  pose proof Hall as Hall_all.
  unfold point_unique_prefix_represents_all in Hall_all.
  destruct Hall_all as [_ Hall_all].
  assert (Hdedup_bound : points_in_bound pts_dedup).
  {
    unfold points_in_bound.
    apply Forall_Znth_intro with (d := default_point).
    intros k Hk.
    destruct (Hall_all k Hk) as [j [Hj Hsame]].
    assert (Hrep_bound :
      point_in_bound (Znth j pts_dedup default_point)).
    {
      apply Hbase_bound_forall.
      apply Hprefix_in_base.
      exact Hj.
    }
    assert (Hsame_eq :
      Znth k pts_dedup default_point = Znth j pts_dedup default_point).
    {
      unfold point_same in Hsame.
      destruct Hsame as [Hx Hy].
      apply point_eq_by_xy; symmetry; assumption.
    }
    rewrite Hsame_eq.
    exact Hrep_bound.
  }
  assert (Hpts_pivot_bound : points_in_bound pts_pivot).
  {
    rewrite PreH10.
    eapply points_in_bound_point_swap; eauto; lia.
  }
  assert (Hsuffix_bound : points_in_bound suffix).
  {
    rewrite PreH17.
    eapply points_in_bound_sublist; eauto.
    - lia.
    - rewrite Hpts_pivot_len. lia.
  }
  assert (Hpts_out_bound :
    points_in_bound ((pivot0 :: tail_sorted) ++ suffix)).
  {
    unfold points_in_bound.
    apply Forall_app.
    split.
    - exact Hbase_bound.
    - exact Hsuffix_bound.
  }
  assert (Hpts_out_len :
    Zlength ((pivot0 :: tail_sorted) ++ suffix) = n_pre).
  {
    rewrite Zlength_app, Zlength_cons.
    rewrite PreH14.
    rewrite PreH17.
    rewrite Zlength_sublist by lia.
    lia.
  }
  assert (Hcovered :
    forall q,
      In q pts_l ->
      exists r, In r (pivot0 :: tail_sorted) /\ q = r).
  {
    intros q Hqin.
    assert (Hq_dedup : In q pts_dedup).
    {
      eapply Permutation_in.
      - exact Hperm_l_dedup.
      - exact Hqin.
    }
    destruct (In_Znth_Zlength pts_dedup q default_point Hq_dedup)
      as [k [Hk Hkq]].
    destruct (Hall_all k Hk) as [j [Hj Hsame]].
    exists (Znth j pts_dedup default_point).
    split.
    - apply Hprefix_in_base. exact Hj.
    - rewrite <- Hkq.
      unfold point_same in Hsame.
      destruct Hsame as [Hx Hy].
      apply point_eq_by_xy; symmetry; assumption.
  }
  assert (Hdedup_hull : is_convex_hull pts_l hull_out_2).
  {
    unfold is_convex_hull in *.
    destruct PreH4 as [Hhull | Hhull].
    - left.
      unfold Maximality.is_convex_hull in *.
      destruct Hhull as [Hconv Hmax].
      split; [exact Hconv |].
      unfold Maximality.is_max_hull'_edges in *.
      rewrite Forall_forall in *.
      intros q Hqin.
      destruct (Hcovered q Hqin) as [r [Hr Hqr]].
      subst q.
      apply Hmax.
      exact Hr.
    - right.
      unfold Maximality.is_convex_hull in *.
      destruct Hhull as [Hconv Hmax].
      split; [exact Hconv |].
      unfold Maximality.is_max_hull'_edges in *.
      rewrite Forall_forall in *.
      intros q Hqin.
      destruct (Hcovered q Hqin) as [r [Hr Hqr]].
      subst q.
      apply Hmax.
      exact Hr.
  }
  Exists hull_out_2 ((pivot0 :: tail_sorted) ++ suffix).
  replace (pts_pre + 1 * sizeof("Point"))
    with (pts_pre + sizeof("Point")) by ring.
  sep_apply_l_atomic (point_array_cons_full pts_pre unique_n pivot0 tail_sorted).
  1:{ entailer!; lia. }
  sep_apply_l_atomic (PointArray.seg_to_full pts_pre unique_n n_pre suffix).
  sep_apply_l_atomic (PointArray.full_merge_to_full pts_pre unique_n n_pre
    (pivot0 :: tail_sorted) suffix).
  1:{ entailer!; lia. }
  sep_apply_l_atomic (PointArray.undef_seg_merge_to_undef_seg
    hull_pre retval unique_n n_pre).
  1:{ entailer!; lia. }
  entailer!;
    try exact Hpts_out_len;
    try exact Hret_nonneg;
    try exact Hpts_out_bound;
    try exact Hdedup_hull;
    try lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_dedup_derive_high_level_spec_by_low_level_spec : build_hull_from_sorted_tail_dedup_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  (** kmp_rel_proof_manual L569 *)
  (** Hoare_safeexec_compose *)
  Exists pivot0_high_level_spec l_high_level_spec n_full_high_level_spec
    (fun _ stk => is_convex_hull
       (pivot0_high_level_spec :: l_high_level_spec) (rev stk)).
  split_pure_spatial.
  - cancel (store_point pivot_pre pivot0_high_level_spec).
    cancel (PointArray.full sorted_tail_pre tail_n_pre l_high_level_spec).
    cancel (PointArray.undef_seg hull_pre 0 (tail_n_pre + 1)).
    cancel (PointArray.undef_seg hull_pre (tail_n_pre + 1)
      n_full_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros stk. Intros retval_2.
    Exists (rev stk) retval_2.
    repeat (split_pure_spatial || split_pures).
    + cancel (store_point pivot_pre pivot0_high_level_spec).
      cancel (PointArray.full sorted_tail_pre tail_n_pre l_high_level_spec).
      cancel (PointArray.seg hull_pre 0 retval_2 (rev stk)).
      cancel (PointArray.undef_seg hull_pre retval_2 (tail_n_pre + 1)).
      cancel (PointArray.undef_seg hull_pre (tail_n_pre + 1)
        n_full_high_level_spec).
    + dump_pre_spatial. exact H7.
    + dump_pre_spatial. exact H8.
    + dump_pre_spatial. exact H9.
    + dump_pre_spatial.
      apply safeExec_ret in H11 as (stk_final & Hstk & Hpost).
      sets_unfold in Hpost.
      hnf in Hstk. subst stk_final.
      exact Hpost.
  - repeat (split_pure_spatial || split_pures).
    + dump_pre_spatial. exact H.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. exact H4.
    + dump_pre_spatial. exact H5.
    + dump_pre_spatial. exact H6.
    + dump_pre_spatial.
      eapply safeExec_X_subset.
      * apply Hoare_result_state.
        apply point_polar_sorted_build_hull_convex_hull_rev_stack.
        -- exact H4.
        -- intro Hnil.
           subst l_high_level_spec.
           rewrite Zlength_nil in H2.
           lia.
        -- exact H3.
      * apply safeExec_result_state.
        exists empty_point_stack.
        unfold empty_point_stack.
        reflexivity.
Qed.
