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
From SimpleC.EE.Applications_human.convex_hull Require Import graham_scan_goal.
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
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib FixpointLib.
Local Open Scope sac.

Lemma proof_of_leftdown_return_wit_1_split_goal_1 :
  leftdown_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_cmp_leftdown, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_return_wit_1 : leftdown_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_leftdown_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_leftdown_return_wit_2_split_goal_1 :
  leftdown_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_cmp_leftdown, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_return_wit_2 : leftdown_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_leftdown_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_leftdown_return_wit_3_split_goal_1 :
  leftdown_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_cmp_leftdown, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_return_wit_3 : leftdown_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_leftdown_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_leftdown_return_wit_4_split_goal_1 :
  leftdown_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_cmp_leftdown, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_return_wit_4 : leftdown_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_leftdown_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_leftdown_return_wit_5_split_goal_1 :
  leftdown_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_cmp_leftdown, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_return_wit_5 : leftdown_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_leftdown_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_cross_prod_safety_wit_1_split_goal_1 :
  cross_prod_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *; simpl in *.
  assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_1_split_goal_2 :
  cross_prod_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *; simpl in *.
  assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_1 : cross_prod_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cross_prod_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_cross_prod_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_cross_prod_safety_wit_2_split_goal_1 : cross_prod_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_2_split_goal_2 : cross_prod_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_3_split_goal_1 : cross_prod_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_3_split_goal_2 : cross_prod_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_4_split_goal_1 : cross_prod_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_4_split_goal_2 : cross_prod_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_5_split_goal_1 : cross_prod_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_5_split_goal_2 : cross_prod_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_6_split_goal_1 : cross_prod_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_6_split_goal_2 : cross_prod_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_7_split_goal_1 : cross_prod_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_7_split_goal_2 : cross_prod_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_return_wit_1_split_goal_1 : cross_prod_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto);
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

Lemma proof_of_swap_points_return_wit_1_split_goal_1 : swap_points_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_swap.
  repeat rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
  repeat rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
  repeat rewrite replace_Znth_twice by (repeat rewrite Zlength_replace_Znth; lia).
  repeat rewrite (Znth_indep pts_l i_pre __default_Point default_point) by lia.
  repeat rewrite (Znth_indep pts_l j_pre __default_Point default_point) by lia.
  simpl.
  replace (point_mk (Znth i_pre pts_l default_point).(x)
                    (Znth i_pre pts_l default_point).(y))
    with (Znth i_pre pts_l default_point)
    by (apply point_eq_by_xy; reflexivity).
  replace (point_mk (Znth j_pre pts_l default_point).(x)
                    (Znth j_pre pts_l default_point).(y))
    with (Znth j_pre pts_l default_point)
    by (apply point_eq_by_xy; reflexivity).
  reflexivity.
Qed.

Lemma proof_of_cross_prod_safety_wit_2 : cross_prod_safety_wit_2.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_cross_prod_safety_wit_2_split_goal_1.
  + Goal_apply proof_of_cross_prod_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_cross_prod_safety_wit_3 : cross_prod_safety_wit_3.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_cross_prod_safety_wit_3_split_goal_1.
  + Goal_apply proof_of_cross_prod_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_cross_prod_safety_wit_4 : cross_prod_safety_wit_4.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_cross_prod_safety_wit_4_split_goal_1.
  + Goal_apply proof_of_cross_prod_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_cross_prod_safety_wit_5 : cross_prod_safety_wit_5.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_cross_prod_safety_wit_5_split_goal_1.
  + Goal_apply proof_of_cross_prod_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_cross_prod_safety_wit_6 : cross_prod_safety_wit_6.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_cross_prod_safety_wit_6_split_goal_1.
  + Goal_apply proof_of_cross_prod_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_cross_prod_safety_wit_7 : cross_prod_safety_wit_7.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_cross_prod_safety_wit_7_split_goal_1.
  + Goal_apply proof_of_cross_prod_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_cross_prod_return_wit_1 : cross_prod_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cross_prod_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_dot_prod_safety_wit_1_split_goal_1 :
  dot_prod_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *; simpl in *.
  assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_1_split_goal_2 :
  dot_prod_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *; simpl in *.
  assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_1 : dot_prod_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dot_prod_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_dot_prod_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_dot_prod_safety_wit_2_split_goal_1 :
  dot_prod_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *; simpl in *.
  assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_2_split_goal_2 :
  dot_prod_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *; simpl in *.
  assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_2 : dot_prod_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dot_prod_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_dot_prod_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_dot_prod_safety_wit_3 : dot_prod_safety_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_4 : dot_prod_safety_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_5_split_goal_1 :
  dot_prod_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *; simpl in *.
  assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_5_split_goal_2 :
  dot_prod_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *; simpl in *.
  assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_5 : dot_prod_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dot_prod_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_dot_prod_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_dot_prod_safety_wit_6 : dot_prod_safety_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_7 : dot_prod_safety_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_return_wit_1_split_goal_1 :
  dot_prod_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_dot_prod_return_wit_1 : dot_prod_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_dot_prod_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmp_polar_safety_wit_6_split_goal_1 :
  cmp_polar_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= gp_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= gp_y_pre - a_y_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_x_pre - a_x_pre) * (gp_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (gp_x_pre - a_x_pre)); nia |].
  assert (-400000000 <=
      (b_y_pre - a_y_pre) * (gp_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (gp_y_pre - a_y_pre)); nia |].
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_6_split_goal_2 :
  cmp_polar_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= gp_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= gp_y_pre - a_y_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_x_pre - a_x_pre) * (gp_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (gp_x_pre - a_x_pre)); nia |].
  assert (-400000000 <=
      (b_y_pre - a_y_pre) * (gp_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (gp_y_pre - a_y_pre)); nia |].
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_6 : cmp_polar_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmp_polar_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_cmp_polar_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_cmp_polar_safety_wit_7_split_goal_1 :
  cmp_polar_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= gp_y_pre - a_y_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_y_pre - a_y_pre) * (gp_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (gp_y_pre - a_y_pre)); nia |].
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_7_split_goal_2 :
  cmp_polar_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  assert (-20000 <= gp_y_pre - a_y_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_y_pre - a_y_pre) * (gp_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (gp_y_pre - a_y_pre)); nia |].
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_7 : cmp_polar_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmp_polar_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_cmp_polar_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_cmp_polar_safety_wit_8_split_goal_1 :
  cmp_polar_safety_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_8_split_goal_2 :
  cmp_polar_safety_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_8 : cmp_polar_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmp_polar_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_cmp_polar_safety_wit_8_split_goal_2.
Qed.

Lemma proof_of_cmp_polar_safety_wit_9_split_goal_1 :
  cmp_polar_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_9_split_goal_2 :
  cmp_polar_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_9 : cmp_polar_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmp_polar_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_cmp_polar_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_cmp_polar_safety_wit_10_split_goal_1 :
  cmp_polar_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= gp_x_pre - a_x_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_x_pre - a_x_pre) * (gp_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (gp_x_pre - a_x_pre)); nia |].
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_10_split_goal_2 :
  cmp_polar_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  assert (-20000 <= gp_x_pre - a_x_pre <= 20000); [lia |].
  assert (-400000000 <=
      (b_x_pre - a_x_pre) * (gp_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (gp_x_pre - a_x_pre)); nia |].
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_10 : cmp_polar_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmp_polar_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_cmp_polar_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_cmp_polar_safety_wit_11_split_goal_1 :
  cmp_polar_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_11_split_goal_2 :
  cmp_polar_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_11 : cmp_polar_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmp_polar_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_cmp_polar_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_cmp_polar_safety_wit_12_split_goal_1 :
  cmp_polar_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_12_split_goal_2 :
  cmp_polar_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_12 : cmp_polar_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmp_polar_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_cmp_polar_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_cmp_polar_entail_wit_2_split_goal_1 :
  cmp_polar_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_colinear in *.
  rewrite <- point_cross_by_value_point.
  simpl in *.
  nia.
Qed.

Lemma proof_of_cmp_polar_entail_wit_2_split_goal_2 :
  cmp_polar_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- point_cross_by_value_point.
  simpl in *.
  nia.
Qed.

Lemma proof_of_cmp_polar_entail_wit_2 : cmp_polar_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmp_polar_entail_wit_2_split_goal_1.
  Goal_apply proof_of_cmp_polar_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_cmp_polar_entail_wit_3 : cmp_polar_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_cmp_polar_return_wit_1_split_goal_1 :
  cmp_polar_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_cmp_polar.
  match goal with H : ?cr = point_cross _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec cr 0); [nia |].
  destruct (Z_lt_dec cr 0); [nia |].
  match goal with H : ?mid = point_at_mid _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [nia |].
  match goal with
  | H : retval = point_cmp_leftdown _ _ |- _ => rewrite H
  end.
  apply point_cmp_leftdown_eq_cmp_xy.
Qed.

Lemma proof_of_cmp_polar_return_wit_1 : cmp_polar_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmp_polar_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmp_polar_return_wit_2_split_goal_1 :
  cmp_polar_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_cmp_polar.
  match goal with H : ?cr = point_cross _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec cr 0); [nia |].
  destruct (Z_lt_dec cr 0); [nia |].
  match goal with H : ?mid = point_at_mid _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [nia |].
  unfold point_cmp_xy, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_cmp_polar_return_wit_2 : cmp_polar_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmp_polar_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmp_polar_return_wit_3_split_goal_1 :
  cmp_polar_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_cmp_polar.
  match goal with H : ?cr = point_cross _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec cr 0); [nia |].
  destruct (Z_lt_dec cr 0); [nia |].
  match goal with H : ?mid = point_at_mid _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [nia |].
  unfold point_cmp_xy, point_mk.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_cmp_polar_return_wit_3 : cmp_polar_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmp_polar_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_cmp_polar_return_wit_4_split_goal_1 :
  cmp_polar_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  aggressive_pre_process.
  Goal_apply proof_of_cmp_polar_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_cmp_polar_return_wit_5_split_goal_1 :
  cmp_polar_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  aggressive_pre_process.
  Goal_apply proof_of_cmp_polar_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_1 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_2 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_3 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_4 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_5 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_6 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_7 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_8 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_9 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_10 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_11 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_12 :
  cmp_polar_partial_solve_wit_1_pure_split_goal_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, point_bound, Point_Order.point_bound in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure :
  cmp_polar_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_2.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_3.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_4.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_5.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_6.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_7.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_8.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_9.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_10.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_11.
  - Goal_apply proof_of_cmp_polar_partial_solve_wit_1_pure_split_goal_12.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_1 : build_hull_from_sorted_tail_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (pivot0_low_level_spec :: nil).
  simpl.
  unfold store_point.
  split_pure_spatial.
  - simpl.
    cancel (&(pivot_pre # "Point" ->ₛ "x") # Int |-> pivot0_low_level_spec.(x)).
    cancel (&(pivot_pre # "Point" ->ₛ "y") # Int |-> pivot0_low_level_spec.(y)).
    cancel (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec).
    cancel (PointArray.undef_seg hull_pre 1 (tail_n_pre + 1)).
    fold (store_point (hull_pre + 0) pivot0_low_level_spec).
    change (StorePointAsElement.storeA hull_pre 0 pivot0_low_level_spec |--
      PointArray.seg hull_pre 0 (0 + 1) (pivot0_low_level_spec :: nil)).
    apply PointArray.seg_single.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + simpl. unfold points_in_bound. constructor; auto.
    + match goal with
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
    * match goal with
      | Hsafe : safeExec _ _ _ |- _ => exact Hsafe
      end.
    * intros s [s0 [Hs _]]. subst s. reflexivity.
Qed.

(* The generated split goal disappeared; keep the original lemma text for reference.
Lemma proof_of_build_hull_from_sorted_tail_entail_wit_2_split_goal_1 :
  build_hull_from_sorted_tail_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
*)

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_2 :
  build_hull_from_sorted_tail_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Exists stk_2.
    split_pure_spatial.
    + cancel.
    + repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
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
      * eapply bind_equiv.
        -- reflexivity.
        -- intros []. reflexivity.
      * match goal with
        | Hsafe : safeExec _ _ _ |- _ => exact Hsafe
        end.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_3 : build_hull_from_sorted_tail_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
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
      assert (Htail_hi : top + 1 <= tail_n_pre + 1) by lia.
      apply (point_array_seg_pop_tail hull_pre top (tail_n_pre + 1)
               (rev (s :: T)) t Htop_pop Htail_hi).
    + repeat split_pures.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. lia.
	      * dump_pre_spatial. lia.
	      * dump_pre_spatial. lia.
	      * dump_pre_spatial. lia.
	      * dump_pre_spatial.
	        match goal with
	        | Hlen_l : tail_n_pre = Zlength l_low_level_spec |- _ =>
	            exact Hlen_l
	        end.
	      * dump_pre_spatial. lia.
	      * dump_pre_spatial.
	        match goal with
	        | Hsorted : point_polar_sorted pivot0_low_level_spec l_low_level_spec |- _ =>
	            exact Hsorted
	        end.
	      * dump_pre_spatial.
	        match goal with
	        | Hpivot_bound : point_in_bound pivot0_low_level_spec |- _ =>
	            exact Hpivot_bound
	        end.
	      * dump_pre_spatial.
	        match goal with
	        | Hpoints_l : points_in_bound l_low_level_spec |- _ =>
	            exact Hpoints_l
	        end.
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

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_4_1 : build_hull_from_sorted_tail_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_4_2 : build_hull_from_sorted_tail_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(int_auto).
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

(* The generated split goal disappeared; keep the original lemma text for reference.
Lemma proof_of_build_hull_from_sorted_tail_return_wit_1_split_goal_1 :
  build_hull_from_sorted_tail_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
*)

Lemma proof_of_build_hull_from_sorted_tail_return_wit_1 :
  build_hull_from_sorted_tail_return_wit_1.
Proof.
  aggressive_pre_process.
  Exists stk_2.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
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

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_1 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_2 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_3 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_4 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_5 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_6 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_7 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_8 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_9 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_10 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_11 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_12 :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  match goal with
  | Hbound : points_in_bound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (points_in_bound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure :
  build_hull_from_sorted_tail_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_1.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_2.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_3.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_4.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_5.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_6.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_7.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_8.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_9.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_10.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_11.
  - Goal_apply proof_of_build_hull_from_sorted_tail_partial_solve_wit_9_pure_split_goal_12.
Qed.

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_swap_points_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_1_split_goal_1 :
  partition_polar_points_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_partition_polar_points_entail_wit_1_split_goal_2 :
  partition_polar_points_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply points_in_bound_Znth_point_mk; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_1_split_goal_3 :
  partition_polar_points_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_partition_polar_points_entail_wit_1_split_goal_4 :
  partition_polar_points_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_partition_polar_points_entail_wit_1 :
  partition_polar_points_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_polar_points_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_partition_polar_points_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_partition_polar_points_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_partition_polar_points_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_1 :
  partition_polar_points_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
              match goal with
              | Hret_le : retval <= 0,
                Hret_eq : retval =
                  point_cmp_polar (point_mk gx_pre gy_pre)
                    (point_mk (point_x (Znth j pts_cur_2 __default_Point))
                              (point_y (Znth j pts_cur_2 __default_Point)))
                    (point_mk pivot_x pivot_y) |- _ =>
                  rewrite <- Hret_eq; exact Hret_le
              end.
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

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_2 :
  partition_polar_points_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply leftmost_permutation.
  - eapply point_swap_permutation; lia.
  - assumption.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_3 :
  partition_polar_points_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply points_in_bound_point_swap; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_4 :
  partition_polar_points_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j)
            high_pre __default_Point default_point)
    by (rewrite Zlength_point_swap; lia).
  rewrite point_swap_Znth_other_index by lia.
  rewrite <- (Znth_indep pts_cur_2 high_pre __default_Point default_point)
    by lia.
  assumption.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_5 :
  partition_polar_points_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j)
            high_pre __default_Point default_point)
    by (rewrite Zlength_point_swap; lia).
  rewrite point_swap_Znth_other_index by lia.
  rewrite <- (Znth_indep pts_cur_2 high_pre __default_Point default_point)
    by lia.
  assumption.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1_split_goal_6 :
  partition_polar_points_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_point_swap. assumption.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_1 :
  partition_polar_points_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_polar_points_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_partition_polar_points_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_partition_polar_points_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_partition_polar_points_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_partition_polar_points_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_partition_polar_points_entail_wit_2_1_split_goal_6.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_2_split_goal_1 :
  partition_polar_points_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_partition_polar_points_entail_wit_2_2 :
  partition_polar_points_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_partition_polar_points_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_partition_polar_points_entail_wit_2_3_split_goal_1 :
  partition_polar_points_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_partition_polar_points_entail_wit_2_3 :
  partition_polar_points_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_partition_polar_points_entail_wit_2_3_split_goal_1.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_1 :
  partition_polar_points_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_polar_partition_scan_inv in *.
  match goal with
  | Hscan : point_permutation _ _ /\ _ |- _ =>
      destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
  end.
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

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_2 :
  partition_polar_points_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_polar_partition_scan_inv in *.
  match goal with
  | Hscan : point_permutation _ _ /\ _ |- _ =>
      destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
  end.
  eapply point_same_outside_range_point_swap_inside; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_3 :
  partition_polar_points_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_polar_partition_scan_inv in *.
  match goal with
  | Hscan : point_permutation _ _ /\ _ |- _ =>
      destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
  end.
  eapply Permutation_trans; [exact Hperm |].
  eapply point_swap_permutation; lia.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_4 :
  partition_polar_points_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply leftmost_permutation.
  - eapply point_swap_permutation; lia.
  - eauto.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_5 :
  partition_polar_points_return_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply points_in_bound_point_swap; eauto; lia.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1_split_goal_6 :
  partition_polar_points_return_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_point_swap. assumption.
Qed.

Lemma proof_of_partition_polar_points_return_wit_1 :
  partition_polar_points_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_polar_points_return_wit_1_split_goal_1.
  - Goal_apply proof_of_partition_polar_points_return_wit_1_split_goal_2.
  - Goal_apply proof_of_partition_polar_points_return_wit_1_split_goal_3.
  - Goal_apply proof_of_partition_polar_points_return_wit_1_split_goal_4.
  - Goal_apply proof_of_partition_polar_points_return_wit_1_split_goal_5.
  - Goal_apply proof_of_partition_polar_points_return_wit_1_split_goal_6.
Qed.

Lemma proof_of_partition_polar_points_return_wit_2_split_goal_1 :
  partition_polar_points_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_polar_partition_scan_inv in *.
  match goal with
  | Hscan : point_permutation _ _ /\ _ |- _ =>
      destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
  end.
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

Lemma proof_of_partition_polar_points_return_wit_2_split_goal_2 :
  partition_polar_points_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_polar_partition_scan_inv in *.
  match goal with
  | Hscan : point_permutation _ _ /\ _ |- _ =>
      destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
  end.
  rewrite PreH1.
  exact Hsame.
Qed.

Lemma proof_of_partition_polar_points_return_wit_2_split_goal_3 :
  partition_polar_points_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_polar_partition_scan_inv in *.
  match goal with
  | Hscan : point_permutation _ _ /\ _ |- _ =>
      destruct Hscan as [Hperm [Hsame [Hpivot [Hle Hgt]]]]
  end.
  exact Hperm.
Qed.

Lemma proof_of_partition_polar_points_return_wit_2 :
  partition_polar_points_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_polar_points_return_wit_2_split_goal_1.
  - Goal_apply proof_of_partition_polar_points_return_wit_2_split_goal_2.
  - Goal_apply proof_of_partition_polar_points_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_partition_polar_points_partial_solve_wit_5_pure : partition_polar_points_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  - exact PreH14.
  - exact PreH15.
  - eapply points_in_bound_Znth_point_mk; eauto; lia.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_1_split_goal_1 :
  quicksort_polar_points_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_quicksort_polar_points_return_wit_1_split_goal_2 :
  quicksort_polar_points_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_quicksort_polar_points_return_wit_1_split_goal_3 :
  quicksort_polar_points_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_permutation in *.
  eapply Permutation_trans; [eassumption |].
  eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_1 :
  quicksort_polar_points_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_1_split_goal_1.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_1_split_goal_2.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_2_split_goal_1 :
  quicksort_polar_points_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_quicksort_polar_points_return_wit_2_split_goal_2 :
  quicksort_polar_points_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_quicksort_polar_points_return_wit_2_split_goal_3 :
  quicksort_polar_points_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_permutation in *.
  eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_2 :
  quicksort_polar_points_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_2_split_goal_1.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_2_split_goal_2.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_3_split_goal_1 :
  quicksort_polar_points_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_quicksort_polar_points_return_wit_3_split_goal_2 :
  quicksort_polar_points_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_quicksort_polar_points_return_wit_3_split_goal_3 :
  quicksort_polar_points_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_permutation in *.
  eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_3 :
  quicksort_polar_points_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_3_split_goal_1.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_3_split_goal_2.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_3_split_goal_3.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_4_split_goal_1 :
  quicksort_polar_points_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_sorted_range. intros.
  assert (i = j) as Hij.
  { lia. }
  subst.
  rewrite point_cmp_polar_refl. lia.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_4_split_goal_2 :
  quicksort_polar_points_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_same_outside_range.
  split; [reflexivity|]. intros; reflexivity.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_4_split_goal_3 :
  quicksort_polar_points_return_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_4 :
  quicksort_polar_points_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_4_split_goal_1.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_4_split_goal_2.
  - Goal_apply proof_of_quicksort_polar_points_return_wit_4_split_goal_3.
Qed.

Lemma proof_of_graham_scan_entail_wit_1_split_goal_1 :
  graham_scan_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_leftmost_prefix.
  apply point_leftmost_prefix_init.
  lia.
Qed.

Lemma proof_of_graham_scan_entail_wit_1 : graham_scan_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_graham_scan_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_graham_scan_entail_wit_2_1_split_goal_1 :
  graham_scan_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_leftmost_prefix in *.
  eapply point_leftmost_prefix_step_update; eauto; try lia.
  apply point_cmp_leftdown_lt_point_leftdown.
  rewrite <- (point_mk_eta (Znth i pts_l default_point)).
  rewrite <- (point_mk_eta (Znth pivot_idx pts_l default_point)).
  rewrite (Znth_indep pts_l i default_point __default_Point) by lia.
  rewrite (Znth_indep pts_l pivot_idx default_point __default_Point) by lia.
  match goal with
  | Hlt : ?retval < 0,
    Heq : ?retval = point_cmp_leftdown _ _ |- point_cmp_leftdown _ _ < 0 =>
      rewrite <- Heq; exact Hlt
  end.
Qed.

Lemma proof_of_graham_scan_entail_wit_2_1 : graham_scan_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_graham_scan_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_graham_scan_entail_wit_2_2_split_goal_1 :
  graham_scan_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold point_leftmost_prefix in *.
  eapply point_leftmost_prefix_step_keep; eauto; try lia.
  apply point_cmp_leftdown_nonneg_point_leftdown_flip.
  rewrite <- (point_mk_eta (Znth i pts_l default_point)).
  rewrite <- (point_mk_eta (Znth pivot_idx pts_l default_point)).
  rewrite (Znth_indep pts_l i default_point __default_Point) by lia.
  rewrite (Znth_indep pts_l pivot_idx default_point __default_Point) by lia.
  match goal with
  | Hge : 0 <= ?retval,
    Heq : ?retval = point_cmp_leftdown _ _ |- _ =>
      rewrite <- Heq; lia
  | Hge : ?retval >= 0,
    Heq : ?retval = point_cmp_leftdown _ _ |- _ =>
      rewrite <- Heq; lia
  | Hge : 0 <= ?retval,
    Heq : point_cmp_leftdown _ _ = ?retval |- _ =>
      rewrite Heq; lia
  | Hge : ?retval >= 0,
    Heq : point_cmp_leftdown _ _ = ?retval |- _ =>
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_graham_scan_entail_wit_2_2 : graham_scan_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_graham_scan_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_graham_scan_entail_wit_3_2 : graham_scan_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (pts_pivot := point_swap pts_l 0 pivot_idx).
  set (pivot0 :=
         point_mk (point_x (Znth 0 pts_l __default_Point))
                  (point_y (Znth 0 pts_l __default_Point))).
  set (tail_sorted := sublist 1 n_pre pts_out).
  Exists tail_sorted pts_out pts_pivot pivot0.
  assert (Hpivot_out :
            Znth 0 pts_out default_point = Znth 0 pts_l default_point).
  {
    subst pts_pivot.
    unfold point_same_outside_range in PreH5.
    destruct PreH5 as [_ Hsame].
    apply Hsame.
    - rewrite PreH17. lia.
    - left. lia.
  }
  assert (Hpivot0_out : pivot0 = Znth 0 pts_out default_point).
  {
    subst pivot0.
    rewrite (Znth_indep pts_l 0 __default_Point default_point) by lia.
    rewrite <- Hpivot_out.
    destruct (Znth 0 pts_out default_point).
    reflexivity.
  }
  assert (Hpts_out_cons : pts_out = pivot0 :: tail_sorted).
  {
    subst tail_sorted.
    eapply point_list_cons_sublist_1_by_fields
      with (d := default_point); eauto; try lia.
    - subst pivot0. rewrite <- Hpivot0_out. reflexivity.
    - subst pivot0. rewrite <- Hpivot0_out. reflexivity.
  }
  assert (Hperm_point : point_permutation pts_pivot pts_out).
  {
    subst pts_pivot.
    rewrite PreH7.
    rewrite point_swap_0_0.
    exact PreH4.
  }
  split_pure_spatial.
  - rewrite Hpts_out_cons.
    sep_apply_l_atomic
      (PointArray.full_split_to_missing_i pts_pre 0 n_pre
         (pivot0 :: tail_sorted) default_point).
    + dump_pre_spatial. lia.
    + simpl.
      sep_apply_l_atomic (PointArray.missing_i_to_seg_head pts_pre 0 n_pre pivot0 tail_sorted).
      sep_apply_l_atomic (PointArray.seg_to_full pts_pre 1 n_pre tail_sorted).
      replace ((n_pre - 1) + 1) with n_pre by lia.
      unfold StorePointAsElement.storeA, store_point.
      replace (pts_pre + 0 * sizeof("Point")) with pts_pre by lia.
      replace (pts_pre + 1 * sizeof("Point")) with (pts_pre + sizeof("Point")) by lia.
      subst pivot0.
      simpl.
      replace (pts_pre + 0) with pts_pre by lia.
      rewrite sizeof_Point_eq.
      simpl.
      cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + subst tail_sorted. rewrite Zlength_sublist; lia.
    + subst tail_sorted.
      eapply points_in_bound_sublist; eauto; lia.
    + rewrite Hpivot0_out.
      eapply points_in_bound_Znth; eauto; lia.
    + unfold point_leftmost_prefix in PreH16.
      replace i with n_pre in PreH16 by lia.
      exact PreH16.
    + subst tail_sorted.
      eapply point_sorted_range_tail_point_polar_sorted.
      * reflexivity.
      * lia.
      * lia.
      * subst pivot0.
        exact PreH6.
    + eapply point_leftmost_prefix_sorted_tail_leftmost
        with (l := pts_l) (pivot_idx := pivot_idx) (n := n_pre)
             (pts_pivot := pts_pivot) (pts_sorted := pts_out).
      * lia.
      * unfold point_leftmost_prefix in PreH16.
        replace i with n_pre in PreH16 by lia.
        exact PreH16.
      * subst pts_pivot. reflexivity.
      * rewrite Hpivot0_out.
        subst pts_pivot.
        rewrite PreH7.
        rewrite point_swap_0_0.
        exact Hpivot_out.
      * lia.
      * subst tail_sorted. reflexivity.
      * exact Hperm_point.
    + rewrite (Znth_indep pts_out 0 __default_Point default_point) by lia.
      rewrite (Znth_indep pts_l 0 __default_Point default_point) by lia.
      rewrite Hpivot_out.
      reflexivity.
    + rewrite (Znth_indep pts_out 0 __default_Point default_point) by lia.
      rewrite (Znth_indep pts_l 0 __default_Point default_point) by lia.
      rewrite Hpivot_out.
      reflexivity.
Qed.

Lemma proof_of_graham_scan_entail_wit_3_1 : graham_scan_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (pts_pivot := point_swap pts_l 0 pivot_idx).
  set (pivot0 :=
         point_mk (point_x (Znth 0 pts_pivot __default_Point))
                  (point_y (Znth 0 pts_pivot __default_Point))).
  set (tail_sorted := sublist 1 n_pre pts_out).
  Exists tail_sorted pts_out pts_pivot pivot0.
  assert (Hpivot_out :
            Znth 0 pts_out default_point =
            Znth 0 pts_pivot default_point).
  {
    subst pts_pivot.
    unfold point_same_outside_range in PreH5.
    destruct PreH5 as [_ Hsame].
    apply Hsame.
    - rewrite Zlength_point_swap. lia.
    - left. lia.
  }
  assert (Hpivot0_out : pivot0 = Znth 0 pts_out default_point).
  {
    subst pivot0 pts_pivot.
    rewrite (Znth_indep (point_swap pts_l 0 pivot_idx) 0 __default_Point default_point)
      by (rewrite Zlength_point_swap; lia).
    rewrite <- Hpivot_out.
    destruct (Znth 0 pts_out default_point).
    reflexivity.
  }
  assert (Hpts_out_cons : pts_out = pivot0 :: tail_sorted).
  {
    subst tail_sorted.
    eapply point_list_cons_sublist_1_by_fields
      with (d := default_point); eauto; try lia.
    - subst pivot0. rewrite <- Hpivot0_out. reflexivity.
    - subst pivot0. rewrite <- Hpivot0_out. reflexivity.
  }
  assert (Hperm_point : point_permutation pts_pivot pts_out).
  {
    subst pts_pivot.
    exact PreH4.
  }
  split_pure_spatial.
  - rewrite Hpts_out_cons.
    sep_apply_l_atomic
      (PointArray.full_split_to_missing_i pts_pre 0 n_pre
         (pivot0 :: tail_sorted) default_point).
    + dump_pre_spatial. lia.
    + simpl.
      sep_apply_l_atomic (PointArray.missing_i_to_seg_head pts_pre 0 n_pre pivot0 tail_sorted).
      sep_apply_l_atomic (PointArray.seg_to_full pts_pre 1 n_pre tail_sorted).
      replace ((n_pre - 1) + 1) with n_pre by lia.
      unfold StorePointAsElement.storeA, store_point.
      replace (pts_pre + 0 * sizeof("Point")) with pts_pre by lia.
      replace (pts_pre + 1 * sizeof("Point")) with (pts_pre + sizeof("Point")) by lia.
      subst pivot0.
      simpl.
      replace (pts_pre + 0) with pts_pre by lia.
      rewrite sizeof_Point_eq.
      simpl.
      cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + subst tail_sorted. rewrite Zlength_sublist; lia.
    + subst tail_sorted.
      eapply points_in_bound_sublist; eauto; lia.
    + rewrite Hpivot0_out.
      eapply points_in_bound_Znth; eauto; lia.
    + unfold point_leftmost_prefix in PreH17.
      replace i with n_pre in PreH17 by lia.
      exact PreH17.
    + subst tail_sorted.
      eapply point_sorted_range_tail_point_polar_sorted.
      * reflexivity.
      * lia.
      * lia.
      * subst pivot0.
        exact PreH6.
    + eapply point_leftmost_prefix_sorted_tail_leftmost
        with (l := pts_l) (pivot_idx := pivot_idx) (n := n_pre)
             (pts_pivot := pts_pivot) (pts_sorted := pts_out).
      * lia.
      * unfold point_leftmost_prefix in PreH17.
        replace i with n_pre in PreH17 by lia.
        exact PreH17.
      * subst pts_pivot. reflexivity.
      * rewrite Hpivot0_out. rewrite Hpivot_out. reflexivity.
      * lia.
      * subst tail_sorted. reflexivity.
      * exact Hperm_point.
    + rewrite (Znth_indep pts_out 0 __default_Point default_point) by lia.
      rewrite (Znth_indep pts_pivot 0 __default_Point default_point)
        by (subst pts_pivot; rewrite Zlength_point_swap; lia).
      rewrite Hpivot_out.
      reflexivity.
    + rewrite (Znth_indep pts_out 0 __default_Point default_point) by lia.
      rewrite (Znth_indep pts_pivot 0 __default_Point default_point)
        by (subst pts_pivot; rewrite Zlength_point_swap; lia).
      rewrite Hpivot_out.
      reflexivity.
Qed.

Lemma proof_of_graham_scan_return_wit_1 : graham_scan_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace ((n_pre - 1) + 1) with n_pre by lia.
  prop_apply (PointArray.undef_seg_valid hull_pre retval n_pre).
  Intros.
  Exists hull_out_2 pts_sorted.
  assert (Hpts_sorted_cons : pts_sorted = pivot0 :: tail_sorted).
  {
    eapply point_list_cons_sublist_1_by_fields
      with (n := n_pre) (d := __default_Point); eauto; try lia.
    - match goal with
      | Hx0 : (Znth 0 pts_sorted __default_Point).(x) = gx,
        Hpivot : pivot0 = point_mk gx gy |- _ =>
          rewrite Hpivot; exact Hx0
      end.
    - match goal with
      | Hy0 : (Znth 0 pts_sorted __default_Point).(y) = gy,
        Hpivot : pivot0 = point_mk gx gy |- _ =>
          rewrite Hpivot; exact Hy0
      end.
  }
  assert (Hperm_l_pivot : point_permutation pts_l pts_pivot).
  {
    subst pts_pivot.
    apply point_swap_permutation;
      unfold point_leftmost_prefix in *; lia.
  }
  assert (Hperm_l_sorted : point_permutation pts_l pts_sorted).
  {
    unfold point_permutation in *.
    eapply Permutation_trans; eauto.
  }
  assert (Hhull_l : is_convex_hull pts_l hull_out_2).
  {
    eapply is_convex_hull_base_permutation.
    - exact Hperm_l_sorted.
    - rewrite Hpts_sorted_cons.
      match goal with
      | Hhull : is_convex_hull (pivot0 :: tail_sorted) hull_out_2 |- _ =>
          exact Hhull
      end.
  }
  assert (Hhull_nonempty : 1 <= Zlength hull_out_2).
  {
    eapply is_convex_hull_base_nonempty_hull_nonempty
      with (base := pivot0 :: tail_sorted) (p := pivot0).
    - simpl. auto.
    - match goal with
      | Hhull : is_convex_hull (pivot0 :: tail_sorted) hull_out_2 |- _ =>
          exact Hhull
      end.
  }
  split_pure_spatial.
  - rewrite Hpts_sorted_cons.
    assert (Htail : tail = pts_pre + sizeof("Point")) by
      (rewrite PreH5; ring).
    rewrite Htail.
    sep_apply_l_atomic (point_array_cons_full pts_pre n_pre pivot0 tail_sorted).
    + dump_pre_spatial. lia.
    + cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try lia.
Qed.

Lemma proof_of_graham_scan_partial_solve_wit_11_pure_split_goal_1 :
  graham_scan_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  rewrite Zlength_point_swap; lia.
Qed.

Lemma proof_of_graham_scan_partial_solve_wit_11_pure_split_goal_2 :
  graham_scan_partial_solve_wit_11_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  apply points_in_bound_point_swap; eauto; lia.
Qed.

Lemma proof_of_graham_scan_partial_solve_wit_11_pure_split_goal_3 :
  graham_scan_partial_solve_wit_11_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  eapply points_in_bound_Znth_point_mk.
  - apply points_in_bound_point_swap; eauto; lia.
  - rewrite Zlength_point_swap; lia.
Qed.

Lemma proof_of_graham_scan_partial_solve_wit_11_pure_split_goal_4 :
  graham_scan_partial_solve_wit_11_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  replace (point_mk (point_x (Znth 0 (point_swap pts_l 0 pivot_idx) __default_Point))
                    (point_y (Znth 0 (point_swap pts_l 0 pivot_idx) __default_Point)))
    with (Znth 0 (point_swap pts_l 0 pivot_idx) default_point).
  - eapply point_leftmost_prefix_leftmost_point_swap with (n := n_pre); eauto.
    match goal with
    | Hprefix : point_leftmost_prefix pts_l pivot_idx i |- _ =>
        unfold point_leftmost_prefix in Hprefix;
        replace i with n_pre in Hprefix by lia;
        exact Hprefix
    end.
  - rewrite (Znth_indep (point_swap pts_l 0 pivot_idx) 0
               __default_Point default_point)
      by (rewrite Zlength_point_swap; lia).
    destruct (Znth 0 (point_swap pts_l 0 pivot_idx) default_point).
    reflexivity.
Qed.

Lemma proof_of_graham_scan_partial_solve_wit_11_pure :
  graham_scan_partial_solve_wit_11_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  all: match goal with
  | |- Zlength (point_swap ?l 0 ?p) = ?n =>
      rewrite Zlength_point_swap; lia
  | |- points_in_bound (point_swap ?l 0 ?p) =>
      apply points_in_bound_point_swap; eauto; lia
  | |- point_in_bound
      (point_mk (point_x (Znth 0 (point_swap ?l 0 ?p) ?d))
                (point_y (Znth 0 (point_swap ?l 0 ?p) ?d))) =>
      eapply points_in_bound_Znth_point_mk;
      [apply points_in_bound_point_swap; eauto; lia
      |rewrite Zlength_point_swap; lia]
  | |- leftmost
      (point_mk (point_x (Znth 0 (point_swap ?l 0 ?p) ?d))
                (point_y (Znth 0 (point_swap ?l 0 ?p) ?d)))
      (point_swap ?l 0 ?p) =>
      replace (point_mk
          (point_x (Znth 0 (point_swap l 0 p) d))
          (point_y (Znth 0 (point_swap l 0 p) d)))
        with (Znth 0 (point_swap l 0 p) default_point);
      [eapply point_leftmost_prefix_leftmost_point_swap; eauto;
       match goal with
       | Hprefix : point_leftmost_prefix l p ?idx,
         Hlen : Zlength l = ?n |- _ =>
           unfold point_leftmost_prefix in Hprefix;
           replace idx with n in Hprefix by lia;
           exact Hprefix
       end
      |rewrite (Znth_indep (point_swap l 0 p) 0 d default_point)
         by (rewrite Zlength_point_swap; lia);
       destruct (Znth 0 (point_swap l 0 p) default_point);
       reflexivity]
  | |- _ => first [assumption | reflexivity | lia]
  end.
Qed.

Lemma proof_of_graham_scan_partial_solve_wit_12_pure_split_goal_1 :
  graham_scan_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  eapply points_in_bound_Znth_point_mk; eauto; lia.
Qed.

Lemma proof_of_graham_scan_partial_solve_wit_12_pure_split_goal_2 :
  graham_scan_partial_solve_wit_12_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  replace (point_mk (point_x (Znth 0 pts_l __default_Point))
                    (point_y (Znth 0 pts_l __default_Point)))
    with (Znth pivot_idx pts_l default_point).
  - apply point_leftmost_prefix_leftmost.
    unfold point_leftmost_prefix in PreH18.
    replace i with (Zlength pts_l) in PreH18 by lia.
    exact PreH18.
  - rewrite PreH9.
    rewrite (Znth_indep pts_l 0 __default_Point default_point) by lia.
    destruct (Znth 0 pts_l default_point); reflexivity.
Qed.

Lemma proof_of_graham_scan_partial_solve_wit_12_pure :
  graham_scan_partial_solve_wit_12_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  all: match goal with
  | |- point_in_bound
      (point_mk (point_x (Znth 0 ?l ?d))
                (point_y (Znth 0 ?l ?d))) =>
      eapply points_in_bound_Znth_point_mk; eauto; lia
  | |- leftmost
      (point_mk (point_x (Znth 0 ?l ?d))
                (point_y (Znth 0 ?l ?d))) ?l =>
      match goal with
      | Hp : ?p = 0 |- _ =>
          match goal with
          | Hprefix : point_leftmost_prefix l p ?idx |- _ =>
              replace (point_mk (point_x (Znth 0 l d))
                                (point_y (Znth 0 l d)))
                with (Znth p l default_point);
              [apply point_leftmost_prefix_leftmost;
               unfold point_leftmost_prefix in Hprefix;
               replace idx with (Zlength l) in Hprefix by lia;
               exact Hprefix
              |rewrite Hp;
               rewrite (Znth_indep l 0 d default_point) by lia;
               destruct (Znth 0 l default_point); reflexivity]
          end
      end
  | |- _ => first [assumption | reflexivity | lia]
  end.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_derive_high_level_spec_by_low_level_spec : build_hull_from_sorted_tail_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  (** kmp_rel_proof_manual L569 *)
  (** Hoare_safeexec_compose *)
  Exists pivot0_high_level_spec l_high_level_spec
    (fun _ stk => is_convex_hull
       (pivot0_high_level_spec :: l_high_level_spec) (rev stk)).
  split_pure_spatial.
  - cancel (store_point pivot_pre pivot0_high_level_spec).
    cancel (PointArray.full sorted_tail_pre tail_n_pre l_high_level_spec).
    cancel (PointArray.undef_full hull_pre (tail_n_pre + 1)).
    apply derivable1_wand_sepcon_adjoint.
    Intros stk. Intros retval_2.
    Exists (rev stk) retval_2.
    repeat (split_pure_spatial || split_pures).
    + cancel (store_point pivot_pre pivot0_high_level_spec).
      cancel (PointArray.full sorted_tail_pre tail_n_pre l_high_level_spec).
      cancel (PointArray.seg hull_pre 0 retval_2 (rev stk)).
      cancel (PointArray.undef_seg hull_pre retval_2 (tail_n_pre + 1)).
    + dump_pre_spatial. exact H6.
    + dump_pre_spatial. exact H7.
    + dump_pre_spatial. exact H8.
    + dump_pre_spatial.
      apply safeExec_ret in H10 as (stk_final & Hstk & Hpost).
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
    + dump_pre_spatial.
      eapply safeExec_X_subset.
      * apply Hoare_result_state.
        apply point_polar_sorted_build_hull_convex_hull_rev_stack;
          try exact H2; try exact H3.
        destruct l_high_level_spec.
        -- rewrite Zlength_nil in H1. lia.
        -- discriminate.
      * apply safeExec_result_state.
        exists empty_point_stack.
        unfold empty_point_stack.
        reflexivity.
Qed.
