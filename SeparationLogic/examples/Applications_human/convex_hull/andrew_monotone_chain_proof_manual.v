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
From SimpleC.EE.Applications_human.convex_hull Require Import andrew_monotone_chain_goal.
From SimpleC.EE.Applications_human.convex_hull Require Import andrew_monotone_chain_proof_auto.
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

(* This proof predates the global [pre_process] change that automatically
   selects the left branch of a disjunctive generated witness.  Preserve the
   legacy behavior locally so the explicit [left]/[right] choices below keep
   their original meaning. *)
Ltac pre_process ::= 
  try Unfold;
  intros; poly_store_unfold;
  Rename pre_process_pure;
  try (solve [entailer!]).

Lemma proof_of_cmp_xy_return_wit_1_split_goal_1 : cmp_xy_return_wit_1_split_goal_1.
Proof.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [lia |].
  destruct (Z_gt_dec a_y_pre b_y_pre) as [Hygt | Hygt]; [lia |].
  entailer!.
Qed.

Lemma proof_of_cmp_xy_return_wit_1 : cmp_xy_return_wit_1.
Proof.
  left.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [lia |].
  destruct (Z_gt_dec a_y_pre b_y_pre) as [Hygt | Hygt]; [lia |].
  entailer!.
Qed.

Lemma proof_of_cmp_xy_return_wit_2_split_goal_1 : cmp_xy_return_wit_2_split_goal_1.
Proof.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [lia |].
  destruct (Z_gt_dec a_y_pre b_y_pre) as [Hygt | Hygt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_2 : cmp_xy_return_wit_2.
Proof.
  left.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [lia |].
  destruct (Z_gt_dec a_y_pre b_y_pre) as [Hygt | Hygt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_3_split_goal_1 : cmp_xy_return_wit_3_split_goal_1.
Proof.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_3 : cmp_xy_return_wit_3.
Proof.
  left.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_4_split_goal_1 : cmp_xy_return_wit_4_split_goal_1.
Proof.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_4 : cmp_xy_return_wit_4.
Proof.
  left.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_5_split_goal_1 : cmp_xy_return_wit_5_split_goal_1.
Proof.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_5 : cmp_xy_return_wit_5.
Proof.
  left.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [entailer! | lia].
Qed.

Lemma proof_of_cross_prod_safety_wit_1_split_goal_1 : cross_prod_safety_wit_1_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_1_split_goal_2 : cross_prod_safety_wit_1_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_1 : cross_prod_safety_wit_1.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_2_split_goal_1 : cross_prod_safety_wit_2_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_2_split_goal_2 : cross_prod_safety_wit_2_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_2 : cross_prod_safety_wit_2.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_3_split_goal_1 : cross_prod_safety_wit_3_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_3_split_goal_2 : cross_prod_safety_wit_3_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_3 : cross_prod_safety_wit_3.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_4_split_goal_1 : cross_prod_safety_wit_4_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_4_split_goal_2 : cross_prod_safety_wit_4_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_4 : cross_prod_safety_wit_4.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_5_split_goal_1 : cross_prod_safety_wit_5_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_5_split_goal_2 : cross_prod_safety_wit_5_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_5 : cross_prod_safety_wit_5.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_6_split_goal_1 : cross_prod_safety_wit_6_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_6_split_goal_2 : cross_prod_safety_wit_6_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_6 : cross_prod_safety_wit_6.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_7_split_goal_1 : cross_prod_safety_wit_7_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_7_split_goal_2 : cross_prod_safety_wit_7_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_7 : cross_prod_safety_wit_7.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_return_wit_1_split_goal_1 : cross_prod_return_wit_1_split_goal_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_cross_prod_return_wit_1 : cross_prod_return_wit_1.
Proof.
  pre_process.
  left.
  intros.
  pre_process.
Qed. 

Lemma proof_of_swap_points_return_wit_1_split_goal_1 : swap_points_return_wit_1_split_goal_1.
Proof.
  pre_process.
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

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof.
  left.
  pre_process.
  match goal with
  | |- PointArray.full _ _ ?l |-- _ =>
      replace l with (point_swap pts_l i_pre j_pre)
  end.
  - split_pure_spatial.
    + cancel (PointArray.full pts_pre n_pre (point_swap pts_l i_pre j_pre)).
    + dump_pre_spatial. exact PreH6.
  - symmetry.
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

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_1 : partition_xy_points_entail_wit_1_split_goal_1.
Proof.
  pre_process.
  eapply point_xy_partition_scan_inv_init; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_2 : partition_xy_points_entail_wit_1_split_goal_2.
Proof.
  pre_process.
  apply points_in_bound_Znth_point_mk; auto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_3 : partition_xy_points_entail_wit_1_split_goal_3.
Proof. pre_process. Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_4 : partition_xy_points_entail_wit_1_split_goal_4.
Proof. pre_process. Qed.

Lemma proof_of_partition_xy_points_entail_wit_1 : partition_xy_points_entail_wit_1.
Proof.
  pre_process. right. intros. split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_partition_scan_inv_init; eauto; lia.
    + dump_pre_spatial.
      apply points_in_bound_Znth_point_mk; auto; lia.
    + dump_pre_spatial; auto.
    + dump_pre_spatial; auto.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_1 : partition_xy_points_entail_wit_2_1_split_goal_1.
Proof.
  pre_process.
  eapply point_xy_partition_scan_inv_accept_swap; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_2 : partition_xy_points_entail_wit_2_1_split_goal_2.
Proof.
  pre_process.
  apply points_in_bound_point_swap; auto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_3 : partition_xy_points_entail_wit_2_1_split_goal_3.
Proof.
  pre_process.
  rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j) high_pre
             __default_Point default_point)
    by (rewrite Zlength_point_swap; lia).
  rewrite point_swap_Znth_other_index by lia.
  rewrite (Znth_indep pts_cur_2 high_pre default_point __default_Point) by lia.
  auto.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_4 : partition_xy_points_entail_wit_2_1_split_goal_4.
Proof.
  pre_process.
  rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j) high_pre
             __default_Point default_point)
    by (rewrite Zlength_point_swap; lia).
  rewrite point_swap_Znth_other_index by lia.
  rewrite (Znth_indep pts_cur_2 high_pre default_point __default_Point) by lia.
  auto.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_5 : partition_xy_points_entail_wit_2_1_split_goal_5.
Proof.
  pre_process.
  rewrite Zlength_point_swap; auto.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1 : partition_xy_points_entail_wit_2_1.
Proof.
  right. intros. pre_process. split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_partition_scan_inv_accept_swap; eauto; lia.
    + dump_pre_spatial.
      apply points_in_bound_point_swap; auto; lia.
    + dump_pre_spatial.
      rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j) high_pre
                 __default_Point default_point)
        by (rewrite Zlength_point_swap; lia).
      rewrite point_swap_Znth_other_index by lia.
      rewrite (Znth_indep pts_cur_2 high_pre default_point __default_Point)
        by lia.
      auto.
    + dump_pre_spatial.
      rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j) high_pre
                 __default_Point default_point)
        by (rewrite Zlength_point_swap; lia).
      rewrite point_swap_Znth_other_index by lia.
      rewrite (Znth_indep pts_cur_2 high_pre default_point __default_Point)
        by lia.
      auto.
    + dump_pre_spatial.
      rewrite Zlength_point_swap; auto.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_2_split_goal_1 : partition_xy_points_entail_wit_2_2_split_goal_1.
Proof.
  pre_process.
  eapply point_xy_partition_scan_inv_accept_noswap; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_2 : partition_xy_points_entail_wit_2_2.
Proof.
  right. intros. pre_process. split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_partition_scan_inv_accept_noswap; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_3_split_goal_1 : partition_xy_points_entail_wit_2_3_split_goal_1.
Proof.
  pre_process.
  eapply point_xy_partition_scan_inv_reject_step; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_3 : partition_xy_points_entail_wit_2_3.
Proof.
  right. intros. pre_process. split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_partition_scan_inv_reject_step; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_1 : partition_xy_points_return_wit_1_split_goal_1.
Proof.
  pre_process.
  eapply worker_partition_finish_swap_partitioned; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_2 : partition_xy_points_return_wit_1_split_goal_2.
Proof.
  pre_process.
  eapply point_same_outside_range_point_swap_inside.
  - destruct PreH17 as [_ [Hsame _]]. exact Hsame.
  - rewrite PreH1; lia.
  - rewrite PreH1; lia.
  - lia.
  - lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_3 : partition_xy_points_return_wit_1_split_goal_3.
Proof.
  pre_process.
  destruct PreH17 as [Hperm _].
  unfold point_permutation in *.
  eapply Permutation_trans with (l' := pts_cur).
  - exact Hperm.
  - apply point_swap_permutation; rewrite PreH1; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_4 : partition_xy_points_return_wit_1_split_goal_4.
Proof.
  pre_process.
  apply points_in_bound_point_swap; auto; rewrite PreH1; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_5 : partition_xy_points_return_wit_1_split_goal_5.
Proof.
  pre_process.
  rewrite Zlength_point_swap; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1 : partition_xy_points_return_wit_1.
Proof.
  left.
  pre_process.
  Exists (point_swap pts_cur (i + 1) high_pre).
  split_pure_spatial.
  - cancel (PointArray.full pts_pre n_pre (point_swap pts_cur (i + 1) high_pre)).
  - repeat apply _derivable1_andp_intros;
    dump_pre_spatial;
    solve
      [ lia
      | rewrite Zlength_point_swap; lia
      | apply points_in_bound_point_swap; auto; rewrite PreH1; lia
      | destruct PreH17 as [Hperm _]; unfold point_permutation in *;
        eapply Permutation_trans with (l' := pts_cur);
        [ exact Hperm | apply point_swap_permutation; rewrite PreH1; lia ]
      | assert (Hsame : point_same_outside_range pts_l
                   (point_swap pts_cur (i + 1) high_pre) low_pre high_pre)
          by (eapply point_same_outside_range_point_swap_inside;
              [ destruct PreH17 as [_ [Hsame _]]; exact Hsame
              | rewrite PreH1; lia
              | rewrite PreH1; lia
              | lia
              | lia ]);
        exact Hsame
      | assert (Hsame : point_same_outside_range pts_l
                   (point_swap pts_cur (i + 1) high_pre) low_pre high_pre)
          by (eapply point_same_outside_range_point_swap_inside;
              [ destruct PreH17 as [_ [Hsame _]]; exact Hsame
              | rewrite PreH1; lia
              | rewrite PreH1; lia
              | lia
              | lia ]);
        unfold point_same_outside_range in Hsame; tauto
      | assert (Hpart : point_xy_partitioned_at
                   (point_swap pts_cur (i + 1) high_pre) low_pre high_pre (i + 1))
          by (eapply worker_partition_finish_swap_partitioned; eauto; lia);
        exact Hpart
      | assert (Hpart : point_xy_partitioned_at
                   (point_swap pts_cur (i + 1) high_pre) low_pre high_pre (i + 1))
          by (eapply worker_partition_finish_swap_partitioned; eauto; lia);
        unfold point_xy_partitioned_at in Hpart; tauto ].
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_1 : partition_xy_points_return_wit_2_split_goal_1.
Proof.
  pre_process.
  eapply worker_partition_finish_noswap_partitioned; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_2 : partition_xy_points_return_wit_2_split_goal_2.
Proof.
  pre_process.
  destruct PreH16 as [_ [Hsame _]]. exact Hsame.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_3 : partition_xy_points_return_wit_2_split_goal_3.
Proof.
  pre_process.
  destruct PreH16 as [Hperm _]. exact Hperm.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2 : partition_xy_points_return_wit_2.
Proof.
  left.
  pre_process.
  Exists pts_cur.
  split_pure_spatial.
  - cancel (PointArray.full pts_pre n_pre pts_cur).
  - repeat apply _derivable1_andp_intros;
    dump_pre_spatial;
    solve
      [ lia
      | exact PreH3
      | exact PreH14
      | destruct PreH16 as [Hperm _]; exact Hperm
      | destruct PreH16 as [_ [Hsame _]]; exact Hsame
      | destruct PreH16 as [_ [Hsame _]]; unfold point_same_outside_range in Hsame; tauto
      | assert (Hpart : point_xy_partitioned_at pts_cur low_pre high_pre (i + 1))
          by (eapply worker_partition_finish_noswap_partitioned; eauto; lia);
        exact Hpart
      | assert (Hpart : point_xy_partitioned_at pts_cur low_pre high_pre (i + 1))
          by (eapply worker_partition_finish_noswap_partitioned; eauto; lia);
        unfold point_xy_partitioned_at in Hpart; tauto ].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_1 : quicksort_xy_points_return_wit_1_split_goal_1.
Proof.
  pre_process.
  eapply point_xy_sorted_range_partition_merge_after_subsorts
    with (base := pts_out_2) (mid := pts_out_3) (p := retval);
    try eassumption; try lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_2 : quicksort_xy_points_return_wit_1_split_goal_2.
Proof.
  pre_process.
  eapply point_same_outside_range_trans.
  - exact PreH18.
  - eapply point_same_outside_range_trans.
    + eapply (point_same_outside_range_weaken
                pts_out_2 pts_out_3 left_pre (retval - 1) left_pre right_pre);
        [lia | lia | exact PreH10].
    + eapply (point_same_outside_range_weaken
                pts_out_3 pts_out_4 (retval + 1) right_pre left_pre right_pre);
        [lia | lia | exact PreH4].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_3 : quicksort_xy_points_return_wit_1_split_goal_3.
Proof.
  pre_process.
  unfold point_permutation in *.
  eapply Permutation_trans.
  - exact PreH17.
  - eapply Permutation_trans.
    + exact PreH9.
    + exact PreH3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1 : quicksort_xy_points_return_wit_1.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_sorted_range_partition_merge_after_subsorts
        with (base := pts_out_2) (mid := pts_out_3) (p := retval);
        try eassumption; try lia.
    + dump_pre_spatial.
      eapply point_same_outside_range_trans.
      * exact PreH18.
      * eapply point_same_outside_range_trans.
        -- eapply (point_same_outside_range_weaken
                     pts_out_2 pts_out_3 left_pre (retval - 1) left_pre right_pre);
           [lia | lia | exact PreH10].
        -- eapply (point_same_outside_range_weaken
                     pts_out_3 pts_out_4 (retval + 1) right_pre left_pre right_pre);
           [lia | lia | exact PreH4].
    + dump_pre_spatial.
      unfold point_permutation in *.
      eapply Permutation_trans.
      * exact PreH17.
      * eapply Permutation_trans.
        -- exact PreH9.
        -- exact PreH3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_1 : quicksort_xy_points_return_wit_2_split_goal_1.
Proof.
  pre_process.
  eapply point_xy_sorted_range_partition_merge_after_subsorts
    with (base := pts_out_2) (mid := pts_out_2) (p := retval);
    try eassumption; try lia.
  - apply Permutation_refl.
  - apply point_same_outside_range_refl.
  - apply point_xy_sorted_range_degenerate; lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_2 : quicksort_xy_points_return_wit_2_split_goal_2.
Proof.
  pre_process.
  eapply point_same_outside_range_trans.
  - exact PreH13.
  - eapply (point_same_outside_range_weaken
              pts_out_2 pts_out_3 (retval + 1) right_pre left_pre right_pre);
    [lia | lia | exact PreH4].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_3 : quicksort_xy_points_return_wit_2_split_goal_3.
Proof.
  pre_process.
  unfold point_permutation in *.
  eapply Permutation_trans.
  - exact PreH12.
  - exact PreH3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2 : quicksort_xy_points_return_wit_2.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_sorted_range_partition_merge_after_subsorts
        with (base := pts_out_2) (mid := pts_out_2) (p := retval);
        try eassumption; try lia.
      * apply Permutation_refl.
      * apply point_same_outside_range_refl.
      * apply point_xy_sorted_range_degenerate; lia.
    + dump_pre_spatial.
      eapply point_same_outside_range_trans.
      * exact PreH13.
      * eapply (point_same_outside_range_weaken
                  pts_out_2 pts_out_3 (retval + 1) right_pre left_pre right_pre);
        [lia | lia | exact PreH4].
    + dump_pre_spatial.
      unfold point_permutation in *.
      eapply Permutation_trans.
      * exact PreH12.
      * exact PreH3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_1 : quicksort_xy_points_return_wit_3_split_goal_1.
Proof.
  pre_process.
  eapply point_xy_sorted_range_partition_merge_after_subsorts
    with (base := pts_out_2) (mid := pts_out_3) (out := pts_out_3) (p := retval);
    try eassumption; try lia.
  - apply Permutation_refl.
  - apply point_same_outside_range_refl.
  - apply point_xy_sorted_range_degenerate; lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_2 : quicksort_xy_points_return_wit_3_split_goal_2.
Proof.
  pre_process.
  eapply point_same_outside_range_trans.
  - exact PreH13.
  - eapply (point_same_outside_range_weaken
              pts_out_2 pts_out_3 left_pre (retval - 1) left_pre right_pre);
    [lia | lia | exact PreH5].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_3 : quicksort_xy_points_return_wit_3_split_goal_3.
Proof.
  pre_process.
  unfold point_permutation in *.
  eapply Permutation_trans.
  - exact PreH12.
  - exact PreH4.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3 : quicksort_xy_points_return_wit_3.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_sorted_range_partition_merge_after_subsorts
        with (base := pts_out_2) (mid := pts_out_3) (out := pts_out_3) (p := retval);
        try eassumption; try lia.
      * apply Permutation_refl.
      * apply point_same_outside_range_refl.
      * apply point_xy_sorted_range_degenerate; lia.
    + dump_pre_spatial.
      eapply point_same_outside_range_trans.
      * exact PreH13.
      * eapply (point_same_outside_range_weaken
                  pts_out_2 pts_out_3 left_pre (retval - 1) left_pre right_pre);
        [lia | lia | exact PreH5].
    + dump_pre_spatial.
      unfold point_permutation in *.
      eapply Permutation_trans.
      * exact PreH12.
      * exact PreH4.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_1 : quicksort_xy_points_return_wit_4_split_goal_1.
Proof.
  pre_process.
  apply point_xy_sorted_range_degenerate; lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_2 : quicksort_xy_points_return_wit_4_split_goal_2.
Proof.
  pre_process.
  apply point_same_outside_range_refl.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_3 : quicksort_xy_points_return_wit_4_split_goal_3.
Proof.
  pre_process.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4 : quicksort_xy_points_return_wit_4.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    + dump_pre_spatial.
      apply point_xy_sorted_range_degenerate; lia.
    + dump_pre_spatial.
      apply point_same_outside_range_refl.
    + dump_pre_spatial.
      unfold point_permutation.
      apply Permutation_refl.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_1 : andrew_build_from_sorted_entail_wit_1_split_goal_1.
Proof.
  pre_process; dump_pre_spatial.
  unfold andrew_lower_cont, build_hull_c_iter.
  rewrite (sublist_self pts_l_low_level_spec (Zlength pts_l_low_level_spec)) by reflexivity.
  unfold andrew_monotone_chain_m in PreH7 at 1.
  unfold Andrew_Monotone_Chain_M.andrew_monotone_chain in PreH7 at 1.
  unfold Andrew_Monotone_Chain_M.build_andrew_hull in PreH7 at 1.
  prog_nf in PreH7.
  unfold Andrew_Monotone_Chain_M.build_lower_chain in PreH7 at 1.
  prog_nf in PreH7.
  unfold Andrew_Monotone_Chain_M.build_chain in PreH7 at 1.
  prog_nf in PreH7.
  apply safeExec_update'_bind in PreH7.
  eapply safeExec_conseq.
  - eapply (@safeExec_proequiv (list Point) unit
      (Graham_Scan_M.iter Graham_Scan_M.step_p pts_l_low_level_spec tt ;;
       lower <- (T <- get' id ;; StateRelMonad.ret (rev T)) ;;
       upper <- Andrew_Monotone_Chain_M.build_upper_chain pts_l_low_level_spec ;;
       update' (fun _ : list Point =>
         Andrew_Monotone_Chain.andrew_merge pts_l_low_level_spec lower upper))
      (Graham_Scan_M.iter Graham_Scan_M.step_p pts_l_low_level_spec tt ;;
       T <- get' id ;;
       upper <- Andrew_Monotone_Chain_M.build_upper_chain pts_l_low_level_spec ;;
       update' (fun _ : list Point =>
         Andrew_Monotone_Chain.andrew_merge pts_l_low_level_spec (rev T) upper))
      (fun s : list Point =>
         exists s0 : list Point, s = nil /\ equiv empty_point_stack s0)
      X_low_level_spec).
    + apply common_step_equiv; intros [].
      etransitivity.
      * apply bind_assoc.
      * apply common_step_equiv; intro T.
        apply (@bind_ret_left (list Point) (list Point) unit (rev T)
          (fun lower =>
             upper <- Andrew_Monotone_Chain_M.build_upper_chain pts_l_low_level_spec ;;
             update' (fun _ : list Point =>
               Andrew_Monotone_Chain.andrew_merge pts_l_low_level_spec lower upper))).
    + exact PreH7.
  - intros s [s0 [Hs Heq]].
    subst s.
    reflexivity.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_2 : andrew_build_from_sorted_entail_wit_1_split_goal_2.
Proof.
  pre_process; dump_pre_spatial.
  apply andrew_lower_scan_inv_nil.
  - rewrite PreH3. exact PreH1.
  - exact PreH4.
  - exact PreH5.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_3 : andrew_build_from_sorted_entail_wit_1_split_goal_3.
Proof.
  pre_process; dump_pre_spatial.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_spatial : andrew_build_from_sorted_entail_wit_1_split_goal_spatial.
Proof.
  pre_process.
  apply PointArray.undef_full_to_undef_seg.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1 : andrew_build_from_sorted_entail_wit_1.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - apply PointArray.undef_full_to_undef_seg.
  - split_pures.
    + eapply proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_1; eauto.
    + eapply proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_2; eauto.
    + eapply proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_3; eauto.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_2_split_goal_1 : andrew_build_from_sorted_entail_wit_2_split_goal_1.
Proof.
  pre_process; dump_pre_spatial.
  apply points_in_bound_Znth; auto; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_2_split_goal_spatial : andrew_build_from_sorted_entail_wit_2_split_goal_spatial.
Proof.
  pre_process.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_2 : andrew_build_from_sorted_entail_wit_2.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    dump_pre_spatial.
    apply points_in_bound_Znth; auto; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_3 : andrew_build_from_sorted_entail_wit_3.
Proof.
  right.
  pre_process.
  Exists (point_drop_last lower_2).
  assert (Htop_for_cross : k = Zlength lower_2).
  {
    pose proof PreH17 as Hinv0.
    unfold andrew_lower_scan_inv in Hinv0.
    tauto.
  }
  assert (Hcross_gen :
    point_cross
      (Znth (k - 2 - 0) lower_2 __default_Point)
      (Znth (k - 1 - 0) lower_2 __default_Point)
      (Znth i pts_sorted_2 __default_Point) <= 0).
  {
    rewrite point_cross_unfold.
    unfold point_cross_by_value in PreH2.
    simpl in *.
    rewrite PreH2 in PreH1.
    exact PreH1.
  }
  assert (Hcross :
    point_cross
      (Znth (k - 2) lower_2 default_point)
      (Znth (k - 1) lower_2 default_point)
      (Znth i pts_sorted_2 default_point) <= 0).
  {
    replace (Znth (k - 2) lower_2 default_point)
      with (Znth (k - 2 - 0) lower_2 __default_Point)
      by (rewrite (Znth_indep lower_2 (k - 2) default_point __default_Point) by lia;
          f_equal; lia).
    replace (Znth (k - 1) lower_2 default_point)
      with (Znth (k - 1 - 0) lower_2 __default_Point)
      by (rewrite (Znth_indep lower_2 (k - 1) default_point __default_Point) by lia;
          f_equal; lia).
    replace (Znth i pts_sorted_2 default_point)
      with (Znth i pts_sorted_2 __default_Point)
      by (apply Znth_indep; rewrite PreH12; lia).
    exact Hcross_gen.
	  }
	  assert (Hinv_pop : andrew_lower_scan_inv pts_sorted_2 (point_drop_last lower_2) i (k - 1)).
  {
    unfold andrew_lower_scan_inv in PreH17.
    destruct PreH17 as
      [Hread [Htop [Htop_bounds [Hbound [Hin Hexit_len]]]]].
    unfold andrew_lower_scan_inv.
    split; [exact Hread |].
    split; [rewrite point_drop_last_Zlength by lia; lia |].
    split; [lia |].
    split; [apply points_in_bound_drop_last; [lia | exact Hbound] |].
    split; [apply Forall_point_drop_last; [lia | exact Hin] |].
    intro Hdone.
    lia.
  }
  assert (Hcont_pop :
    safeExec (equiv (rev (point_drop_last lower_2)))
      (andrew_lower_cont pts_sorted_2 i) X_low_level_spec).
  {
    eapply safeExec_andrew_lower_cont_drop_last with (top := k);
      [exact Hcross | lia | lia | exact Htop_for_cross | rewrite PreH12; exact PreH5 | exact PreH18].
  }
  split_pure_spatial.
  - destruct (point_drop_last_decompose lower_2) as [prefix [last [Hlower Hdrop]]].
    { unfold andrew_lower_scan_inv in PreH17.
      destruct PreH17 as [_ [Htop _]].
      lia. }
    rewrite Hlower at 1.
    rewrite Hdrop.
    sep_apply_l_atomic (point_array_seg_pop_tail_at_k hull_pre k (2 * n_pre) prefix last).
    + dump_pre_spatial.
      rewrite <- Hdrop.
      rewrite point_drop_last_Zlength.
      * unfold andrew_lower_scan_inv in PreH17.
        destruct PreH17 as [_ [Htop _]].
        lia.
      * unfold andrew_lower_scan_inv in PreH17.
        destruct PreH17 as [_ [Htop _]].
        lia.
    + dump_pre_spatial.
      lia.
    + cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH11.
    + dump_pre_spatial. exact PreH12.
    + dump_pre_spatial. exact PreH13.
    + dump_pre_spatial. exact PreH14.
    + dump_pre_spatial. exact PreH15.
    + dump_pre_spatial. exact PreH16.
    + dump_pre_spatial. exact Hinv_pop.
    + dump_pre_spatial. exact Hcont_pop.
    + dump_pre_spatial.
      intro Hdone.
      rewrite PreH12 in Hdone.
      lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1 : andrew_build_from_sorted_entail_wit_4_1.
Proof.
  right.
  pre_process.
  assert (HZnth_default :
    Znth i pts_sorted_2 __default_Point =
    Znth i pts_sorted_2 default_point).
  {
    apply Znth_indep.
    rewrite PreH14; lia.
  }
  rewrite HZnth_default in *.
  pose proof PreH19 as Hlower_inv.
  unfold andrew_lower_scan_inv in Hlower_inv.
  destruct Hlower_inv as
    [Hread [Hk_len [Htop [Hlower_bound [Hlower_in Hlower_done]]]]].
  Exists (lower_2 ++ Znth i pts_sorted_2 default_point :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic
      (store_point_fold
         (hull_pre + k * sizeof("Point"))
         (Znth i pts_sorted_2 default_point)).
    eapply (point_array_seg_snoc_store_undef hull_pre k (2 * n_pre)
             lower_2 (Znth i pts_sorted_2 default_point));
      lia.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH11.
    + dump_pre_spatial. exact PreH12.
    + dump_pre_spatial. exact PreH13.
    + dump_pre_spatial. exact PreH14.
    + dump_pre_spatial. exact PreH15.
    + dump_pre_spatial. exact PreH16.
    + dump_pre_spatial. exact PreH17.
    + dump_pre_spatial.
      unfold andrew_lower_scan_inv.
      repeat split.
      * lia.
      * rewrite PreH14; lia.
      * replace (Zlength (lower_2 ++ Znth i pts_sorted_2 default_point :: nil))
          with (Zlength lower_2 + 1)
          by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
        lia.
      * lia.
      * lia.
      * apply points_in_bound_snoc_Znth; try assumption.
        rewrite PreH14; lia.
      * apply Forall_app.
        split; [exact Hlower_in |].
        constructor.
        -- apply Znth_In_range.
           rewrite PreH14; lia.
        -- constructor.
      * intros Hdone_new.
        assert (0 < i) by (rewrite PreH14 in Hdone_new; lia).
        specialize (PreH10 H).
        lia.
    + dump_pre_spatial.
      eapply (safeExec_andrew_lower_cont_short_push
                pts_sorted_2 lower_2 i k X_low_level_spec).
      * exact Hk_len.
      * exact PreH5.
      * exact PreH6.
      * rewrite PreH14; lia.
      * exact PreH20.
    + dump_pre_spatial.
      intros Hdone_new.
      assert (Hread_end : i + 1 = Zlength pts_sorted_2)
        by (rewrite PreH14 in Hdone_new; lia).
      replace (sublist ((k + 1) - 1)
                 (Zlength (lower_2 ++
                   Znth i pts_sorted_2 default_point :: nil))
                 (lower_2 ++ Znth i pts_sorted_2 default_point :: nil))
        with (Znth i pts_sorted_2 default_point :: nil).
      2:{
        replace ((k + 1) - 1) with k by lia.
        rewrite (sublist_split_app_r k
                   (Zlength (lower_2 ++
                     Znth i pts_sorted_2 default_point :: nil))
                   k lower_2
                   (Znth i pts_sorted_2 default_point :: nil)).
        - replace (k - k) with 0 by lia.
          replace (Zlength (lower_2 ++
                    Znth i pts_sorted_2 default_point :: nil) - k)
            with (Zlength (Znth i pts_sorted_2 default_point :: nil))
            by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
          symmetry.
          apply sublist_self.
          reflexivity.
        - symmetry; exact Hk_len.
        - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
      }
      replace (sublist 0 (k + 1)
                 (lower_2 ++ Znth i pts_sorted_2 default_point :: nil))
        with (lower_2 ++ Znth i pts_sorted_2 default_point :: nil).
      2:{
        symmetry.
        apply sublist_self.
        rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
      }
      simpl.
      eapply (safeExec_andrew_lower_cont_done_snoc_to_upper
                pts_sorted_2 lower_2 i X_low_level_spec).
      * exact Hread_end.
      * exact PreH6.
      * eapply (safeExec_andrew_lower_cont_short_push
                  pts_sorted_2 lower_2 i k X_low_level_spec).
        -- exact Hk_len.
        -- exact PreH5.
        -- exact PreH6.
        -- rewrite PreH14; lia.
        -- exact PreH20.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2 : andrew_build_from_sorted_entail_wit_4_2.
Proof.
  right.
  pre_process.
  assert (HZnth_default :
    Znth i pts_sorted_2 __default_Point =
    Znth i pts_sorted_2 default_point).
  {
    apply Znth_indep.
    rewrite PreH16; lia.
  }
  rewrite HZnth_default in *.
  pose proof PreH21 as Hlower_inv.
  unfold andrew_lower_scan_inv in Hlower_inv.
  destruct Hlower_inv as
    [Hread [Hk_len [Htop [Hlower_bound [Hlower_in Hlower_done]]]]].
  assert (Hcross_gen :
    point_cross
      (Znth (k - 2 - 0) lower_2 __default_Point)
      (Znth (k - 1 - 0) lower_2 __default_Point)
      (Znth i pts_sorted_2 default_point) > 0).
  {
    rewrite point_cross_unfold.
    unfold point_cross_by_value in PreH6.
    simpl in *.
    rewrite PreH6 in PreH5.
    exact PreH5.
  }
  assert (Hcross :
    point_cross
      (Znth (k - 2) lower_2 default_point)
      (Znth (k - 1) lower_2 default_point)
      (Znth i pts_sorted_2 default_point) > 0).
  {
    replace (Znth (k - 2) lower_2 default_point)
      with (Znth (k - 2 - 0) lower_2 __default_Point)
      by (rewrite (Znth_indep lower_2 (k - 2) default_point __default_Point) by lia;
          f_equal; lia).
    replace (Znth (k - 1) lower_2 default_point)
      with (Znth (k - 1 - 0) lower_2 __default_Point)
      by (rewrite (Znth_indep lower_2 (k - 1) default_point __default_Point) by lia;
          f_equal; lia).
    exact Hcross_gen.
  }
  Exists (lower_2 ++ Znth i pts_sorted_2 default_point :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic
      (store_point_fold
         (hull_pre + k * sizeof("Point"))
         (Znth i pts_sorted_2 default_point)).
    eapply (point_array_seg_snoc_store_undef hull_pre k (2 * n_pre)
             lower_2 (Znth i pts_sorted_2 default_point));
      lia.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH13.
    + dump_pre_spatial. exact PreH14.
    + dump_pre_spatial. exact PreH15.
    + dump_pre_spatial. exact PreH16.
    + dump_pre_spatial. exact PreH17.
    + dump_pre_spatial. exact PreH18.
    + dump_pre_spatial. exact PreH19.
    + dump_pre_spatial.
      unfold andrew_lower_scan_inv.
      repeat split.
      * lia.
      * rewrite PreH16; lia.
      * replace (Zlength (lower_2 ++ Znth i pts_sorted_2 default_point :: nil))
          with (Zlength lower_2 + 1)
          by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
        lia.
      * lia.
      * lia.
      * apply points_in_bound_snoc_Znth; try assumption.
        rewrite PreH16; lia.
      * apply Forall_app.
        split; [exact Hlower_in |].
        constructor.
        -- apply Znth_In_range.
           rewrite PreH16; lia.
        -- constructor.
      * intros Hdone_new.
        assert (0 < i) by (rewrite PreH16 in Hdone_new; lia).
        specialize (PreH12 H).
        lia.
    + dump_pre_spatial.
      eapply (safeExec_andrew_lower_cont_ccw_push
                pts_sorted_2 lower_2 i k X_low_level_spec).
      * exact Hk_len.
      * lia.
      * exact PreH8.
      * rewrite PreH16; lia.
      * exact Hcross.
      * exact PreH22.
    + dump_pre_spatial.
      intros Hdone_new.
      assert (Hread_end : i + 1 = Zlength pts_sorted_2)
        by (rewrite PreH16 in Hdone_new; lia).
      replace (sublist ((k + 1) - 1)
                 (Zlength (lower_2 ++
                   Znth i pts_sorted_2 default_point :: nil))
                 (lower_2 ++ Znth i pts_sorted_2 default_point :: nil))
        with (Znth i pts_sorted_2 default_point :: nil).
      2:{
        replace ((k + 1) - 1) with k by lia.
        rewrite (sublist_split_app_r k
                   (Zlength (lower_2 ++
                     Znth i pts_sorted_2 default_point :: nil))
                   k lower_2
                   (Znth i pts_sorted_2 default_point :: nil)).
        - replace (k - k) with 0 by lia.
          replace (Zlength (lower_2 ++
                    Znth i pts_sorted_2 default_point :: nil) - k)
            with (Zlength (Znth i pts_sorted_2 default_point :: nil))
            by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
          symmetry.
          apply sublist_self.
          reflexivity.
        - symmetry; exact Hk_len.
        - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
      }
      replace (sublist 0 (k + 1)
                 (lower_2 ++ Znth i pts_sorted_2 default_point :: nil))
        with (lower_2 ++ Znth i pts_sorted_2 default_point :: nil).
      2:{
        symmetry.
        apply sublist_self.
        rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
      }
      simpl.
      eapply (safeExec_andrew_lower_cont_done_snoc_to_upper
                pts_sorted_2 lower_2 i X_low_level_spec).
      * exact Hread_end.
      * exact PreH8.
      * eapply (safeExec_andrew_lower_cont_ccw_push
                  pts_sorted_2 lower_2 i k X_low_level_spec).
        -- exact Hk_len.
        -- lia.
        -- exact PreH8.
        -- rewrite PreH16; lia.
        -- exact Hcross.
        -- exact PreH22.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_1 : andrew_build_from_sorted_entail_wit_5_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  specialize (PreH16 ltac:(rewrite PreH10; lia)) as Hupper.
  replace (n_pre - 2 + 1) with (Zlength pts_sorted_2 - 1) by lia.
  exact Hupper.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_2 : andrew_build_from_sorted_entail_wit_5_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  assert (Hi_eq : i = n_pre) by lia.
  subst i.
  unfold andrew_lower_scan_inv in PreH14.
  destruct PreH14 as [_ [Hk_len [_ [Hbound [Hin Hexit]]]]].
  unfold andrew_upper_scan_inv, andrew_upper_capacity.
  repeat split.
  - lia.
  - rewrite PreH10; lia.
  - lia.
  - rewrite PreH10; lia.
  - exact Hk_len.
  - intro Hread_nonpos; lia.
  - exact Hbound.
  - exact Hin.
  - rewrite PreH10; lia.
  - rewrite <- Hk_len.
    rewrite PreH10.
    lia.
  - intro Hread_pos.
    rewrite <- Hk_len.
    rewrite PreH10.
    lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_3 : andrew_build_from_sorted_entail_wit_5_split_goal_3.
Proof.
	  pre_process.
	  dump_pre_spatial.
  match goal with
  | Hinv : andrew_lower_scan_inv _ _ _ _ |- _ =>
      unfold andrew_lower_scan_inv in Hinv;
      destruct Hinv as [_ [_ [_ [_ [_ Hexit_len]]]]]
  end.
  apply Hexit_len.
  rewrite PreH10.
  lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_spatial : andrew_build_from_sorted_entail_wit_5_split_goal_spatial.
Proof.
  pre_process.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5 : andrew_build_from_sorted_entail_wit_5.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - pre_process.
  - split_pures.
    + eapply proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_1; eauto.
      unfold point_permutation; reflexivity.
    + eapply proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_2; eauto.
      unfold point_permutation; reflexivity.
    + eapply proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_3; eauto.
      unfold point_permutation; reflexivity.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_6_split_goal_1 : andrew_build_from_sorted_entail_wit_6_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  apply points_in_bound_Znth; auto.
  rewrite PreH10; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_6_split_goal_2 : andrew_build_from_sorted_entail_wit_6_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold andrew_upper_scan_inv, andrew_upper_capacity in PreH14.
  intuition subst; rewrite PreH10 in *; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_6_split_goal_spatial : andrew_build_from_sorted_entail_wit_6_split_goal_spatial.
Proof.
  pre_process.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_6 : andrew_build_from_sorted_entail_wit_6.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - pre_process.
  - split_pures.
    + dump_pre_spatial.
      apply points_in_bound_Znth; auto.
      rewrite PreH10; lia.
    + dump_pre_spatial.
      unfold andrew_upper_scan_inv, andrew_upper_capacity in PreH14.
      intuition subst; rewrite PreH10 in *; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_7 : andrew_build_from_sorted_entail_wit_7.
Proof.
  right.
  pre_process.
  Exists (point_drop_last hull_cur_2).
  assert (Htop_for_cross : k = Zlength hull_cur_2).
  {
    pose proof PreH17 as Hinv0.
    unfold andrew_upper_scan_inv in Hinv0.
    tauto.
  }
  assert (Hcross_gen :
    point_cross
      (Znth (k - 2 - 0) hull_cur_2 __default_Point)
      (Znth (k - 1 - 0) hull_cur_2 __default_Point)
      (Znth i pts_sorted_2 __default_Point) <= 0).
  {
    rewrite point_cross_unfold.
    unfold point_cross_by_value in PreH2.
    simpl in *.
    rewrite PreH2 in PreH1.
    exact PreH1.
  }
  assert (Hcross :
    point_cross
      (Znth (k - 2) hull_cur_2 default_point)
      (Znth (k - 1) hull_cur_2 default_point)
      (Znth i pts_sorted_2 default_point) <= 0).
  {
    replace (Znth (k - 2) hull_cur_2 default_point)
      with (Znth (k - 2 - 0) hull_cur_2 __default_Point)
      by (rewrite (Znth_indep hull_cur_2 (k - 2) default_point __default_Point) by lia;
          f_equal; lia).
    replace (Znth (k - 1) hull_cur_2 default_point)
      with (Znth (k - 1 - 0) hull_cur_2 __default_Point)
      by (rewrite (Znth_indep hull_cur_2 (k - 1) default_point __default_Point) by lia;
          f_equal; lia).
    replace (Znth i pts_sorted_2 default_point)
      with (Znth i pts_sorted_2 __default_Point)
      by (apply Znth_indep; rewrite PreH12; lia).
    exact Hcross_gen.
  }
  assert (Hinv_pop :
    andrew_upper_scan_inv pts_sorted_2 (point_drop_last hull_cur_2)
      (i + 1) (k - 1) lower_n).
  {
    unfold andrew_upper_scan_inv in PreH17.
    destruct PreH17 as
      [Hread [Htop_bounds [Htop [Hprogress [Hbound [Hin Hcap]]]]]].
    unfold andrew_upper_scan_inv.
    split; [exact Hread |].
    split; [lia |].
    split; [rewrite point_drop_last_Zlength by lia; lia |].
    split; [intro Hdone; lia |].
    split; [apply points_in_bound_drop_last; [lia | exact Hbound] |].
    split; [apply Forall_point_drop_last; [lia | exact Hin] |].
    unfold andrew_upper_capacity in *.
    destruct Hcap as [Hlower_len [Hcap_len Hcap_strict]].
    repeat split; try lia.
    - rewrite point_drop_last_Zlength by lia.
      lia.
    - intro Hread_pos.
      rewrite point_drop_last_Zlength by lia.
      lia.
  }
  assert (Hlower_prefix :
    sublist 0 lower_n (point_drop_last hull_cur_2) =
    sublist 0 lower_n hull_cur_2).
  {
    unfold point_drop_last.
    rewrite Zsublist_Zsublist00 by lia.
    reflexivity.
  }
  assert (Hdrop_suffix :
    sublist (lower_n - 1) (Zlength (point_drop_last hull_cur_2))
      (point_drop_last hull_cur_2) =
    sublist (lower_n - 1) (k - 1) hull_cur_2).
  {
    rewrite point_drop_last_Zlength by lia.
    rewrite <- Htop_for_cross.
    unfold point_drop_last.
    rewrite Zsublist_Zsublist0 by lia.
    reflexivity.
  }
  assert (Hstack_len :
    2 <= Zlength (sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2)).
  {
    rewrite Zlength_sublist by lia.
    lia.
  }
  destruct (rev (sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2))
    as [| t rest] eqn:Hstack.
  {
    apply (f_equal (@rev Point)) in Hstack.
    rewrite rev_involutive in Hstack.
    simpl in Hstack.
    rewrite Hstack in Hstack_len.
    rewrite Zlength_nil in Hstack_len.
    lia.
  }
  destruct rest as [| s T].
  {
    apply (f_equal (@rev Point)) in Hstack.
    rewrite rev_involutive in Hstack.
    simpl in Hstack.
    rewrite Hstack in Hstack_len.
    rewrite Zlength_cons, Zlength_nil in Hstack_len.
    lia.
  }
  assert (Hsuffix_eq :
    sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2 =
    rev (t :: s :: T)).
  {
    apply (f_equal (@rev Point)) in Hstack.
    rewrite rev_involutive in Hstack.
    simpl in Hstack.
    exact Hstack.
  }
  assert (Htail_stack :
    rev (sublist (lower_n - 1) (k - 1) hull_cur_2) = s :: T).
  {
    assert (Horig_snoc :
      sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2 =
      sublist (lower_n - 1) (k - 1) hull_cur_2 ++
      Znth (k - 1) hull_cur_2 default_point :: nil).
    {
      rewrite (sublist_split (lower_n - 1) (Zlength hull_cur_2) (k - 1) hull_cur_2)
        by lia.
      replace (sublist (k - 1) (Zlength hull_cur_2) hull_cur_2)
        with (sublist (k - 1) (k - 1 + 1) hull_cur_2)
        by (rewrite <- Htop_for_cross; f_equal; lia).
      rewrite (sublist_single default_point (k - 1) hull_cur_2)
        by (rewrite <- Htop_for_cross; lia).
      reflexivity.
    }
    rewrite Horig_snoc in Hstack.
    rewrite rev_app_distr in Hstack.
    simpl in Hstack.
    inversion Hstack.
    reflexivity.
  }
  assert (Hnccw :
    ~ ccw s t (Znth ((i + 1) - 1) pts_sorted_2 default_point)).
  {
    replace (Znth ((i + 1) - 1) pts_sorted_2 default_point)
      with (Znth i pts_sorted_2 default_point) by (f_equal; lia).
    apply point_cross_le_0_not_ccw_local.
    assert (Hlen_for_rev :
      k - lower_n + 1 = Zlength (rev (t :: s :: T))).
    {
      rewrite <- Hsuffix_eq.
      rewrite Zlength_sublist by lia.
      lia.
    }
    replace (Znth (k - 2) hull_cur_2 default_point)
      with (Znth (k - lower_n - 1 - 0) (rev (t :: s :: T)) default_point)
      in Hcross.
    2:{
      rewrite <- Hsuffix_eq.
      rewrite Znth_sublist by lia.
      replace (k - lower_n - 1 - 0 + (lower_n - 1)) with (k - 2) by lia.
      reflexivity.
    }
    replace (Znth (k - 1) hull_cur_2 default_point)
      with (Znth (k - lower_n - 0) (rev (t :: s :: T)) default_point)
      in Hcross.
    2:{
      rewrite <- Hsuffix_eq.
      rewrite Znth_sublist by lia.
      replace (k - lower_n - 0 + (lower_n - 1)) with (k - 1) by lia.
      reflexivity.
    }
    rewrite (Znth_rev_stack_prev default_point t s T (k - lower_n)) in Hcross
      by exact Hlen_for_rev.
    rewrite (Znth_rev_stack_top default_point t s T (k - lower_n)) in Hcross
      by exact Hlen_for_rev.
    exact Hcross.
  }
  assert (Hcont_pop_raw :
    safeExec (equiv (s :: T))
      (andrew_upper_cont pts_sorted_2 (sublist 0 lower_n hull_cur_2) (i + 1))
      X_low_level_spec).
  {
    eapply safeExec_andrew_upper_cont_pop with (t := t).
    - lia.
    - rewrite PreH12; lia.
    - exact Hnccw.
    - exact PreH18.
  }
  assert (Hcont_pop :
    safeExec
      (equiv (rev (sublist (lower_n - 1)
        (Zlength (point_drop_last hull_cur_2)) (point_drop_last hull_cur_2))))
      (andrew_upper_cont pts_sorted_2
        (sublist 0 lower_n (point_drop_last hull_cur_2)) (i + 1))
      X_low_level_spec).
  {
    rewrite Hdrop_suffix.
    rewrite Htail_stack.
    rewrite Hlower_prefix.
    exact Hcont_pop_raw.
  }
  split_pure_spatial.
  - destruct (point_drop_last_decompose hull_cur_2) as [prefix [last [Hhull Hdrop]]].
    { lia. }
    rewrite Hhull at 1.
    rewrite Hdrop.
    sep_apply_l_atomic (point_array_seg_pop_tail_at_k hull_pre k (2 * n_pre) prefix last).
    + dump_pre_spatial.
      rewrite <- Hdrop.
      rewrite point_drop_last_Zlength.
      * lia.
      * lia.
    + dump_pre_spatial.
      lia.
    + cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH11.
    + dump_pre_spatial. exact PreH12.
    + dump_pre_spatial. exact PreH13.
    + dump_pre_spatial. exact PreH14.
    + dump_pre_spatial. exact PreH15.
    + dump_pre_spatial. exact PreH16.
    + dump_pre_spatial. exact Hinv_pop.
    + dump_pre_spatial. exact Hcont_pop.
Qed. 

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1 : andrew_build_from_sorted_entail_wit_8_1.
Proof.
  right.
  pre_process.
  assert (Hk_lower : k = lower_n) by lia.
  assert (HZnth_default :
    Znth i pts_sorted_2 __default_Point =
    Znth i pts_sorted_2 default_point).
  {
    apply Znth_indep.
    rewrite PreH14; lia.
  }
  rewrite HZnth_default in *.
  pose proof PreH19 as Hupper_inv.
  unfold andrew_upper_scan_inv in Hupper_inv.
  destruct Hupper_inv as
    [Hread [Htop_bounds [Htop [Hprogress [Hbound [Hin Hcap]]]]]].
  destruct Hcap as [Hlower_len [Hcap_len Hcap_strict]].
  assert (Hlen_hull : Zlength hull_cur_2 = lower_n) by lia.
  set (new_pt := Znth i pts_sorted_2 default_point).
  set (new_hull := hull_cur_2 ++ new_pt :: nil).
  assert (Hold_stack :
    rev (sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2) =
    Znth (lower_n - 1) hull_cur_2 default_point :: nil).
  {
    rewrite Hlen_hull.
    replace (sublist (lower_n - 1) lower_n hull_cur_2)
      with (sublist (lower_n - 1) ((lower_n - 1) + 1) hull_cur_2)
      by (f_equal; lia).
    rewrite (sublist_single default_point (lower_n - 1) hull_cur_2)
      by (rewrite Hlen_hull; lia).
    simpl.
    reflexivity.
  }
  assert (Hnew_suffix :
    sublist (lower_n - 1) (Zlength new_hull) new_hull =
    Znth (lower_n - 1) hull_cur_2 default_point :: new_pt :: nil).
  {
    subst new_hull.
    replace (Zlength (hull_cur_2 ++ new_pt :: nil)) with (lower_n + 1)
      by (rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen_hull; lia).
    rewrite (sublist_split (lower_n - 1) (lower_n + 1) lower_n
               (hull_cur_2 ++ new_pt :: nil)) by
      (try rewrite Zlength_app; try rewrite Zlength_cons;
       try rewrite Zlength_nil; try rewrite Hlen_hull; lia).
    rewrite (sublist_split_app_l (lower_n - 1) lower_n
               hull_cur_2 (new_pt :: nil)) by (try rewrite Hlen_hull; lia).
    replace (sublist (lower_n - 1) lower_n hull_cur_2)
      with (sublist (lower_n - 1) ((lower_n - 1) + 1) hull_cur_2)
      by (f_equal; lia).
    rewrite (sublist_single default_point (lower_n - 1) hull_cur_2)
      by (rewrite Hlen_hull; lia).
    rewrite (sublist_split_app_r lower_n (lower_n + 1) lower_n
               hull_cur_2 (new_pt :: nil)) by (try rewrite Hlen_hull; lia).
    replace (lower_n - lower_n) with 0 by lia.
    replace (lower_n + 1 - lower_n) with 1 by lia.
    replace (sublist 0 1 (new_pt :: nil)) with (new_pt :: nil).
    - reflexivity.
    - symmetry.
      apply sublist_self.
      rewrite Zlength_cons, Zlength_nil; lia.
  }
  assert (Hnew_stack :
    rev (sublist (lower_n - 1) (Zlength new_hull) new_hull) =
    new_pt :: Znth (lower_n - 1) hull_cur_2 default_point :: nil).
  {
    rewrite Hnew_suffix.
    simpl.
    reflexivity.
  }
  assert (Hlower_prefix_new :
    sublist 0 lower_n new_hull = sublist 0 lower_n hull_cur_2).
  {
    subst new_hull.
    rewrite (sublist_split_app_l 0 lower_n hull_cur_2 (new_pt :: nil))
      by (try rewrite Hlen_hull; lia).
    reflexivity.
  }
  assert (Hcont_single :
    safeExec
      (equiv (Znth (lower_n - 1) hull_cur_2 default_point :: nil))
      (andrew_upper_cont pts_sorted_2 (sublist 0 lower_n hull_cur_2)
        (i + 1)) X_low_level_spec).
  {
    rewrite <- Hold_stack.
    exact PreH20.
  }
  assert (Hcont_push_raw :
    safeExec
      (equiv (new_pt :: Znth (lower_n - 1) hull_cur_2 default_point :: nil))
      (andrew_upper_cont pts_sorted_2 (sublist 0 lower_n hull_cur_2) i)
      X_low_level_spec).
  {
    subst new_pt.
    replace i with ((i + 1) - 1) by lia.
    eapply (safeExec_andrew_upper_cont_single_push
              pts_sorted_2 (sublist 0 lower_n hull_cur_2) (i + 1)
              (Znth (lower_n - 1) hull_cur_2 default_point)
              X_low_level_spec).
    - lia.
    - rewrite PreH14; lia.
    - exact Hcont_single.
  }
  assert (Hcont_push :
    safeExec
      (equiv (rev (sublist (lower_n - 1) (Zlength new_hull) new_hull)))
      (andrew_upper_cont pts_sorted_2 (sublist 0 lower_n new_hull)
        ((i - 1) + 1)) X_low_level_spec).
  {
    rewrite Hnew_stack.
    rewrite Hlower_prefix_new.
    replace ((i - 1) + 1) with i by lia.
    exact Hcont_push_raw.
  }
  assert (Hcap_push :
    andrew_upper_capacity pts_sorted_2 new_hull i lower_n).
  {
    subst new_hull new_pt.
    unfold andrew_upper_capacity.
    split.
    - exact Hlower_len.
    - split.
      + rewrite Zlength_app, Zlength_cons, Zlength_nil.
        rewrite PreH14.
        lia.
      + intro Hread_pos.
        rewrite Zlength_app, Zlength_cons, Zlength_nil.
        rewrite PreH14.
        lia.
  }
  assert (Hinv_push :
    andrew_upper_scan_inv pts_sorted_2 new_hull i (k + 1) lower_n).
  {
    subst new_hull new_pt.
    unfold andrew_upper_scan_inv.
    split.
    - split; [lia | rewrite PreH14; lia].
    - split.
      + split; [lia | rewrite PreH14; lia].
      + split.
        * rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
        * split.
          -- intro Hread_done; lia.
          -- split.
             ++ apply points_in_bound_snoc_Znth; try assumption.
                rewrite PreH14; lia.
             ++ split.
                ** apply Forall_app.
                   split; [exact Hin |].
                   constructor.
                   --- apply Znth_In_range.
                       rewrite PreH14; lia.
                   --- constructor.
                ** exact Hcap_push.
  }
  Exists new_hull.
  split_pure_spatial.
  - subst new_hull new_pt.
    sep_apply_l_atomic
      (store_point_fold
         (hull_pre + k * sizeof("Point"))
         (Znth i pts_sorted_2 default_point)).
    eapply (point_array_seg_snoc_store_undef hull_pre k (2 * n_pre)
             hull_cur_2 (Znth i pts_sorted_2 default_point));
      lia.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH13.
    + dump_pre_spatial. exact PreH14.
    + dump_pre_spatial. exact PreH15.
    + dump_pre_spatial. exact PreH16.
    + dump_pre_spatial. exact PreH17.
    + dump_pre_spatial.
      replace ((i - 1) + 1) with i by lia.
      exact Hinv_push.
    + dump_pre_spatial. exact Hcont_push.
Qed. 

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2 : andrew_build_from_sorted_entail_wit_8_2.
Proof.
  right.
  pre_process.
  assert (HZnth_default :
    Znth i pts_sorted_2 __default_Point =
    Znth i pts_sorted_2 default_point).
  {
    apply Znth_indep.
    rewrite PreH16; lia.
  }
  rewrite HZnth_default in *.
  pose proof PreH21 as Hupper_inv.
  unfold andrew_upper_scan_inv in Hupper_inv.
  destruct Hupper_inv as
    [Hread [Htop_bounds [Htop [Hprogress [Hbound [Hin Hcap]]]]]].
  destruct Hcap as [Hlower_len [Hcap_len Hcap_strict]].
  assert (Hlen_hull : Zlength hull_cur_2 = k) by lia.
  set (new_pt := Znth i pts_sorted_2 default_point).
  set (new_hull := hull_cur_2 ++ new_pt :: nil).
  assert (Hcross_gen :
    point_cross
      (Znth (k - 2 - 0) hull_cur_2 __default_Point)
      (Znth (k - 1 - 0) hull_cur_2 __default_Point)
      (Znth i pts_sorted_2 default_point) > 0).
  {
    rewrite point_cross_unfold.
    unfold point_cross_by_value in PreH6.
    simpl in *.
    rewrite PreH6 in PreH5.
    exact PreH5.
  }
  assert (Hcross :
    point_cross
      (Znth (k - 2) hull_cur_2 default_point)
      (Znth (k - 1) hull_cur_2 default_point)
      (Znth i pts_sorted_2 default_point) > 0).
  {
    replace (Znth (k - 2) hull_cur_2 default_point)
      with (Znth (k - 2 - 0) hull_cur_2 __default_Point)
      by (rewrite (Znth_indep hull_cur_2 (k - 2) default_point __default_Point)
            by lia; f_equal; lia).
    replace (Znth (k - 1) hull_cur_2 default_point)
      with (Znth (k - 1 - 0) hull_cur_2 __default_Point)
      by (rewrite (Znth_indep hull_cur_2 (k - 1) default_point __default_Point)
            by lia; f_equal; lia).
    exact Hcross_gen.
  }
  assert (Hnew_suffix :
    sublist (lower_n - 1) (Zlength new_hull) new_hull =
    sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2 ++ new_pt :: nil).
  {
    subst new_hull.
    replace (Zlength (hull_cur_2 ++ new_pt :: nil)) with (k + 1)
      by (rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen_hull; lia).
    rewrite (sublist_split (lower_n - 1) (k + 1) k
               (hull_cur_2 ++ new_pt :: nil)) by
      (try rewrite Zlength_app; try rewrite Zlength_cons;
       try rewrite Zlength_nil; try rewrite Hlen_hull; lia).
    rewrite (sublist_split_app_l (lower_n - 1) k
               hull_cur_2 (new_pt :: nil)) by (try rewrite Hlen_hull; lia).
    rewrite (sublist_split_app_r k (k + 1) k
               hull_cur_2 (new_pt :: nil)) by (try rewrite Hlen_hull; lia).
    replace (k - k) with 0 by lia.
    replace (k + 1 - k) with 1 by lia.
    replace (sublist 0 1 (new_pt :: nil)) with (new_pt :: nil).
    - rewrite Hlen_hull.
      reflexivity.
    - symmetry.
      apply sublist_self.
      rewrite Zlength_cons, Zlength_nil; lia.
  }
  assert (Hlower_prefix_new :
    sublist 0 lower_n new_hull = sublist 0 lower_n hull_cur_2).
  {
    subst new_hull.
    rewrite (sublist_split_app_l 0 lower_n hull_cur_2 (new_pt :: nil))
      by (try rewrite Hlen_hull; lia).
    reflexivity.
  }
  assert (Hcross_suffix :
    point_cross
      (Znth (Zlength (sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2) - 2)
         (sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2) default_point)
      (Znth (Zlength (sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2) - 1)
         (sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2) default_point)
      (Znth ((i + 1) - 1) pts_sorted_2 default_point) > 0).
  {
    rewrite Zlength_sublist by lia.
    replace (k - (lower_n - 1) - 2) with (k - lower_n - 1) by lia.
    replace (k - (lower_n - 1) - 1) with (k - lower_n) by lia.
    replace (Znth ((i + 1) - 1) pts_sorted_2 default_point)
      with (Znth i pts_sorted_2 default_point) by (f_equal; lia).
    rewrite Znth_sublist by lia.
    rewrite Znth_sublist by lia.
    replace (Zlength hull_cur_2 - (lower_n - 1) - 2 + (lower_n - 1))
      with (k - 2) by lia.
    replace (Zlength hull_cur_2 - (lower_n - 1) - 1 + (lower_n - 1))
      with (k - 1) by lia.
    exact Hcross.
  }
  assert (Hcont_push_raw :
    safeExec
      (equiv (rev (sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2 ++
                    Znth ((i + 1) - 1) pts_sorted_2 default_point :: nil)))
      (andrew_upper_cont pts_sorted_2 (sublist 0 lower_n hull_cur_2)
        ((i + 1) - 1)) X_low_level_spec).
  {
    eapply (safeExec_andrew_upper_cont_ccw_push
              pts_sorted_2 (sublist 0 lower_n hull_cur_2)
              (sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2)
              (i + 1)
              (Zlength (sublist (lower_n - 1) (Zlength hull_cur_2) hull_cur_2))
              X_low_level_spec).
    - reflexivity.
    - rewrite Zlength_sublist by lia. lia.
    - lia.
    - rewrite PreH16; lia.
    - exact Hcross_suffix.
    - exact PreH22.
  }
  assert (Hcont_push :
    safeExec
      (equiv (rev (sublist (lower_n - 1) (Zlength new_hull) new_hull)))
      (andrew_upper_cont pts_sorted_2 (sublist 0 lower_n new_hull)
        ((i - 1) + 1)) X_low_level_spec).
  {
    rewrite Hnew_suffix.
    rewrite Hlower_prefix_new.
    replace ((i - 1) + 1) with ((i + 1) - 1) by lia.
    subst new_pt.
    replace (Znth i pts_sorted_2 default_point)
      with (Znth ((i + 1) - 1) pts_sorted_2 default_point) by (f_equal; lia).
    exact Hcont_push_raw.
  }
  assert (Hcap_push :
    andrew_upper_capacity pts_sorted_2 new_hull i lower_n).
  {
    subst new_hull new_pt.
    unfold andrew_upper_capacity.
    split.
    - exact Hlower_len.
    - split.
      + rewrite Zlength_app, Zlength_cons, Zlength_nil.
        rewrite PreH16.
        lia.
      + intro Hread_pos.
        rewrite Zlength_app, Zlength_cons, Zlength_nil.
        rewrite PreH16.
        lia.
  }
  assert (Hinv_push :
    andrew_upper_scan_inv pts_sorted_2 new_hull i (k + 1) lower_n).
  {
    subst new_hull new_pt.
    unfold andrew_upper_scan_inv.
    split.
    - split; [lia | rewrite PreH16; lia].
    - split.
      + split; [lia | rewrite PreH16; lia].
      + split.
        * rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
        * split.
          -- intro Hread_done; lia.
          -- split.
             ++ apply points_in_bound_snoc_Znth; try assumption.
                rewrite PreH16; lia.
             ++ split.
                ** apply Forall_app.
                   split; [exact Hin |].
                   constructor.
                   --- apply Znth_In_range.
                       rewrite PreH16; lia.
                   --- constructor.
                ** exact Hcap_push.
  }
  Exists new_hull.
  split_pure_spatial.
  - subst new_hull new_pt.
    sep_apply_l_atomic
      (store_point_fold
         (hull_pre + k * sizeof("Point"))
         (Znth i pts_sorted_2 default_point)).
    eapply (point_array_seg_snoc_store_undef hull_pre k (2 * n_pre)
             hull_cur_2 (Znth i pts_sorted_2 default_point));
      lia.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH13.
    + dump_pre_spatial. exact PreH14.
    + dump_pre_spatial. exact PreH15.
    + dump_pre_spatial. exact PreH16.
    + dump_pre_spatial. exact PreH17.
    + dump_pre_spatial. exact PreH18.
    + dump_pre_spatial. exact PreH19.
    + dump_pre_spatial.
      replace ((i - 1) + 1) with i by lia.
      exact Hinv_push.
    + dump_pre_spatial. exact Hcont_push.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_9 : andrew_build_from_sorted_entail_wit_9.
Proof.
  right.
  pre_process.
  Exists (point_drop_last hull_cur).
  assert (Hread0 : i + 1 = 0) by lia.
  pose proof PreH14 as Hupper_inv.
  unfold andrew_upper_scan_inv in Hupper_inv.
  destruct Hupper_inv as
    [Hread [Htop_bounds [Htop [Hprogress [Hbound [Hin Hcap]]]]]].
  assert (Hlower_lt : lower_n < k).
  {
    specialize (Hprogress ltac:(lia)).
    lia.
  }
  assert (Hfinal :
    safeExec (equiv (rev (point_drop_last hull_cur)))
      (return tt) X_low_level_spec).
  {
    rewrite Hread0 in PreH15.
    eapply (safeExec_andrew_upper_cont_done_point_drop_last
              pts_sorted_2 hull_cur lower_n X_low_level_spec).
    - rewrite PreH10. lia.
    - lia.
    - rewrite <- Htop. exact Hlower_lt.
    - exact PreH15.
  }
  split_pure_spatial.
  - destruct (point_drop_last_decompose hull_cur) as [prefix [last [Hhull Hdrop]]].
    { lia. }
    rewrite Hhull at 1.
    rewrite Hdrop.
    sep_apply_l_atomic (point_array_seg_pop_tail_at_k hull_pre k (2 * n_pre) prefix last).
    + dump_pre_spatial.
      rewrite <- Hdrop.
      rewrite point_drop_last_Zlength; lia.
    + dump_pre_spatial.
      lia.
    + cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial.
      rewrite point_drop_last_Zlength; lia.
    + dump_pre_spatial. exact PreH11.
    + dump_pre_spatial. exact PreH12.
    + dump_pre_spatial. exact PreH13.
    + dump_pre_spatial. exact Hfinal.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_1 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      match goal with
      | Hinv : andrew_lower_scan_inv _ _ _ _ |- _ =>
          unfold andrew_lower_scan_inv in Hinv;
          destruct Hinv as [_ [Hlen [_ [Hbound _]]]]
      end;
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength xs) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_2 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      match goal with
      | Hinv : andrew_lower_scan_inv _ _ _ _ |- _ =>
          unfold andrew_lower_scan_inv in Hinv;
          destruct Hinv as [_ [Hlen [_ [Hbound _]]]]
      end;
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength xs) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_3 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      match goal with
      | Hinv : andrew_lower_scan_inv _ _ _ _ |- _ =>
          unfold andrew_lower_scan_inv in Hinv;
          destruct Hinv as [_ [Hlen [_ [Hbound _]]]]
      end;
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength xs) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_4 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_4.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      match goal with
      | Hinv : andrew_lower_scan_inv _ _ _ _ |- _ =>
          unfold andrew_lower_scan_inv in Hinv;
          destruct Hinv as [_ [Hlen [_ [Hbound _]]]]
      end;
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength xs) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_5 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_5.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      match goal with
      | Hinv : andrew_lower_scan_inv _ _ _ _ |- _ =>
          unfold andrew_lower_scan_inv in Hinv;
          destruct Hinv as [_ [Hlen [_ [Hbound _]]]]
      end;
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength xs) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_6 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_6.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      match goal with
      | Hinv : andrew_lower_scan_inv _ _ _ _ |- _ =>
          unfold andrew_lower_scan_inv in Hinv;
          destruct Hinv as [_ [Hlen [_ [Hbound _]]]]
      end;
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength xs) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_7 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_7.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      match goal with
      | Hinv : andrew_lower_scan_inv _ _ _ _ |- _ =>
          unfold andrew_lower_scan_inv in Hinv;
          destruct Hinv as [_ [Hlen [_ [Hbound _]]]]
      end;
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength xs) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_8 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_8.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      match goal with
      | Hinv : andrew_lower_scan_inv _ _ _ _ |- _ =>
          unfold andrew_lower_scan_inv in Hinv;
          destruct Hinv as [_ [Hlen [_ [Hbound _]]]]
      end;
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength xs) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_9 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_9.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | Hpt : point_in_bound _ |- _ =>
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound in Hpt;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]]
  end.
  unfold point_bound, Point_Order.point_bound.
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_10 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_10.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | Hpt : point_in_bound _ |- _ =>
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound in Hpt;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]]
  end.
  unfold point_bound, Point_Order.point_bound.
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_11 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_11.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | Hpt : point_in_bound _ |- _ =>
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound in Hpt;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]]
  end.
  unfold point_bound, Point_Order.point_bound.
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_12 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_12.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | Hpt : point_in_bound _ |- _ =>
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound in Hpt;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]]
  end.
  unfold point_bound, Point_Order.point_bound.
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure : andrew_build_from_sorted_partial_solve_wit_7_pure.
Proof.
  right.
  intros.
  pre_process.
  repeat apply _derivable1_andp_intros.
  all:
    try (dump_pre_spatial;
         match goal with
         | |- context [Znth ?idx ?xs ?d] =>
             match goal with
             | Hinv : andrew_lower_scan_inv _ _ _ _ |- _ =>
                 unfold andrew_lower_scan_inv in Hinv;
                 destruct Hinv as [_ [Hlen [_ [Hbound _]]]]
             end;
             pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
             assert (0 <= idx < Zlength xs) by lia;
             specialize (Hpt H);
             unfold point_in_bound, Point_Order.point_in_bound in Hpt;
             unfold point_bound, Point_Order.point_bound;
             destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
             try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
         end).
  all:
    dump_pre_spatial;
    match goal with
    | Hpt : point_in_bound _ |- _ =>
        unfold point_in_bound, Point_Order.point_in_bound in Hpt;
        unfold point_bound, Point_Order.point_bound in Hpt;
        destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]]
    end;
    unfold point_bound, Point_Order.point_bound;
    try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_1 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [_ [Hbound _]]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_2 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [_ [Hbound _]]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_3 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [_ [Hbound _]]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_4 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_4.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [_ [Hbound _]]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_5 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_5.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [_ [Hbound _]]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_6 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_6.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [_ [Hbound _]]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_7 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_7.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [_ [Hbound _]]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_8 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_8.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [_ [Hbound _]]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_9 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_9.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH22.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH22 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_10 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_10.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH22.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH22 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_11 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_11.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH22.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH22 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_12 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_12.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH22.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH22 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure : andrew_build_from_sorted_partial_solve_wit_20_pure.
Proof.
  right.
  intros.
  pre_process.
  repeat apply _derivable1_andp_intros.
  all:
    try (dump_pre_spatial;
         match goal with
         | |- context [Znth ?idx ?xs ?d] =>
             unfold andrew_upper_scan_inv in PreH23;
             destruct PreH23 as [_ [_ [Hlen [_ [Hbound _]]]]];
             pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
             assert (0 <= idx < Zlength hull_cur) by lia;
             specialize (Hpt H);
             unfold point_in_bound, Point_Order.point_in_bound in Hpt;
             unfold point_bound, Point_Order.point_bound;
             destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
             try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
         end).
  all:
    dump_pre_spatial;
    unfold point_in_bound, Point_Order.point_in_bound in PreH22;
    unfold point_bound, Point_Order.point_bound;
    destruct PreH22 as [[Hxlo Hxhi] [Hylo Hyhi]];
    try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_monotone_chain_entail_wit_1_split_goal_1 : andrew_monotone_chain_entail_wit_1_split_goal_1.
Proof.
  pre_process. unfold point_xy_sorted. rewrite PreH1. exact PreH5.
Qed.

Lemma proof_of_andrew_monotone_chain_entail_wit_1_split_goal_2 : andrew_monotone_chain_entail_wit_1_split_goal_2.
Proof.
  pre_process.
  eapply points_not_all_same_permutation_worker; eauto.
Qed.

Lemma proof_of_andrew_monotone_chain_entail_wit_1 : andrew_monotone_chain_entail_wit_1.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - pre_process.
  - split_pures.
    + dump_pre_spatial. unfold point_xy_sorted. rewrite PreH1. exact PreH5.
    + dump_pre_spatial. eapply points_not_all_same_permutation_worker; eauto.
Qed.

Lemma proof_of_andrew_monotone_chain_return_wit_1_split_goal_1 : andrew_monotone_chain_return_wit_1_split_goal_1.
Proof.
  pre_process. dump_pre_spatial.
  eapply is_convex_hull_base_permutation; eauto.
Qed.

Lemma proof_of_andrew_monotone_chain_return_wit_1_split_goal_2 : andrew_monotone_chain_return_wit_1_split_goal_2.
Proof.
  pre_process. dump_pre_spatial.
  eapply Permutation_trans; eauto.
Qed.

Lemma proof_of_andrew_monotone_chain_return_wit_1_split_goal_spatial : andrew_monotone_chain_return_wit_1_split_goal_spatial.
Proof. pre_process. Qed.

Lemma proof_of_andrew_monotone_chain_return_wit_1 : andrew_monotone_chain_return_wit_1.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - pre_process.
  - split_pures.
    + dump_pre_spatial. eapply is_convex_hull_base_permutation; eauto.
    + dump_pre_spatial. eapply Permutation_trans; eauto.
Qed.

Lemma proof_of_andrew_build_from_sorted_derive_high_level_spec_by_low_level_spec : andrew_build_from_sorted_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists pts_l_high_level_spec.
  Exists (result_state (equiv empty_point_stack)
    (andrew_monotone_chain_m pts_l_high_level_spec)).
  split_pure_spatial.
  - cancel (PointArray.full pts_pre n_pre pts_l_high_level_spec).
    cancel (PointArray.undef_full hull_pre (2 * n_pre)).
    apply derivable1_wand_sepcon_adjoint.
    pre_process.
    Intros hull_out_2.
    Intros pts_out_2.
    Intros retval_2.
    pre_process.
    Exists hull_out_2.
    Exists pts_out_2.
    Exists retval_2.
    split_pure_spatial.
    + pre_process.
    + split_pures.
      * dump_pre_spatial. exact H5.
      * dump_pre_spatial. exact H6.
      * dump_pre_spatial. exact H7.
      * dump_pre_spatial. exact H8.
	      * dump_pre_spatial. exact H9.
	      * dump_pre_spatial. exact H10.
	      * dump_pre_spatial. exact H11.
	      * dump_pre_spatial.
	        change (result_state (equiv empty_point_stack)
	          (andrew_monotone_chain_m pts_l_high_level_spec))
	          with (fun _ : unit => result_state (equiv empty_point_stack)
	            (andrew_monotone_chain_m pts_l_high_level_spec) tt) in H12.
	        destruct (safeExec_ret_tt _ _ H12) as [s [Heq Hres]].
        change (rev hull_out_2 = s) in Heq.
        subst s.
        pose proof (Hoare_result_state
          (fun _ : list Point =>
            Andrew_Monotone_Chain.point_xy_sorted pts_l_high_level_spec /\
            Andrew_Monotone_Chain.point_list_non_singleton pts_l_high_level_spec)
          (andrew_monotone_chain_m pts_l_high_level_spec)
          (fun (_ : unit) (T : list Point) =>
            T = Andrew_Monotone_Chain.andrew_hull pts_l_high_level_spec /\
            Maximality.is_convex_hull pts_l_high_level_spec T)
          (Andrew_Monotone_Chain_M.andrew_monotone_chain_correct pts_l_high_level_spec)) as Hrs.
        specialize (Hrs tt (rev hull_out_2)) as Hrs.
        unfold is_convex_hull.
        right.
        apply Hrs.
        destruct Hres as [s0 [Hs0 Hc]].
        exists s0. split.
        -- split.
           ++ apply public_point_xy_sorted_to_andrew_worker. exact H4.
           ++ apply points_not_all_same_non_singleton_worker. exact H3.
        -- exact Hc.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. exact H4.
    + dump_pre_spatial.
      apply safeExec_result_state.
      exists empty_point_stack.
      unfold equiv.
      reflexivity.
Qed.
