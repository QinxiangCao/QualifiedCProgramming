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
From SimpleC.EE.LLM_bench.Algorithms.convex_hull_float Require Import convex_hull_float_goal.
From SimpleC.EE.LLM_bench.Algorithms.convex_hull_float Require Import convex_hull_float_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.convex_hull_float.convex_hull_float_lib.
Local Open Scope sac.

Lemma proof_of_point_cmp_xy_safety_wit_1_split_goal_1 : point_cmp_xy_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_finite in PreH1; cbn in PreH1.
  destruct PreH1 as [Hax _].
  dump_pre_spatial.
  exact Hax.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_1_split_goal_2 : point_cmp_xy_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_finite in PreH2; cbn in PreH2.
  destruct PreH2 as [Hbx _].
  dump_pre_spatial.
  exact Hbx.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_1 : point_cmp_xy_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_4_split_goal_1 : point_cmp_xy_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_finite in PreH2; cbn in PreH2.
  destruct PreH2 as [Hax _].
  dump_pre_spatial.
  exact Hax.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_4_split_goal_2 : point_cmp_xy_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_finite in PreH3; cbn in PreH3.
  destruct PreH3 as [Hbx _].
  dump_pre_spatial.
  exact Hbx.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_4 : point_cmp_xy_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_6_split_goal_1 : point_cmp_xy_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_finite in PreH3; cbn in PreH3.
  destruct PreH3 as [_ Hay].
  dump_pre_spatial.
  exact Hay.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_6_split_goal_2 : point_cmp_xy_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_finite in PreH4; cbn in PreH4.
  destruct PreH4 as [_ Hby].
  dump_pre_spatial.
  exact Hby.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_6 : point_cmp_xy_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_9_split_goal_1 : point_cmp_xy_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_finite in PreH4; cbn in PreH4.
  destruct PreH4 as [_ Hay].
  dump_pre_spatial.
  exact Hay.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_9_split_goal_2 : point_cmp_xy_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_finite in PreH5; cbn in PreH5.
  destruct PreH5 as [_ Hby].
  dump_pre_spatial.
  exact Hby.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_9 : point_cmp_xy_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_1_split_goal_1 : point_cmp_xy_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cmp_xy, fp32_le, fp32_ge in *; simpl in *.
  destruct (fp32_compare ax_pre bx_pre) as [[]|] eqn:Hx; simpl in *; try contradiction.
  destruct (fp32_compare ay_pre b_y_pre) as [[]|] eqn:Hy; simpl in *; try contradiction;
    reflexivity.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_1 : point_cmp_xy_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_2_split_goal_1 : point_cmp_xy_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cmp_xy, fp32_le, fp32_ge, fp32_gt in *; simpl in *.
  destruct (fp32_compare ax_pre bx_pre) as [[]|] eqn:Hx; simpl in *; try contradiction.
  rewrite PreH1.
  reflexivity.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_2 : point_cmp_xy_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_3_split_goal_1 : point_cmp_xy_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cmp_xy, fp32_le, fp32_ge, fp32_lt in *; simpl in *.
  destruct (fp32_compare ax_pre bx_pre) as [[]|] eqn:Hx; simpl in *; try contradiction.
  rewrite PreH1.
  reflexivity.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_3 : point_cmp_xy_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_4_split_goal_1 : point_cmp_xy_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cmp_xy, fp32_gt in *; simpl in *.
  rewrite PreH1.
  reflexivity.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_4 : point_cmp_xy_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_5_split_goal_1 : point_cmp_xy_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cmp_xy, fp32_lt in *; simpl in *.
  rewrite PreH1.
  reflexivity.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_5 : point_cmp_xy_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_1_split_goal_1 : point_cross_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cross_finite, pointf_cross in PreH4; cbn in PreH4.
  destruct PreH4 as [_ [_ [_ [_ [_ [_ Hcross]]]]]].
  dump_pre_spatial.
  exact Hcross.
Qed.

Lemma proof_of_point_cross_safety_wit_1 : point_cross_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_1_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_2_split_goal_1 : point_cross_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cross_finite, pointf_cross in PreH4; cbn in PreH4.
  destruct PreH4 as [_ [_ [_ [_ [_ [Hmul2 _]]]]]].
  dump_pre_spatial.
  exact Hmul2.
Qed.

Lemma proof_of_point_cross_safety_wit_2 : point_cross_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_2_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_3_split_goal_1 : point_cross_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cross_finite, pointf_cross in PreH4; cbn in PreH4.
  destruct PreH4 as [_ [_ [_ [Hcxax _]]]].
  dump_pre_spatial.
  exact Hcxax.
Qed.

Lemma proof_of_point_cross_safety_wit_3 : point_cross_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_3_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_4_split_goal_1 : point_cross_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cross_finite, pointf_cross in PreH4; cbn in PreH4.
  destruct PreH4 as [_ [_ [Hbyay _]]].
  dump_pre_spatial.
  exact Hbyay.
Qed.

Lemma proof_of_point_cross_safety_wit_4 : point_cross_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_4_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_5_split_goal_1 : point_cross_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cross_finite, pointf_cross in PreH4; cbn in PreH4.
  destruct PreH4 as [_ [_ [_ [_ [Hmul1 _]]]]].
  dump_pre_spatial.
  exact Hmul1.
Qed.

Lemma proof_of_point_cross_safety_wit_5 : point_cross_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_5_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_6_split_goal_1 : point_cross_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cross_finite, pointf_cross in PreH4; cbn in PreH4.
  destruct PreH4 as [_ [Hcyay _]].
  dump_pre_spatial.
  exact Hcyay.
Qed.

Lemma proof_of_point_cross_safety_wit_6 : point_cross_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_6_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_7_split_goal_1 : point_cross_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cross_finite, pointf_cross in PreH4; cbn in PreH4.
  destruct PreH4 as [Hbxax _].
  dump_pre_spatial.
  exact Hbxax.
Qed.

Lemma proof_of_point_cross_safety_wit_7 : point_cross_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_7_split_goal_1.
Qed.

Lemma proof_of_point_cross_return_wit_1_split_goal_1 : point_cross_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_cross_finite in PreH4.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  unfold pointf_cross, fp32_eq, fp32_compare, fp32_isFinite in *.
  rewrite Binary.Bcompare_correct by assumption.
  rewrite Raux.Rcompare_Eq by reflexivity.
  reflexivity.
Qed.

Lemma proof_of_point_cross_return_wit_1 : point_cross_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_swap_points_return_wit_1_split_goal_1 : swap_points_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct (Z.eq_dec i_pre j_pre) as [Hij | Hij].
  - subst j_pre.
    unfold pointf_swap.
    repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
    repeat rewrite replace_Znth_Znth by lia.
    repeat rewrite (Znth_indep l i_pre __default_PointF default_pointf) by lia.
    destruct (Znth i_pre l default_pointf) eqn:Hzi.
    cbn.
    repeat rewrite <- Hzi.
    repeat rewrite replace_Znth_Znth by lia.
    reflexivity.
  - unfold pointf_swap.
    repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
    repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
    repeat rewrite replace_Znth_Znth by lia.
    repeat rewrite (Znth_indep l i_pre __default_PointF default_pointf) by lia.
    repeat rewrite (Znth_indep l j_pre __default_PointF default_pointf) by lia.
    destruct (Znth i_pre l default_pointf) eqn:Hzi.
    destruct (Znth j_pre l default_pointf) eqn:Hzj.
    cbn.
    repeat rewrite <- Hzi.
    repeat rewrite <- Hzj.
    apply (proj2 (list_eq_ext _ _ default_pointf)).
    split.
    + repeat rewrite Zlength_replace_Znth. reflexivity.
    + intros k Hk.
      repeat rewrite Zlength_replace_Znth in Hk.
      destruct (Z.eq_dec k j_pre) as [Hkj | Hkj].
      * subst k.
        repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
        reflexivity.
      * destruct (Z.eq_dec k i_pre) as [Hki | Hki].
        -- subst k.
           repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
           repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
           reflexivity.
        -- repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           reflexivity.
Qed.

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_swap_points_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_1 : partition_xy_points_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hpivot :
      Znth high_pre l default_pointf =
      pointf_mk (pointf_get_x (Znth high_pre l __default_PointF))
        (pointf_get_y (Znth high_pre l __default_PointF))).
  {
    unfold pointf_get_x, pointf_get_y.
    rewrite <- (Znth_indep l high_pre __default_PointF default_pointf) by lia.
    destruct (Znth high_pre l __default_PointF); reflexivity.
  }
  rewrite <- Hpivot.
  apply pointf_partition_scan_inv_init__swap_partition; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_2 : partition_xy_points_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_get_x, pointf_get_y.
  change (pointf_finite (Znth high_pre l __default_PointF)).
  rewrite (Znth_indep l high_pre __default_PointF default_pointf) by lia.
  apply pointsf_finite_Znth__swap_partition; auto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_3 : partition_xy_points_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_get_y.
  apply pointf_y_eq_self__partition.
  rewrite (Znth_indep l high_pre __default_PointF default_pointf) by lia.
  apply pointsf_finite_Znth__swap_partition; auto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_4 : partition_xy_points_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_get_x.
  apply pointf_x_eq_self__partition.
    rewrite (Znth_indep l high_pre __default_PointF default_pointf) by lia.
    apply pointsf_finite_Znth__swap_partition; auto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1 : partition_xy_points_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_partition_xy_points_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_partition_xy_points_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_partition_xy_points_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_1 : partition_xy_points_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcmp_le :
      pointf_cmp_xy (Znth j cur_2 default_pointf)
        (pointf_mk pivot_x pivot_y) <= 0).
  {
    rewrite <- (Znth_indep cur_2 j __default_PointF default_pointf) by lia.
    replace (Znth j cur_2 __default_PointF)
      with (pointf_mk (pointf_get_x (Znth j cur_2 __default_PointF))
            (pointf_get_y (Znth j cur_2 __default_PointF))).
    - rewrite <- PreH3. exact PreH2.
    - unfold pointf_get_x, pointf_get_y.
      destruct (Znth j cur_2 __default_PointF); reflexivity.
  }
  eapply pointf_partition_scan_inv_step_le__swap_partition; eauto; try lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_2 : partition_xy_points_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply all_pointf_cross_finite_permutation__swap_partition; eauto.
  apply pointf_swap_permutation__swap_partition; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_3 : partition_xy_points_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply pointsf_finite_permutation__swap_partition; eauto.
  apply pointf_swap_permutation__swap_partition; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_4 : partition_xy_points_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (Znth_indep (pointf_swap cur_2 (i + 1) j) high_pre
             __default_PointF default_pointf)
    by (rewrite pointf_swap_length__swap_partition; lia).
  rewrite pointf_swap_Znth_other__swap_partition by lia.
  rewrite (Znth_indep cur_2 high_pre default_pointf __default_PointF) by lia.
  exact PreH15.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_5 : partition_xy_points_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (Znth_indep (pointf_swap cur_2 (i + 1) j) high_pre
             __default_PointF default_pointf)
    by (rewrite pointf_swap_length__swap_partition; lia).
  rewrite pointf_swap_Znth_other__swap_partition by lia.
  rewrite (Znth_indep cur_2 high_pre default_pointf __default_PointF) by lia.
  exact PreH14.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_6 : partition_xy_points_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite pointf_swap_length__swap_partition. exact PreH13.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1 : partition_xy_points_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_6.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_2_split_goal_1 : partition_xy_points_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace cur_2 with (pointf_swap cur_2 (i + 1) j).
  2:{
    rewrite PreH1.
    apply pointf_swap_same__swap_partition. lia.
  }
  assert (Hcmp_le :
    pointf_cmp_xy (Znth j cur_2 default_pointf)
      (pointf_mk pivot_x pivot_y) <= 0).
  {
    rewrite <- (Znth_indep cur_2 j __default_PointF default_pointf) by lia.
    replace (Znth j cur_2 __default_PointF)
      with (pointf_mk (pointf_get_x (Znth j cur_2 __default_PointF))
            (pointf_get_y (Znth j cur_2 __default_PointF))).
    - rewrite <- PreH3. exact PreH2.
    - unfold pointf_get_x, pointf_get_y.
      destruct (Znth j cur_2 __default_PointF); reflexivity.
  }
  symmetry in PreH1; subst j.
  eapply pointf_partition_scan_inv_step_le__swap_partition; eauto; try lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_2 : partition_xy_points_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_3_split_goal_1 : partition_xy_points_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcmp :
    pointf_cmp_xy (Znth j cur_2 default_pointf)
      (pointf_mk pivot_x pivot_y) > 0).
  {
    rewrite <- (Znth_indep cur_2 j __default_PointF default_pointf) by lia.
    replace (pointf_mk (pointf_get_x (Znth j cur_2 __default_PointF))
              (pointf_get_y (Znth j cur_2 __default_PointF)))
      with (Znth j cur_2 __default_PointF) in PreH2.
    - rewrite <- PreH2. exact PreH1.
    - unfold pointf_get_x, pointf_get_y.
      destruct (Znth j cur_2 __default_PointF); reflexivity.
  }
  eapply pointf_partition_scan_inv_step_gt__swap_partition; eauto; try lia.
  apply pointf_cmp_xy_gt_flip__partition. exact Hcmp.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_3 : partition_xy_points_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_3_split_goal_1.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_1 : partition_xy_points_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply pointf_partition_scan_final_partitioned__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_2 : partition_xy_points_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply pointf_partition_scan_final_same_outside__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_3 : partition_xy_points_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply pointf_partition_scan_final_permutation__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_4 : partition_xy_points_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply all_pointf_cross_finite_permutation__swap_partition; eauto.
  apply pointf_swap_permutation__swap_partition; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_5 : partition_xy_points_return_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply pointsf_finite_permutation__swap_partition; eauto.
  apply pointf_swap_permutation__swap_partition; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_6 : partition_xy_points_return_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite pointf_swap_length__swap_partition. exact PreH11.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1 : partition_xy_points_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_return_wit_1_split_goal_1.
  - Goal_apply proof_of_partition_xy_points_return_wit_1_split_goal_2.
  - Goal_apply proof_of_partition_xy_points_return_wit_1_split_goal_3.
  - Goal_apply proof_of_partition_xy_points_return_wit_1_split_goal_4.
  - Goal_apply proof_of_partition_xy_points_return_wit_1_split_goal_5.
  - Goal_apply proof_of_partition_xy_points_return_wit_1_split_goal_6.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_1 : partition_xy_points_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace cur with (pointf_swap cur (i + 1) high_pre).
  2:{
    rewrite PreH1.
    apply pointf_swap_same__swap_partition. lia.
  }
  symmetry in PreH1; subst high_pre.
  eapply pointf_partition_scan_final_partitioned__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_2 : partition_xy_points_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace cur with (pointf_swap cur (i + 1) high_pre).
  2:{
    rewrite PreH1.
    apply pointf_swap_same__swap_partition. lia.
  }
  symmetry in PreH1; subst high_pre.
  eapply pointf_partition_scan_final_same_outside__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_3 : partition_xy_points_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace cur with (pointf_swap cur (i + 1) high_pre).
  2:{
    rewrite PreH1.
    apply pointf_swap_same__swap_partition. lia.
  }
  symmetry in PreH1; subst high_pre.
  eapply pointf_partition_scan_final_permutation__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2 : partition_xy_points_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_return_wit_2_split_goal_1.
  - Goal_apply proof_of_partition_xy_points_return_wit_2_split_goal_2.
  - Goal_apply proof_of_partition_xy_points_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_partition_xy_points_partial_solve_wit_5_pure_split_goal_1 : partition_xy_points_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (pointsf_finite_Znth__swap_partition cur j PreH23) as Hfin.
  unfold pointf_finite, pointf_get_x, pointf_get_y.
  split; [
    rewrite (Znth_indep cur j __default_PointF default_pointf) by lia;
    apply Hfin; lia
  | rewrite (Znth_indep cur j __default_PointF default_pointf) by lia;
    apply Hfin; lia ].
Qed.

Lemma proof_of_partition_xy_points_partial_solve_wit_5_pure : partition_xy_points_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - dump_pre_spatial.
    pose proof (pointsf_finite_Znth__swap_partition cur j PreH23) as Hfin.
    unfold pointf_finite, pointf_get_x, pointf_get_y.
    rewrite (Znth_indep cur j __default_PointF default_pointf) by lia.
    apply Hfin; lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_1 : quicksort_xy_points_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hpart3 : pointf_xy_partitioned_at out_3 left_pre right_pre retval).
  {
    pose proof PreH12 as [Hlen23 _].
    eapply pointf_xy_partitioned_at_preserved_by_left__quicksort_top.
    - exact PreH11.
    - exact PreH26.
    - exact PreH12.
    - rewrite PreH17. lia.
    - exact PreH22.
  }
  assert (Hpart4 : pointf_xy_partitioned_at out_4 left_pre right_pre retval).
  {
    pose proof PreH5 as [Hlen34 _].
    eapply pointf_xy_partitioned_at_preserved_by_right__quicksort_top.
    - exact PreH4.
    - exact PreH26.
    - exact PreH5.
    - rewrite PreH8. lia.
    - exact Hpart3.
  }
  assert (Hsorted_left4 : pointf_xy_sorted_range out_4 left_pre (retval - 1)).
  {
    pose proof PreH5 as [Hlen34 Heq34].
    eapply pointf_xy_sorted_range_ext__quicksort_top.
    - exact PreH26.
    - rewrite Hlen34, PreH1. lia.
    - exact Hlen34.
    - intros k Hk. apply Heq34.
      + rewrite Hlen34, PreH1. lia.
      + left. lia.
    - exact PreH13.
  }
  eapply pointf_xy_sorted_range_from_partition__quicksort_top with (p := retval).
  - exact PreH2.
  - exact PreH26.
  - rewrite PreH1. lia.
  - exact Hpart4.
  - exact Hsorted_left4.
  - exact PreH6.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_2 : quicksort_xy_points_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hsame23_full : pointf_same_outside_range out_2 out_3 left_pre right_pre).
  {
    eapply (pointf_same_outside_range_weaken__quicksort_top
      out_2 out_3 left_pre (retval - 1) left_pre right_pre).
    - lia.
    - lia.
    - exact PreH12.
  }
  assert (Hsame34_full : pointf_same_outside_range out_3 out_4 left_pre right_pre).
  {
    eapply (pointf_same_outside_range_weaken__quicksort_top
      out_3 out_4 (retval + 1) right_pre left_pre right_pre).
    - lia.
    - lia.
    - exact PreH5.
  }
  eapply pointf_same_outside_range_trans__quicksort_top.
  - exact PreH21.
  - eapply pointf_same_outside_range_trans__quicksort_top;
    [exact Hsame23_full | exact Hsame34_full].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_3 : quicksort_xy_points_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply Permutation_trans.
  - exact PreH20.
  - eapply Permutation_trans; [exact PreH11 | exact PreH4].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1 : quicksort_xy_points_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_1_split_goal_1.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_1_split_goal_2.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_1 : quicksort_xy_points_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hpart3 : pointf_xy_partitioned_at out_3 left_pre right_pre retval).
  {
    pose proof PreH5 as [Hlen23 _].
    eapply pointf_xy_partitioned_at_preserved_by_right__quicksort_top.
    - exact PreH4.
    - exact PreH20.
    - exact PreH5.
    - rewrite PreH11. lia.
    - exact PreH16.
  }
  eapply pointf_xy_sorted_range_from_partition__quicksort_top with (p := retval).
  - exact PreH2.
  - exact PreH20.
  - rewrite PreH1. lia.
  - exact Hpart3.
  - apply pointf_xy_sorted_range_base__quicksort_top; auto; lia.
  - exact PreH6.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_2 : quicksort_xy_points_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hsame23_full : pointf_same_outside_range out_2 out_3 left_pre right_pre).
  {
    eapply (pointf_same_outside_range_weaken__quicksort_top
      out_2 out_3 (retval + 1) right_pre left_pre right_pre).
    - lia.
    - lia.
    - exact PreH5.
  }
  eapply pointf_same_outside_range_trans__quicksort_top.
  - exact PreH15.
  - exact Hsame23_full.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_3 : quicksort_xy_points_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply Permutation_trans; [exact PreH14 | exact PreH4].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2 : quicksort_xy_points_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_2_split_goal_1.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_2_split_goal_2.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_1 : quicksort_xy_points_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hpart3 : pointf_xy_partitioned_at out_3 left_pre right_pre retval).
  {
    pose proof PreH6 as [Hlen23 _].
    eapply pointf_xy_partitioned_at_preserved_by_left__quicksort_top.
    - exact PreH5.
    - exact PreH20.
    - exact PreH6.
    - rewrite PreH11. lia.
    - exact PreH16.
  }
  eapply pointf_xy_sorted_range_from_partition__quicksort_top with (p := retval).
  - exact PreH3.
  - exact PreH20.
  - rewrite PreH2. lia.
  - exact Hpart3.
  - exact PreH7.
  - apply pointf_xy_sorted_range_base__quicksort_top; auto; lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_2 : quicksort_xy_points_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hsame23_full : pointf_same_outside_range out_2 out_3 left_pre right_pre).
  {
    eapply (pointf_same_outside_range_weaken__quicksort_top
      out_2 out_3 left_pre (retval - 1) left_pre right_pre).
    - lia.
    - lia.
    - exact PreH6.
  }
  eapply pointf_same_outside_range_trans__quicksort_top.
  - exact PreH15.
  - exact Hsame23_full.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_3 : quicksort_xy_points_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply Permutation_trans; [exact PreH14 | exact PreH5].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3 : quicksort_xy_points_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_3_split_goal_1.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_3_split_goal_2.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_3_split_goal_3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_1 : quicksort_xy_points_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply pointf_xy_sorted_range_base__quicksort_top; auto; lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_2 : quicksort_xy_points_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply pointf_same_outside_range_refl__swap_partition.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_3 : quicksort_xy_points_return_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4 : quicksort_xy_points_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_4_split_goal_1.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_4_split_goal_2.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_4_split_goal_3.
Qed.

Ltac build_lower_andrew_cross_finite Hcross :=
  match goal with
  | Hacf : all_pointf_cross_finite ?sorted,
    Hpop : pointf_lower_pop_inv ?sorted ?before (sublist 0 ?k ?hull) ?i ?k,
    Hsorted_len : Zlength ?sorted = ?n,
    Hhull_len : Zlength ?hull = _ |- context [Znth _ ?hull ?d] =>
      assert (Hcross : pointf_cross_finite
        (Znth (k - 2) hull d)
        (Znth (k - 1) hull d)
        (Znth i sorted d));
      [ apply Hacf;
        [ eapply pointf_lower_pop_inv_chain_member_sorted__andrew_lower;
          [ exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | eapply pointf_lower_pop_inv_chain_member_sorted__andrew_lower;
          [ exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | apply Znth_In_range__andrew; rewrite Hsorted_len; lia ]
      | idtac ]
  end.

Ltac build_upper_andrew_cross_finite Hcross :=
  match goal with
  | Hacf : all_pointf_cross_finite ?sorted,
    Hpop : pointf_upper_pop_inv ?sorted ?lower ?before
      (sublist 0 ?k ?hull) ?i ?k ?lower_n,
    Hsorted_len : Zlength ?sorted = ?n,
    Hhull_len : Zlength ?hull = _ |- _ =>
      match goal with
      | |- context [Znth _ _ ?d] =>
        assert (Hcross : pointf_cross_finite
          (Znth (k - 2) hull d)
          (Znth (k - 1) hull d)
          (Znth i sorted d));
        [ apply Hacf;
          [ eapply (pointf_upper_pop_inv_chain_member_sorted__andrew_upper
              sorted lower before (sublist 0 k hull) i k lower_n);
            [ rewrite Hsorted_len; lia
            | exact Hpop
            | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
          | eapply (pointf_upper_pop_inv_chain_member_sorted__andrew_upper
              sorted lower before (sublist 0 k hull) i k lower_n);
            [ rewrite Hsorted_len; lia
            | exact Hpop
            | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
          | apply Znth_In_range__andrew; rewrite Hsorted_len; lia ]
        | idtac ]
      end
  end.

Ltac finish_andrew_cross_projection Hcross :=
  unfold pointf_cross_finite, pointf_cross in Hcross; cbn in Hcross;
  destruct Hcross as
    [Hdx [Hdyc [Hdyb [Hdxc [Hmul1 [Hmul2 Hcross_val]]]]]];
  dump_pre_spatial;
  first
    [ exact Hcross_val
    | exact Hmul2
    | exact Hdxc
    | exact Hdyb
    | exact Hmul1
    | exact Hdyc
    | exact Hdx ].

Ltac prove_lower_andrew_cross_projection :=
  LLM_pre_process ltac:(int_auto);
  match goal with
  | Hacf : all_pointf_cross_finite ?sorted,
    Hpop : pointf_lower_pop_inv ?sorted ?before (sublist 0 ?k ?hull) ?i ?k,
    Hsorted_len : Zlength ?sorted = ?n,
    Hhull_len : Zlength ?hull = _ |- context [Znth _ ?hull ?d] =>
      let Hcross := fresh "Hcross" in
      assert (Hcross : pointf_cross_finite
        (Znth (k - 2) hull d)
        (Znth (k - 1) hull d)
        (Znth i sorted d));
      [ apply Hacf;
        [ eapply pointf_lower_pop_inv_chain_member_sorted__andrew_lower;
          [ exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | eapply pointf_lower_pop_inv_chain_member_sorted__andrew_lower;
          [ exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | apply Znth_In_range__andrew; rewrite Hsorted_len; lia ]
      | finish_andrew_cross_projection Hcross ]
  end.

Ltac prove_upper_andrew_cross_projection :=
  LLM_pre_process ltac:(int_auto);
  match goal with
  | Hacf : all_pointf_cross_finite ?sorted,
    Hpop : pointf_upper_pop_inv ?sorted ?lower ?before
      (sublist 0 ?k ?hull) ?i ?k ?lower_n,
    Hsorted_len : Zlength ?sorted = ?n,
    Hhull_len : Zlength ?hull = _ |- context [Znth _ ?hull ?d] =>
      let Hcross := fresh "Hcross" in
      assert (Hcross : pointf_cross_finite
        (Znth (k - 2) hull d)
        (Znth (k - 1) hull d)
        (Znth i sorted d));
      [ apply Hacf;
        [ eapply pointf_upper_pop_inv_chain_member_sorted__andrew_upper;
          [ rewrite Hsorted_len; lia
          | exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | eapply pointf_upper_pop_inv_chain_member_sorted__andrew_upper;
          [ rewrite Hsorted_len; lia
          | exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | apply Znth_In_range__andrew; rewrite Hsorted_len; lia ]
      | finish_andrew_cross_projection Hcross ]
  end.

Lemma proof_of_andrew_build_from_sorted_safety_wit_4_split_goal_1 : andrew_build_from_sorted_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcross : pointf_cross_finite
    (Znth (k - 2) hull_all __default_PointF)
    (Znth (k - 1) hull_all __default_PointF)
    (Znth i sorted __default_PointF)).
  {
    apply PreH10.
    - eapply pointf_lower_pop_inv_chain_member_sorted__andrew_lower.
      + exact PreH14.
      + apply Znth_In_sublist0__andrew; [lia | rewrite PreH12; lia].
    - eapply pointf_lower_pop_inv_chain_member_sorted__andrew_lower.
      + exact PreH14.
      + apply Znth_In_sublist0__andrew; [lia | rewrite PreH12; lia].
    - apply Znth_In_range__andrew. rewrite PreH8. lia.
  }
  unfold pointf_cross_finite, pointf_cross in Hcross; cbn in Hcross.
  destruct Hcross as [_ [_ [_ [_ [_ [_ Hcross]]]]]].
  dump_pre_spatial.
  exact Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_4_split_goal_2 : andrew_build_from_sorted_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  exact fp32_of_real_zero_finite__andrew.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_4 : andrew_build_from_sorted_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_5_split_goal_1 : andrew_build_from_sorted_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_5 : andrew_build_from_sorted_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_5_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_6_split_goal_1 : andrew_build_from_sorted_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_6 : andrew_build_from_sorted_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_6_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_7_split_goal_1 : andrew_build_from_sorted_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_7 : andrew_build_from_sorted_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_7_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_9_split_goal_1 : andrew_build_from_sorted_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_9 : andrew_build_from_sorted_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_9_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_12_split_goal_1 : andrew_build_from_sorted_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_12 : andrew_build_from_sorted_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_12_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_13_split_goal_1 : andrew_build_from_sorted_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_13 : andrew_build_from_sorted_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_13_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_15_split_goal_1 : andrew_build_from_sorted_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_15 : andrew_build_from_sorted_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_15_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_32_split_goal_1 : andrew_build_from_sorted_safety_wit_32_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcross : pointf_cross_finite
    (Znth (k - 2) hull_all __default_PointF)
    (Znth (k - 1) hull_all __default_PointF)
    (Znth i sorted __default_PointF)).
  {
    apply PreH13.
    - eapply (pointf_upper_pop_inv_chain_member_sorted__andrew_upper
        sorted lower before (sublist 0 k hull_all) i k lower_n).
      + rewrite PreH11. lia.
      + exact PreH17.
      + apply Znth_In_sublist0__andrew; [lia | rewrite PreH15; lia].
    - eapply (pointf_upper_pop_inv_chain_member_sorted__andrew_upper
        sorted lower before (sublist 0 k hull_all) i k lower_n).
      + rewrite PreH11. lia.
      + exact PreH17.
      + apply Znth_In_sublist0__andrew; [lia | rewrite PreH15; lia].
    - apply Znth_In_range__andrew. rewrite PreH11. lia.
  }
  unfold pointf_cross_finite, pointf_cross in Hcross; cbn in Hcross.
  destruct Hcross as [_ [_ [_ [_ [_ [_ Hcross]]]]]].
  dump_pre_spatial.
  exact Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_32_split_goal_2 : andrew_build_from_sorted_safety_wit_32_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  exact fp32_of_real_zero_finite__andrew.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_32 : andrew_build_from_sorted_safety_wit_32.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_32_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_32_split_goal_2.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_33_split_goal_1 : andrew_build_from_sorted_safety_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_33 : andrew_build_from_sorted_safety_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_33_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_34_split_goal_1 : andrew_build_from_sorted_safety_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_34 : andrew_build_from_sorted_safety_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_34_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_35_split_goal_1 : andrew_build_from_sorted_safety_wit_35_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_35 : andrew_build_from_sorted_safety_wit_35.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_35_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_37_split_goal_1 : andrew_build_from_sorted_safety_wit_37_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_37 : andrew_build_from_sorted_safety_wit_37.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_37_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_40_split_goal_1 : andrew_build_from_sorted_safety_wit_40_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_40 : andrew_build_from_sorted_safety_wit_40.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_40_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_41_split_goal_1 : andrew_build_from_sorted_safety_wit_41_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_41 : andrew_build_from_sorted_safety_wit_41.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_41_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_43_split_goal_1 : andrew_build_from_sorted_safety_wit_43_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_43 : andrew_build_from_sorted_safety_wit_43.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_43_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_1 : andrew_build_from_sorted_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_lower_scan_inv.
  repeat split; try lia.
  - simpl. constructor.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1 : andrew_build_from_sorted_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_2 : andrew_build_from_sorted_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (sublist 0 k hull_all_2) hull_all_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    unfold pointf_lower_pop_inv.
    unfold pointf_lower_scan_inv in PreH14.
    destruct PreH14 as [[Hread_low Hread_high] [Htop [Hscan Hdone]]].
    repeat split; try lia.
    + exact Hscan.
    + constructor.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_3 : andrew_build_from_sorted_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists before_2 hull_all_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
  unfold pointf_lower_pop_inv in *.
  destruct PreH15 as [Hscan [Htrace Htop]].
  unfold pointf_lower_scan_inv in Hscan.
  destruct Hscan as [[Hread_low Hread_high] [Hbefore_len [Hscan_from Hdone]]].
  assert (Hsub_remove:
    sublist 0 (k - 1) hull_all_2 =
    removelast (sublist 0 k hull_all_2)).
  {
    rewrite (sublist_split 0 k (k - 1) hull_all_2) by lia.
    replace (sublist (k - 1) k hull_all_2)
      with (sublist (k - 1) ((k - 1) + 1) hull_all_2)
      by (f_equal; lia).
    rewrite (sublist_single default_pointf (k - 1) hull_all_2) by lia.
    rewrite removelast_last.
    reflexivity.
  }
  repeat split; try lia.
  + repeat split; try lia.
    all: try exact Hscan_from.
    all: try constructor.
  + rewrite Hsub_remove.
    eapply pointf_pop_trace_pop; eauto; try lia.
    unfold pointf_ccw, pointf_cross.
    simpl.
    unfold pointf_get_x, pointf_get_y in PreH1.
    unfold fp32_le in PreH1.
    unfold fp32_gt.
    intros Hgt.
    rewrite fp32_compare_zero_of_real__andrew_lower in Hgt.
    rewrite ?Zlength_sublist in Hgt by lia.
    rewrite !Znth_sublist0 in Hgt by lia.
    rewrite ?Zlength_sublist in Hgt by lia.
    repeat rewrite <- (Znth_indep hull_all_2 _ __default_PointF default_pointf) in Hgt by lia.
    rewrite <- (Znth_indep sorted i __default_PointF default_pointf) in Hgt by lia.
    replace (k - 0 - 1) with (k - 1) in Hgt by lia.
    replace (k - 0 - 2) with (k - 2) in Hgt by lia.
    rewrite Hgt in PreH1.
    simpl in PreH1.
    contradiction.
  + rewrite Zlength_sublist by lia. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_1 : andrew_build_from_sorted_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply lower_scan_after_store_short__andrew_lower; eauto.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_2 : andrew_build_from_sorted_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply pointsf_finite_lower_store__andrew_lower; eauto; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_3 : andrew_build_from_sorted_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat rewrite Zlength_replace_Znth. exact PreH12.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1 : andrew_build_from_sorted_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_3.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_1 : andrew_build_from_sorted_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply lower_scan_after_store_ccw__andrew_lower; eauto.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_2 : andrew_build_from_sorted_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply pointsf_finite_lower_store__andrew_lower; eauto; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_3 : andrew_build_from_sorted_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat rewrite Zlength_replace_Znth. exact PreH13.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2 : andrew_build_from_sorted_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_3.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_1 : andrew_build_from_sorted_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_lower_scan_inv in PreH14.
  destruct PreH14 as [[Hread_low Hread_high] [Htop [Hscan Hdone]]].
  assert (Hi_eq : i = n_pre) by lia. subst i.
  assert (Hk_len : k = Zlength (sublist 0 k hull_all_2)) by lia.
  assert (Hlower_len :
    k = Zlength (sublist 0 k (sublist 0 k hull_all_2))).
  {
    rewrite Zlength_sublist.
    - lia.
    - rewrite Zlength_sublist by lia. lia.
  }
  unfold pointf_upper_scan_inv, pointf_upper_capacity.
  repeat split; try lia; try exact Hk_len; try exact Hlower_len;
    try solve [rewrite Zlength_sublist by lia; lia];
    try solve [let H := fresh in intro H; rewrite Zlength_sublist by lia; lia];
    try solve [intro Hbad; lia].
  - replace (sublist 0 k (sublist 0 k hull_all_2))
      with (sublist 0 k hull_all_2) by
      (symmetry; apply sublist_self; rewrite Zlength_sublist by lia; lia).
    replace (sublist 0 n_pre sorted) with sorted in Hscan.
    + exact Hscan.
    + rewrite sublist_self by lia. reflexivity.
  - replace (rev (sublist (n_pre - 2 + 1) (Zlength sorted - 1) sorted))
      with (@nil PointF).
    + replace (sublist 0 k (sublist 0 k hull_all_2))
        with (sublist 0 k hull_all_2) by
        (symmetry; apply sublist_self; rewrite Zlength_sublist by lia; lia).
      constructor.
    + symmetry.
      rewrite PreH8.
      replace (n_pre - 2 + 1) with (n_pre - 1) by lia.
      rewrite (@Zsublist_nil PointF sorted (n_pre - 1) (n_pre - 1)) by lia.
      reflexivity.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_2 : andrew_build_from_sorted_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_sublist.
  - lia.
  - rewrite Zlength_sublist by lia. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_3 : andrew_build_from_sorted_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_lower_scan_inv in PreH14.
  destruct PreH14 as [_ [_ [_ Hdone]]].
  apply Hdone. rewrite PreH8. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5 : andrew_build_from_sorted_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_6 : andrew_build_from_sorted_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hk_lt_2n : k < 2 * n_pre).
  {
    pose proof PreH17 as Hupper_inv.
    unfold pointf_upper_scan_inv in Hupper_inv.
    destruct Hupper_inv as
      [_ [Htop_inv [_ [_ [_ [_ [_ Hcap]]]]]]].
    unfold pointf_upper_capacity in Hcap.
    destruct Hcap as [_ [_ [Hstrict _]]].
    rewrite <- PreH11.
    rewrite Htop_inv.
    apply Hstrict. lia.
  }
  Exists (sublist 0 k hull_all_2) hull_all_2 lower_2.
  assert (Hlower_len :
    Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)) = lower_n).
  {
    rewrite Zlength_sublist by
      (rewrite Zlength_sublist by lia; lia).
    lia.
  }
  assert (Hlower_norm :
    sublist 0 (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      (sublist 0 k hull_all_2) = lower_2).
  {
    rewrite Hlower_len.
    symmetry. exact PreH10.
  }
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
      try solve [rewrite Zlength_sublist by lia; lia];
      try solve [rewrite Zlength_sublist by
        (rewrite Zlength_sublist by lia; lia); lia].
    try solve
      [ rewrite Hlower_len;
        rewrite Zlength_sublist by
          (rewrite Zlength_sublist by lia; lia);
        lia ].
    replace (sublist 0
      (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      (sublist 0 k hull_all_2)) with lower_2 by
      (symmetry; exact Hlower_norm).
    replace (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      with lower_n by (symmetry; exact Hlower_len).
    unfold pointf_upper_pop_inv.
    replace (Zlength (sublist 0 k hull_all_2)) with k by
      (rewrite Zlength_sublist by lia; lia).
    split; [exact PreH17 |].
    split; [constructor |].
    split; [reflexivity |].
    split; [exact PreH10 | lia].
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_7 : andrew_build_from_sorted_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists before_2 hull_all_2 lower_2.
  assert (Hsub_remove:
    sublist 0 (k - 1) hull_all_2 =
    removelast (sublist 0 k hull_all_2)).
  {
    rewrite (sublist_split 0 k (k - 1) hull_all_2) by lia.
    replace (sublist (k - 1) k hull_all_2)
      with (sublist (k - 1) ((k - 1) + 1) hull_all_2) by
      (f_equal; lia).
    rewrite sublist_single with (d := default_pointf) by lia.
    rewrite removelast_last by (rewrite Zlength_sublist by lia; lia).
    reflexivity.
  }
  assert (Hlower_prefix:
    sublist 0 lower_n (sublist 0 (k - 1) hull_all_2) = lower_2).
  {
    rewrite PreH11.
    rewrite Zsublist_Zsublist00 by lia.
    rewrite Zsublist_Zsublist00 by lia.
    reflexivity.
  }
  assert (Hnccw :
    ~ pointf_ccw
        (Znth (Zlength (sublist 0 k hull_all_2) - 2)
          (sublist 0 k hull_all_2) default_pointf)
        (Znth (Zlength (sublist 0 k hull_all_2) - 1)
          (sublist 0 k hull_all_2) default_pointf)
        (Znth i sorted default_pointf)).
  {
    rewrite Zlength_sublist by lia.
    rewrite !Znth_sublist by lia.
    replace (k - 2 + 0) with (k - 2) by lia.
    replace (k - 1 + 0) with (k - 1) by lia.
    unfold pointf_ccw, pointf_cross.
    repeat rewrite (Znth_indep hull_all_2 _ default_pointf __default_PointF) by lia.
    rewrite (Znth_indep sorted i default_pointf __default_PointF) by lia.
    replace (k - 0 - 2 + 0) with (k - 2) by lia.
    replace (k - 0 - 1 + 0) with (k - 1) by lia.
    unfold pointf_get_x, pointf_get_y in PreH1.
    unfold fp32_le in PreH1.
    unfold fp32_gt.
    rewrite fp32_compare_zero_of_real__andrew_upper.
    match type of PreH1 with
    | context [fp32_compare ?e ?z] =>
      intro Hgt; rewrite Hgt in PreH1; exact PreH1
    end.
  }
  assert (Hlower_len :
    Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)) = lower_n).
  {
    rewrite Zlength_sublist by
      (rewrite Zlength_sublist by lia; lia).
    lia.
  }
  assert (Hlower_norm :
    sublist 0 (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      (sublist 0 (k - 1) hull_all_2) = lower_2).
  {
    rewrite Hlower_len.
    exact Hlower_prefix.
  }
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
      try solve [rewrite Zlength_sublist by lia; lia];
      try solve [rewrite Zlength_sublist by
        (rewrite Zlength_sublist by lia; lia); lia].
    try solve
      [ rewrite Hlower_len;
        rewrite Zlength_sublist by
          (rewrite Zlength_sublist by lia; lia);
        lia ].
    replace (sublist 0
      (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      (sublist 0 (k - 1) hull_all_2)) with lower_2 by
      (symmetry; exact Hlower_norm).
    replace (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      with lower_n by (symmetry; exact Hlower_len).
    unfold pointf_upper_pop_inv in *.
    destruct PreH18 as [Hscan [Htrace [Htop [Hlower Hle]]]].
    replace (Zlength (sublist 0 (k - 1) hull_all_2)) with (k - 1) by
      (rewrite Zlength_sublist by lia; lia).
    split.
    + exact Hscan.
    + split.
      * rewrite Hsub_remove.
        eapply pointf_upper_pop_trace_pop; eauto; try lia.
      * split.
        -- lia.
        -- split; [symmetry; exact Hlower_prefix | lia].
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_1 : andrew_build_from_sorted_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (new_all :=
    replace_Znth k
      (pointf_mk
        (pointf_get_x
          (Znth k
            (replace_Znth k
              (pointf_mk (pointf_get_x (Znth i sorted __default_PointF))
                (pointf_get_y (Znth k hull_all_2 __default_PointF))) hull_all_2)
            __default_PointF))
        (pointf_get_y (Znth i sorted __default_PointF)))
      (replace_Znth k
        (pointf_mk (pointf_get_x (Znth i sorted __default_PointF))
          (pointf_get_y (Znth k hull_all_2 __default_PointF))) hull_all_2)).
  assert (Hprefix :
    sublist 0 (k + 1) new_all =
    sublist 0 k hull_all_2 ++ Znth i sorted default_pointf :: nil).
  {
    subst new_all.
    apply upper_store_prefix__andrew_upper; lia.
  }
  assert (Hlower_new :
    sublist 0 lower_n (sublist 0 (k + 1) new_all) = lower_2).
  {
    rewrite Hprefix.
    rewrite (sublist_app_prefix__andrew_upper
      (sublist 0 k hull_all_2) (Znth i sorted default_pointf) lower_n).
    2:{ rewrite Zlength_sublist by lia; lia. }
    rewrite PreH10.
    reflexivity.
  }
  assert (Hinv :
    pointf_upper_scan_inv sorted lower_2
      (sublist 0 k hull_all_2 ++ Znth i sorted default_pointf :: nil)
      i (k + 1) lower_n).
  {
    eapply pointf_upper_scan_inv_after_append__andrew_upper
      with (before := before) (top := k).
    - rewrite PreH11. lia.
    - exact PreH17.
    - apply pointf_upper_pop_until_boundary.
      rewrite Zlength_sublist by lia. lia.
  }
  split_pures; auto; try lia;
    try solve [subst new_all; rewrite Zlength_replace_Znth; lia];
    try solve [rewrite Zlength_sublist by lia; lia].
  rewrite Hlower_new.
  rewrite Hprefix.
  replace ((i - 1) + 1) with i by lia.
  exact Hinv.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_2 : andrew_build_from_sorted_entail_wit_8_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply pointsf_finite_upper_store__andrew_upper.
  - exact PreH16.
  - exact PreH12.
  - lia.
  - rewrite PreH11. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_3 : andrew_build_from_sorted_entail_wit_8_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_4 : andrew_build_from_sorted_entail_wit_8_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_sublist.
  - lia.
  - rewrite Zlength_sublist.
    + lia.
    + repeat rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1 : andrew_build_from_sorted_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_2.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_3.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_4.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_1 : andrew_build_from_sorted_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (new_all :=
    replace_Znth k
      (pointf_mk
        (pointf_get_x
          (Znth k
            (replace_Znth k
              (pointf_mk (pointf_get_x (Znth i sorted __default_PointF))
                (pointf_get_y (Znth k hull_all_2 __default_PointF))) hull_all_2)
            __default_PointF))
        (pointf_get_y (Znth i sorted __default_PointF)))
      (replace_Znth k
        (pointf_mk (pointf_get_x (Znth i sorted __default_PointF))
          (pointf_get_y (Znth k hull_all_2 __default_PointF))) hull_all_2)).
  assert (Hprefix :
    sublist 0 (k + 1) new_all =
    sublist 0 k hull_all_2 ++ Znth i sorted default_pointf :: nil).
  {
    subst new_all.
    apply upper_store_prefix__andrew_upper; lia.
  }
  assert (Hlower_new :
    sublist 0 lower_n (sublist 0 (k + 1) new_all) = lower_2).
  {
    rewrite Hprefix.
    rewrite (sublist_app_prefix__andrew_upper
      (sublist 0 k hull_all_2) (Znth i sorted default_pointf) lower_n).
    2:{ rewrite Zlength_sublist by lia; lia. }
    rewrite PreH11.
    reflexivity.
  }
  assert (Hccw :
    pointf_ccw
      (Znth (Zlength (sublist 0 k hull_all_2) - 2)
        (sublist 0 k hull_all_2) default_pointf)
      (Znth (Zlength (sublist 0 k hull_all_2) - 1)
        (sublist 0 k hull_all_2) default_pointf)
      (Znth i sorted default_pointf)).
  {
    unfold pointf_ccw, pointf_cross.
    rewrite ?Zlength_sublist by lia.
    rewrite !Znth_sublist0 by lia.
    repeat rewrite <- (Znth_indep hull_all_2 _ __default_PointF default_pointf)
      by lia.
    rewrite <- (Znth_indep sorted i __default_PointF default_pointf) by lia.
    unfold fp32_gt in *.
    rewrite fp32_compare_zero_of_real__andrew_upper.
    replace (k - 0 - 2) with (k - 2) by lia.
    replace (k - 0 - 1) with (k - 1) by lia.
    exact PreH1.
  }
  assert (Hinv :
    pointf_upper_scan_inv sorted lower_2
      (sublist 0 k hull_all_2 ++ Znth i sorted default_pointf :: nil)
      i (k + 1) lower_n).
  {
    eapply pointf_upper_scan_inv_after_append__andrew_upper
      with (before := before) (top := k).
    - rewrite PreH12. lia.
    - exact PreH18.
    - apply pointf_upper_pop_until_ccw.
      + rewrite Zlength_sublist by lia. lia.
      + rewrite Zlength_sublist by lia. lia.
      + exact Hccw.
  }
  split_pures; auto; try lia;
    try solve [subst new_all; rewrite Zlength_replace_Znth; lia];
    try solve [rewrite Zlength_sublist by lia; lia].
  rewrite Hlower_new.
  rewrite Hprefix.
  replace ((i - 1) + 1) with i by lia.
  exact Hinv.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_2 : andrew_build_from_sorted_entail_wit_8_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply pointsf_finite_upper_store__andrew_upper.
  - exact PreH17.
  - exact PreH13.
  - lia.
  - rewrite PreH12. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_3 : andrew_build_from_sorted_entail_wit_8_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_4 : andrew_build_from_sorted_entail_wit_8_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_sublist.
  - lia.
  - rewrite Zlength_sublist.
    + lia.
    + repeat rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2 : andrew_build_from_sorted_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_2.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_3.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_4.
Qed.

Lemma proof_of_andrew_build_from_sorted_return_wit_1_split_goal_1 : andrew_build_from_sorted_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hread0 : i + 1 = 0) by lia.
  replace (sublist 0 (k - 1) hull_all_2)
    with (pointf_drop_last (sublist 0 k hull_all_2)).
  2:{
    apply pointf_drop_last_sublist_prefix__andrew_upper.
    rewrite PreH15. lia.
  }
  eapply upper_scan_final_is_andrew_hull__andrew_upper.
  - rewrite PreH11. lia.
  - exact PreH14.
  - replace (sublist (i + 1) k hull_all_2)
      with (sublist 0 k hull_all_2) by
      (replace (i + 1) with 0 by lia; reflexivity).
    pose proof PreH17 as Hfinal_inv.
    replace (i + 1) with 0 in Hfinal_inv by lia.
    exact Hfinal_inv.
Qed.

Lemma proof_of_andrew_build_from_sorted_return_wit_1_split_goal_2 : andrew_build_from_sorted_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_andrew_build_from_sorted_return_wit_1_split_goal_3 : andrew_build_from_sorted_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH17 as Hupper_inv.
  unfold pointf_upper_scan_inv in Hupper_inv.
  destruct Hupper_inv as
    [_ [Htop [_ [_ [_ [_ [_ Hcap]]]]]]].
  destruct Hcap as [_ [_ [Hcap_strict Hcap_done]]].
  specialize (Hcap_done ltac:(lia)).
  rewrite Htop in Hcap_done.
  rewrite Zlength_sublist in Hcap_done by lia.
  lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_return_wit_1_split_goal_4 : andrew_build_from_sorted_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_return_wit_1 : andrew_build_from_sorted_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_return_wit_1_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_return_wit_1_split_goal_2.
  - Goal_apply proof_of_andrew_build_from_sorted_return_wit_1_split_goal_3.
  - Goal_apply proof_of_andrew_build_from_sorted_return_wit_1_split_goal_4.
Qed.

Lemma proof_of_convex_hull_float_entail_wit_1_split_goal_1 : convex_hull_float_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold pointf_xy_sorted.
  rewrite PreH1.
  exact PreH6.
Qed.

Lemma proof_of_convex_hull_float_entail_wit_1 : convex_hull_float_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_convex_hull_float_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_convex_hull_float_return_wit_1_split_goal_1 : convex_hull_float_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply is_andrew_hull_float_permutation_input__quicksort_top.
  - exact PreH18.
  - exact PreH10.
  - exact PreH12.
Qed.

Lemma proof_of_convex_hull_float_return_wit_1_split_goal_2 : convex_hull_float_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply Permutation_trans.
  - exact PreH18.
  - exact PreH10.
Qed.

Lemma proof_of_convex_hull_float_return_wit_1 : convex_hull_float_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_convex_hull_float_return_wit_1_split_goal_1.
  - Goal_apply proof_of_convex_hull_float_return_wit_1_split_goal_2.
Qed.
