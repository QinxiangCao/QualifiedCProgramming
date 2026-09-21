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
From SimpleC.EE.LLM_bench.Algorithms.rmq Require Import rmq_goal.
From SimpleC.EE.LLM_bench.Algorithms.rmq Require Import rmq_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_lib.
Local Open Scope sac.

Lemma proof_of_build_safety_wit_12_split_goal_1 : build_safety_wit_12_split_goal_1.
Proof.
  aggressive_pre_process.
  pose proof (worker_Power2_bound_lt_30 j K_pre ltac:(lia) ltac:(lia)).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_build_safety_wit_12_split_goal_2 : build_safety_wit_12_split_goal_2.
Proof.
  aggressive_pre_process.
  pose proof (worker_Power2_nonneg j).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_build_safety_wit_12 : build_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_28_split_goal_1 : build_safety_wit_28_split_goal_1.
Proof.
  aggressive_pre_process.
  pose proof (worker_Power2_double_int_bound_30 j K_pre ltac:(lia) ltac:(lia)).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_build_safety_wit_28_split_goal_2 : build_safety_wit_28_split_goal_2.
Proof.
  aggressive_pre_process.
  pose proof (worker_Power2_nonneg j).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_build_safety_wit_28 : build_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_28_split_goal_2.
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_1 : build_entail_wit_3_split_goal_1.
Proof.
  aggressive_pre_process. unfold STBasePrefix; intros; lia.
Qed.

Lemma proof_of_build_entail_wit_3 : build_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_1 : build_entail_wit_4_split_goal_1.
Proof.
  aggressive_pre_process; nia.
Qed.

Lemma proof_of_build_entail_wit_4 : build_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_build_entail_wit_5 : build_entail_wit_5.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength arr_pre n_pre l). Intros_p Hl.
  prop_apply (IntArray.full_Zlength st_pre (n_pre * K_pre)
    (replace_Znth (i * K_pre) (Znth i l 0) st_l_2)). Intros_p Hst.
  rewrite Zlength_replace_Znth in Hst.
  pose proof (worker_STBasePrefix_write_base_step l st_l_2 K_pre n_pre i
    Hl Hst ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH10) as Hnext.
  Exists (replace_Znth (i * K_pre) (Znth i l 0) st_l_2).
  entailer!.
Qed.

Lemma proof_of_build_entail_wit_6_split_goal_1 : build_entail_wit_6_split_goal_1.
Proof.
  aggressive_pre_process. eapply worker_STBasePrefix_complete_level1; eauto.
Qed.

Lemma proof_of_build_entail_wit_6_split_goal_2 : build_entail_wit_6_split_goal_2.
Proof.
  aggressive_pre_process; reflexivity.
Qed.

Lemma proof_of_build_entail_wit_6_split_goal_3 : build_entail_wit_6_split_goal_3.
Proof.
  aggressive_pre_process; reflexivity.
Qed.

Lemma proof_of_build_entail_wit_6 : build_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_6_split_goal_3.
Qed.

Lemma proof_of_build_entail_wit_7_split_goal_1 : build_entail_wit_7_split_goal_1.
Proof.
  aggressive_pre_process. unfold STLevelPrefix; intros; lia.
Qed.

Lemma proof_of_build_entail_wit_7 : build_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_build_entail_wit_8_split_goal_1 : build_entail_wit_8_split_goal_1.
Proof.
  aggressive_pre_process.
  pose proof (Power2_pos (j - 1) ltac:(lia)).
  pose proof (Power2_sub1_double j ltac:(lia)).
  nia.
Qed.

Lemma proof_of_build_entail_wit_8_split_goal_2 : build_entail_wit_8_split_goal_2.
Proof.
  aggressive_pre_process.
  pose proof (Power2_pos (j - 1) ltac:(lia)).
  pose proof (Power2_sub1_double j ltac:(lia)).
  nia.
Qed.

Lemma proof_of_build_entail_wit_8_split_goal_3 : build_entail_wit_8_split_goal_3.
Proof.
  aggressive_pre_process.
  pose proof (Power2_pos (j - 1) ltac:(lia)).
  pose proof (Power2_sub1_double j ltac:(lia)).
  nia.
Qed.

Lemma proof_of_build_entail_wit_8_split_goal_4 : build_entail_wit_8_split_goal_4.
Proof.
  aggressive_pre_process.
  pose proof (Power2_pos (j - 1) ltac:(lia)).
  pose proof (Power2_sub1_double j ltac:(lia)).
  nia.
Qed.

Lemma proof_of_build_entail_wit_8 : build_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_build_entail_wit_8_split_goal_4.
Qed.

Lemma proof_of_build_entail_wit_9_1 : build_entail_wit_9_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength st_pre (n_pre * K_pre)
    (replace_Znth (i * K_pre + j) (Znth (i * K_pre + j - 1) st_l_2 0) st_l_2)). Intros_p Hst.
  rewrite Zlength_replace_Znth in Hst.
  pose proof (Power2_pos (j - 1) ltac:(lia)) as Hhalf.
  pose proof (Power2_sub1_double j ltac:(lia)) as Hdouble.
  assert (Hleft : STCellRangeMax l st_l_2 K_pre i (j - 1)).
  { apply PreH19; repeat split; lia. }
  assert (Hright : STCellRangeMax l st_l_2 K_pre (i + half) (j - 1)).
  { apply PreH19; repeat split; lia. }
  assert (Hbuilt : STBuiltBeforeLevel l
    (replace_Znth (i * K_pre + j) (Znth (i * K_pre + j - 1) st_l_2 0) st_l_2) K_pre n_pre j).
  { eapply STBuiltBeforeLevel_replace_level_cell; eauto.
    - rewrite Hst; lia.
    - intros row col (Hrow & Hcol & Hcolj & Hrange).
      pose proof (Power2_pos col Hcol). rewrite Hst; split; nia. }
  assert (Hprefix : STLevelPrefix l
    (replace_Znth (i * K_pre + j) (Znth (i * K_pre + j - 1) st_l_2 0) st_l_2) K_pre n_pre j (i + 1)).
  { eapply STLevelPrefix_extend_by_left_max with
      (half := half) (a := Znth (i * K_pre + j - 1) st_l_2 0)
      (b := Znth ((i + half) * K_pre + j - 1) st_l_2 0); eauto.
    - rewrite Hst; lia.
    - f_equal; lia.
    - f_equal; lia. }
  Exists (replace_Znth (i * K_pre + j) (Znth (i * K_pre + j - 1) st_l_2 0) st_l_2).
  entailer!; lia.
Qed.

Lemma proof_of_build_entail_wit_9_2 : build_entail_wit_9_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength st_pre (n_pre * K_pre)
    (replace_Znth (i * K_pre + j) (Znth ((i + half) * K_pre + j - 1) st_l_2 0) st_l_2)). Intros_p Hst.
  rewrite Zlength_replace_Znth in Hst.
  pose proof (Power2_pos (j - 1) ltac:(lia)) as Hhalf.
  pose proof (Power2_sub1_double j ltac:(lia)) as Hdouble.
  assert (Hleft : STCellRangeMax l st_l_2 K_pre i (j - 1)).
  { apply PreH19; repeat split; lia. }
  assert (Hright : STCellRangeMax l st_l_2 K_pre (i + half) (j - 1)).
  { apply PreH19; repeat split; lia. }
  assert (Hbuilt : STBuiltBeforeLevel l
    (replace_Znth (i * K_pre + j) (Znth ((i + half) * K_pre + j - 1) st_l_2 0) st_l_2) K_pre n_pre j).
  { eapply STBuiltBeforeLevel_replace_level_cell; eauto.
    - rewrite Hst; lia.
    - intros row col (Hrow & Hcol & Hcolj & Hrange).
      pose proof (Power2_pos col Hcol). rewrite Hst; split; nia. }
  assert (Hprefix : STLevelPrefix l
    (replace_Znth (i * K_pre + j) (Znth ((i + half) * K_pre + j - 1) st_l_2 0) st_l_2) K_pre n_pre j (i + 1)).
  { eapply STLevelPrefix_extend_by_right_max with
      (half := half) (a := Znth (i * K_pre + j - 1) st_l_2 0)
      (b := Znth ((i + half) * K_pre + j - 1) st_l_2 0); eauto.
    - rewrite Hst; lia.
    - f_equal; lia.
    - f_equal; lia. }
  Exists (replace_Znth (i * K_pre + j) (Znth ((i + half) * K_pre + j - 1) st_l_2 0) st_l_2).
  entailer!; lia.
Qed.

Lemma proof_of_build_entail_wit_10_split_goal_1 : build_entail_wit_10_split_goal_1.
Proof.
  aggressive_pre_process. eapply STLevelPrefix_exit_to_built_step; eauto.
Qed.

Lemma proof_of_build_entail_wit_10_split_goal_2 : build_entail_wit_10_split_goal_2.
Proof.
  aggressive_pre_process. rewrite PreH10. apply Power2_step; lia.
Qed.

Lemma proof_of_build_entail_wit_10_split_goal_3 : build_entail_wit_10_split_goal_3.
Proof.
  aggressive_pre_process. replace (j + 1 - 1) with j by lia; assumption.
Qed.

Lemma proof_of_build_entail_wit_10 : build_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_10_split_goal_3.
Qed.

Lemma proof_of_build_return_wit_1_split_goal_1 : build_return_wit_1_split_goal_1.
Proof.
  aggressive_pre_process. unfold STBuilt. assert (j = K_pre) by lia. subst j; assumption.
Qed.

Lemma proof_of_build_return_wit_1 : build_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_query_entail_wit_1_split_goal_1 : query_entail_wit_1_split_goal_1.
Proof.
  aggressive_pre_process; reflexivity.
Qed.

Lemma proof_of_query_entail_wit_1 : query_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_query_entail_wit_2_split_goal_1 : query_entail_wit_2_split_goal_1.
Proof.
  aggressive_pre_process. rewrite PreH13. apply Power2_step; lia.
Qed.

Lemma proof_of_query_entail_wit_2_split_goal_2 : query_entail_wit_2_split_goal_2.
Proof.
  aggressive_pre_process.
  pose proof (Power2_step k ltac:(lia)).
  assert (k + 1 < K_pre \/ k + 1 = K_pre) as [Hlt | Heq] by lia.
  - exact Hlt.
  - rewrite Heq in H. lia.
Qed.

Lemma proof_of_query_entail_wit_2 : query_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_query_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_1 : query_entail_wit_3_split_goal_1.
Proof.
  aggressive_pre_process; nia.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_2 : query_entail_wit_3_split_goal_2.
Proof.
  aggressive_pre_process; nia.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_3 : query_entail_wit_3_split_goal_3.
Proof.
  aggressive_pre_process; nia.
Qed.

Lemma proof_of_query_entail_wit_3 : query_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_query_return_wit_1_split_goal_1 : query_return_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply (RangeMaxValue_sparse_query_right l st_l K_pre n_pre) with
    (len := len) (j := k) (pow := pow)
    (a := Znth (left_pre * K_pre + k) st_l 0); eauto.
  - pose proof (Power2_step_query k ltac:(lia)); repeat split; lia.
  - apply PreH21; repeat split; lia.
  - apply PreH21; repeat split; lia.
Qed.

Lemma proof_of_query_return_wit_1 : query_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_query_return_wit_2_split_goal_1 : query_return_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply (RangeMaxValue_sparse_query_left l st_l K_pre n_pre) with
    (len := len) (j := k) (pow := pow)
    (b := Znth ((right_pre - pow + 1) * K_pre + k) st_l 0); eauto.
  - pose proof (Power2_step_query k ltac:(lia)); repeat split; lia.
  - apply PreH21; repeat split; lia.
  - apply PreH21; repeat split; lia.
Qed.

Lemma proof_of_query_return_wit_2 : query_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_return_wit_2_split_goal_1.
Qed.
