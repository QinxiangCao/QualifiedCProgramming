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

Lemma proof_of_build_safety_wit_2_split_goal_1 : build_safety_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_2_split_goal_2 : build_safety_wit_2_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_build_safety_wit_2 : build_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_4_split_goal_1 : build_safety_wit_4_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_4_split_goal_2 : build_safety_wit_4_split_goal_2.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_4 : build_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_6_split_goal_1 : build_safety_wit_6_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_6_split_goal_2 : build_safety_wit_6_split_goal_2.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_6 : build_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_12_split_goal_1 : build_safety_wit_12_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, STLevelPrefixBounds in *.
  assert (Hpow : Power2 j <= 536870912).
  { apply worker_Power2_bound_lt_30 with (K := K_pre); lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_12_split_goal_2 : build_safety_wit_12_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STLevelPrefixBounds in *.
  pose proof (worker_Power2_nonneg j).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_12 : build_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_13_split_goal_1 : build_safety_wit_13_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_13_split_goal_2 : build_safety_wit_13_split_goal_2.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_13 : build_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_13_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_14_split_goal_1 : build_safety_wit_14_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_14_split_goal_2 : build_safety_wit_14_split_goal_2.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_14 : build_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_14_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_15_split_goal_1 : build_safety_wit_15_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_15_split_goal_2 : build_safety_wit_15_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_15 : build_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_17_split_goal_1 : build_safety_wit_17_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_17_split_goal_2 : build_safety_wit_17_split_goal_2.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_17 : build_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_18_split_goal_1 : build_safety_wit_18_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_18_split_goal_2 : build_safety_wit_18_split_goal_2.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_18 : build_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_18_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_19_split_goal_1 : build_safety_wit_19_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_19_split_goal_2 : build_safety_wit_19_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  pose proof (worker_Power2_nonneg (j - 1)).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_build_safety_wit_19 : build_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_20_split_goal_1 : build_safety_wit_20_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  pose proof (Power2_sub1_double j ltac:(lia)).
  pose proof (worker_Power2_nonneg (j - 1)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_20_split_goal_2 : build_safety_wit_20_split_goal_2.
Proof.
  aggressive_pre_process.
  pose proof (worker_Power2_nonneg (j - 1)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_20 : build_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_20_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_22_split_goal_1 : build_safety_wit_22_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, STTableShape, STCellBounds in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_build_safety_wit_22_split_goal_2 : build_safety_wit_22_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STCellBounds in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_build_safety_wit_22 : build_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_23_split_goal_1 : build_safety_wit_23_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, STTableShape, STCellBounds in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_build_safety_wit_23_split_goal_2 : build_safety_wit_23_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STCellBounds in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_build_safety_wit_23 : build_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_24_split_goal_1 : build_safety_wit_24_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, STTableShape, STCellBounds in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_build_safety_wit_24_split_goal_2 : build_safety_wit_24_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STCellBounds in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_build_safety_wit_24 : build_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_25_split_goal_1 : build_safety_wit_25_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, STTableShape, STCellBounds in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_build_safety_wit_25_split_goal_2 : build_safety_wit_25_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STCellBounds in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_build_safety_wit_25 : build_safety_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_25_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_25_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_26_split_goal_1 : build_safety_wit_26_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  pose proof (worker_Power2_nonneg j) as Hpow_nonneg.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_26_split_goal_2 : build_safety_wit_26_split_goal_2.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_26 : build_safety_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_26_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_26_split_goal_2.
Qed.

Lemma proof_of_build_safety_wit_27_split_goal_1 : build_safety_wit_27_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  pose proof
    (worker_Power2_double_int_bound_30 j K_pre ltac:(lia) ltac:(lia))
    as Hpow_bound.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_27_split_goal_2 : build_safety_wit_27_split_goal_2.
Proof.
  aggressive_pre_process.
  pose proof (worker_Power2_nonneg j) as Hpow_nonneg.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_safety_wit_27 : build_safety_wit_27.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_safety_wit_27_split_goal_1.
  - Goal_apply proof_of_build_safety_wit_27_split_goal_2.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_1 : build_entail_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold STZeroPrefix.
  intros; lia.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_2 : build_entail_wit_1_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STZeroPrefixBounds.
  split.
  - lia.
  - apply Zlength_nonneg.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_3 : build_entail_wit_1_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  lia.
Qed.

Lemma proof_of_build_entail_wit_1 : build_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_3.
Qed. 

Lemma proof_of_build_entail_wit_2_split_goal_1 : build_entail_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply STZeroPrefix_replace_zero_step.
  - exact PreH8.
  - unfold STTableShape in PreH4.
    lia.
Qed.

Lemma proof_of_build_entail_wit_2_split_goal_2 : build_entail_wit_2_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STZeroPrefixBounds, STTableShape in *.
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_build_entail_wit_2_split_goal_3 : build_entail_wit_2_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold STTableShape in *.
  rewrite Zlength_replace_Znth.
  exact PreH4.
Qed.

Lemma proof_of_build_entail_wit_2 : build_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_2_split_goal_3.
Qed. 

Lemma proof_of_build_entail_wit_3_split_goal_1 : build_entail_wit_3_split_goal_1.
Proof.
  aggressive_pre_process.
  assert (idx = n_pre * K_pre) by lia.
  subst idx.
  exact PreH8.
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_2 : build_entail_wit_3_split_goal_2.
Proof.
  aggressive_pre_process.
  assert (idx = n_pre * K_pre) by lia.
  subst idx.
  exact PreH7.
Qed.

Lemma proof_of_build_entail_wit_3 : build_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_2.
Qed. 

Lemma proof_of_build_entail_wit_4_split_goal_1 : build_entail_wit_4_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold STBasePrefix.
  intros; lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_2 : build_entail_wit_4_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STBasePrefixBounds, RMQSizeSafe in *.
  lia.
Qed.

Lemma proof_of_build_entail_wit_4 : build_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_2.
Qed. 

Lemma proof_of_build_entail_wit_5_split_goal_1 : build_entail_wit_5_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold STCellBounds, STBasePrefixBounds, STTableShape, RMQSizeSafe in *.
  repeat split; nia.
Qed.

Lemma proof_of_build_entail_wit_5_split_goal_2 : build_entail_wit_5_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  nia.
Qed.

Lemma proof_of_build_entail_wit_5_split_goal_3 : build_entail_wit_5_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold STBasePrefixBounds, RMQSizeSafe in *.
  nia.
Qed.

Lemma proof_of_build_entail_wit_5_split_goal_4 : build_entail_wit_5_split_goal_4.
Proof.
  aggressive_pre_process.
  unfold STBasePrefixBounds in *.
  lia.
Qed.

Lemma proof_of_build_entail_wit_5 : build_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_build_entail_wit_5_split_goal_4.
Qed. 

Lemma proof_of_build_entail_wit_6_split_goal_1 : build_entail_wit_6_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, RMQInputValues, STTableShape in *.
  eapply worker_STBasePrefix_write_base_step; eauto; try lia; try nia.
Qed.

Lemma proof_of_build_entail_wit_6_split_goal_2 : build_entail_wit_6_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STBasePrefixBounds in *.
  lia.
Qed.

Lemma proof_of_build_entail_wit_6_split_goal_3 : build_entail_wit_6_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold STTableShape in *.
  rewrite Zlength_replace_Znth.
  exact PreH3.
Qed.

Lemma proof_of_build_entail_wit_6 : build_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_6_split_goal_3.
Qed. 

Lemma proof_of_build_entail_wit_8_split_goal_1 : build_entail_wit_8_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply worker_STBasePrefix_complete_level1; eauto.
  unfold STBasePrefixBounds in PreH5.
  lia.
Qed.

Lemma proof_of_build_entail_wit_8_split_goal_2 : build_entail_wit_8_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STBuiltBeforeLevelBounds, RMQSizeSafe in *.
  lia.
Qed.

Lemma proof_of_build_entail_wit_8 : build_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_8_split_goal_2.
Qed. 

Lemma proof_of_build_entail_wit_9_split_goal_1 : build_entail_wit_9_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold Power2.
  vm_compute.
  reflexivity.
Qed.

Lemma proof_of_build_entail_wit_9_split_goal_2 : build_entail_wit_9_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold Power2.
  vm_compute.
  reflexivity.
Qed.

Lemma proof_of_build_entail_wit_9_split_goal_3 : build_entail_wit_9_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  lia.
Qed.

Lemma proof_of_build_entail_wit_9 : build_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_9_split_goal_3.
Qed. 

Lemma proof_of_build_entail_wit_10_split_goal_1 : build_entail_wit_10_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold STLevelPrefix.
  intros.
  lia.
Qed.

Lemma proof_of_build_entail_wit_10_split_goal_2 : build_entail_wit_10_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STLevelPrefixBounds, RMQSizeSafe in *.
  lia.
Qed.

Lemma proof_of_build_entail_wit_10 : build_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_10_split_goal_2.
Qed. 

Lemma proof_of_build_entail_wit_11_split_goal_1 : build_entail_wit_11_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold STBuiltBeforeLevel in PreH11.
  unfold STBuiltBeforeLevelBounds in PreH9.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH9 as [Hj_nonneg Hj_le].
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  pose proof (worker_Power2_nonneg (j - 1)) as Hhalf_nonneg.
  pose proof (Power2_sub1_double j ltac:(lia)) as Hdouble.
  apply PreH11.
  rewrite Hdouble in PreH8.
  repeat split; lia.
Qed.

Lemma proof_of_build_entail_wit_11_split_goal_2 : build_entail_wit_11_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STBuiltBeforeLevel in PreH11.
  unfold STBuiltBeforeLevelBounds in PreH9.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH9 as [Hj_nonneg Hj_le].
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  pose proof (worker_Power2_nonneg (j - 1)) as Hhalf_nonneg.
  pose proof (Power2_sub1_double j ltac:(lia)) as Hdouble.
  apply PreH11.
  rewrite Hdouble in PreH8.
  repeat split; lia.
Qed.

Lemma proof_of_build_entail_wit_11_split_goal_3 : build_entail_wit_11_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold STCellBounds.
  unfold RMQSizeSafe in PreH2.
  unfold STTableShape in PreH4.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH2 as [_ [_ [HK_pos [HK_le [_ Hn_pow]]]]].
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  pose proof (Power2_pos j ltac:(lia)) as Hj_pow_pos.
  repeat split; try lia.
  all: rewrite PreH4; nia.
Qed.

Lemma proof_of_build_entail_wit_11_split_goal_4 : build_entail_wit_11_split_goal_4.
Proof.
  aggressive_pre_process.
  unfold STCellBounds.
  unfold RMQSizeSafe in PreH2.
  unfold STTableShape in PreH4.
  unfold STBuiltBeforeLevelBounds in PreH9.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH2 as [_ [_ [HK_pos [HK_le [_ Hn_pow]]]]].
  destruct PreH9 as [Hj_nonneg Hj_le].
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  pose proof (Power2_pos (j - 1) ltac:(lia)) as Hhalf_pos.
  pose proof (Power2_sub1_double j ltac:(lia)) as Hdouble.
  rewrite Hdouble in PreH8.
  repeat split; try lia.
  all: rewrite PreH4; nia.
Qed.

Lemma proof_of_build_entail_wit_11_split_goal_5 : build_entail_wit_11_split_goal_5.
Proof.
  aggressive_pre_process.
  unfold STCellBounds.
  unfold RMQSizeSafe in PreH2.
  unfold STTableShape in PreH4.
  unfold STBuiltBeforeLevelBounds in PreH9.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH2 as [_ [_ [HK_pos [HK_le [_ Hn_pow]]]]].
  destruct PreH9 as [Hj_nonneg Hj_le].
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  pose proof (Power2_pos (j - 1) ltac:(lia)) as Hhalf_pos.
  pose proof (Power2_sub1_double j ltac:(lia)) as Hdouble.
  rewrite Hdouble in PreH8.
  repeat split; try lia.
  all: rewrite PreH4; nia.
Qed.

Lemma proof_of_build_entail_wit_11_split_goal_6 : build_entail_wit_11_split_goal_6.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in PreH2.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH2 as [_ [_ [HK_pos [HK_le [_ Hn_pow]]]]].
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  pose proof (Power2_pos j ltac:(lia)) as Hj_pow_pos.
  nia.
Qed.

Lemma proof_of_build_entail_wit_11_split_goal_7 : build_entail_wit_11_split_goal_7.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in PreH2.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH2 as [_ [_ [HK_pos [HK_le [_ Hn_pow]]]]].
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  nia.
Qed.

Lemma proof_of_build_entail_wit_11_split_goal_8 : build_entail_wit_11_split_goal_8.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in PreH2.
  unfold STBuiltBeforeLevelBounds in PreH9.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH2 as [_ [_ [HK_pos [HK_le [_ Hn_pow]]]]].
  destruct PreH9 as [Hj_nonneg Hj_le].
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  pose proof (Power2_pos (j - 1) ltac:(lia)) as Hhalf_pos.
  pose proof (Power2_sub1_double j ltac:(lia)) as Hdouble.
  rewrite Hdouble in PreH8.
  nia.
Qed.

Lemma proof_of_build_entail_wit_11_split_goal_9 : build_entail_wit_11_split_goal_9.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in PreH2.
  unfold STBuiltBeforeLevelBounds in PreH9.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH2 as [_ [_ [HK_pos [HK_le [_ Hn_pow]]]]].
  destruct PreH9 as [Hj_nonneg Hj_le].
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  pose proof (worker_Power2_nonneg (j - 1)) as Hhalf_nonneg.
  nia.
Qed.

Lemma proof_of_build_entail_wit_11_split_goal_10 : build_entail_wit_11_split_goal_10.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in PreH2.
  unfold STBuiltBeforeLevelBounds in PreH9.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH2 as [_ [_ [HK_pos [HK_le [_ Hn_pow]]]]].
  destruct PreH9 as [Hj_nonneg Hj_le].
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  pose proof (Power2_pos (j - 1) ltac:(lia)) as Hhalf_pos.
  pose proof (Power2_sub1_double j ltac:(lia)) as Hdouble.
  rewrite Hdouble in PreH8.
  nia.
Qed.

Lemma proof_of_build_entail_wit_11_split_goal_11 : build_entail_wit_11_split_goal_11.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in PreH2.
  unfold STBuiltBeforeLevelBounds in PreH9.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH2 as [_ [_ [HK_pos [HK_le [_ Hn_pow]]]]].
  destruct PreH9 as [Hj_nonneg Hj_le].
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  nia.
Qed.

Lemma proof_of_build_entail_wit_11_split_goal_12 : build_entail_wit_11_split_goal_12.
Proof.
  aggressive_pre_process.
  unfold STLevelPrefixBounds in PreH10.
  destruct PreH10 as [_ [_ [Hi_nonneg Hi_le]]].
  exact Hi_nonneg.
Qed.

Lemma proof_of_build_entail_wit_11 : build_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_3.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_4.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_5.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_6.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_7.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_8.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_9.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_10.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_11.
  - Goal_apply proof_of_build_entail_wit_11_split_goal_12.
Qed. 

Lemma proof_of_build_entail_wit_13_1_split_goal_1 : build_entail_wit_13_1_split_goal_1.
Proof.
  aggressive_pre_process.
  assert (Ha : a = Znth (i * K_pre + (j - 1)) st_l_2 0) by
    (replace (i * K_pre + (j - 1)) with (i * K_pre + j - 1) by lia;
     exact PreH17).
  assert (Hb : b = Znth ((i + half) * K_pre + (j - 1)) st_l_2 0) by
    (replace ((i + half) * K_pre + (j - 1))
       with ((i + half) * K_pre + j - 1) by lia;
     exact PreH18).
  eapply STLevelPrefix_extend_by_left_max; eauto.
  unfold STTableShape in PreH4.
  lia.
Qed.

Lemma proof_of_build_entail_wit_13_1_split_goal_2 : build_entail_wit_13_1_split_goal_2.
Proof.
  aggressive_pre_process.
  eapply STBuiltBeforeLevel_replace_level_cell.
  - exact PreH24.
  - exact PreH6.
  - unfold STTableShape in PreH4.
    lia.
  - intros row0 col (Hrow0 & Hcol0 & Hcolj & Hrow_range).
    unfold STTableShape in PreH4.
    unfold RMQSizeSafe in PreH2.
    pose proof (Power2_pos col Hcol0).
    split; nia.
Qed.

Lemma proof_of_build_entail_wit_13_1_split_goal_3 : build_entail_wit_13_1_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold STLevelPrefixBounds in *.
  pose proof (Power2_pos j ltac:(lia)).
  nia.
Qed.

Lemma proof_of_build_entail_wit_13_1_split_goal_4 : build_entail_wit_13_1_split_goal_4.
Proof.
  aggressive_pre_process.
  rewrite Znth_replace_Znth_Diff.
  - exact PreH18.
  - unfold STTableShape in PreH4; lia.
  - unfold STTableShape in PreH4; lia.
  - unfold RMQSizeSafe in PreH2.
    pose proof (Power2_pos (j - 1) ltac:(lia)).
    nia.
Qed.

Lemma proof_of_build_entail_wit_13_1_split_goal_5 : build_entail_wit_13_1_split_goal_5.
Proof.
  aggressive_pre_process.
  rewrite Znth_replace_Znth_Diff.
  - exact PreH17.
  - unfold STTableShape in PreH4; lia.
  - unfold STTableShape in PreH4; lia.
  - lia.
Qed.

Lemma proof_of_build_entail_wit_13_1_split_goal_6 : build_entail_wit_13_1_split_goal_6.
Proof.
  aggressive_pre_process.
  unfold STTableShape in *.
  rewrite Zlength_replace_Znth.
  exact PreH4.
Qed.

Lemma proof_of_build_entail_wit_13_1 : build_entail_wit_13_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_13_1_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_13_1_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_13_1_split_goal_3.
  - Goal_apply proof_of_build_entail_wit_13_1_split_goal_4.
  - Goal_apply proof_of_build_entail_wit_13_1_split_goal_5.
  - Goal_apply proof_of_build_entail_wit_13_1_split_goal_6.
Qed. 

Lemma proof_of_build_entail_wit_13_2_split_goal_1 : build_entail_wit_13_2_split_goal_1.
Proof.
  aggressive_pre_process.
  assert (Ha : a = Znth (i * K_pre + (j - 1)) st_l_2 0) by
    (replace (i * K_pre + (j - 1)) with (i * K_pre + j - 1) by lia;
     exact PreH17).
  assert (Hb : b = Znth ((i + half) * K_pre + (j - 1)) st_l_2 0) by
    (replace ((i + half) * K_pre + (j - 1))
       with ((i + half) * K_pre + j - 1) by lia;
     exact PreH18).
  eapply STLevelPrefix_extend_by_right_max; eauto.
  unfold STTableShape in PreH4.
  lia.
Qed.

Lemma proof_of_build_entail_wit_13_2_split_goal_2 : build_entail_wit_13_2_split_goal_2.
Proof.
  aggressive_pre_process.
  eapply STBuiltBeforeLevel_replace_level_cell.
  - exact PreH24.
  - exact PreH6.
  - unfold STTableShape in PreH4.
    lia.
  - intros row0 col (Hrow0 & Hcol0 & Hcolj & Hrow_range).
    unfold STTableShape in PreH4.
    unfold RMQSizeSafe in PreH2.
    pose proof (Power2_pos col Hcol0).
    split; nia.
Qed.

Lemma proof_of_build_entail_wit_13_2_split_goal_3 : build_entail_wit_13_2_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold STLevelPrefixBounds in *.
  pose proof (Power2_pos j ltac:(lia)).
  nia.
Qed.

Lemma proof_of_build_entail_wit_13_2_split_goal_4 : build_entail_wit_13_2_split_goal_4.
Proof.
  aggressive_pre_process.
  rewrite Znth_replace_Znth_Diff.
  - exact PreH18.
  - unfold STTableShape in PreH4; lia.
  - unfold STTableShape in PreH4; lia.
  - unfold RMQSizeSafe in PreH2.
    pose proof (Power2_pos (j - 1) ltac:(lia)).
    nia.
Qed.

Lemma proof_of_build_entail_wit_13_2_split_goal_5 : build_entail_wit_13_2_split_goal_5.
Proof.
  aggressive_pre_process.
  rewrite Znth_replace_Znth_Diff.
  - exact PreH17.
  - unfold STTableShape in PreH4; lia.
  - unfold STTableShape in PreH4; lia.
  - lia.
Qed.

Lemma proof_of_build_entail_wit_13_2_split_goal_6 : build_entail_wit_13_2_split_goal_6.
Proof.
  aggressive_pre_process.
  unfold STTableShape in *.
  rewrite Zlength_replace_Znth.
  exact PreH4.
Qed.

Lemma proof_of_build_entail_wit_13_2 : build_entail_wit_13_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_13_2_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_13_2_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_13_2_split_goal_3.
  - Goal_apply proof_of_build_entail_wit_13_2_split_goal_4.
  - Goal_apply proof_of_build_entail_wit_13_2_split_goal_5.
  - Goal_apply proof_of_build_entail_wit_13_2_split_goal_6.
Qed. 

Lemma proof_of_build_entail_wit_15_split_goal_1 : build_entail_wit_15_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply STLevelPrefix_exit_to_built_step; eauto.
Qed.

Lemma proof_of_build_entail_wit_15_split_goal_2 : build_entail_wit_15_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STBuiltBeforeLevelBounds in *.
  lia.
Qed.

Lemma proof_of_build_entail_wit_15 : build_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_15_split_goal_2.
Qed. 

Lemma proof_of_build_entail_wit_16_split_goal_1 : build_entail_wit_16_split_goal_1.
Proof.
  aggressive_pre_process.
  rewrite PreH7.
  apply Power2_step.
  lia.
Qed.

Lemma proof_of_build_entail_wit_16_split_goal_2 : build_entail_wit_16_split_goal_2.
Proof.
  aggressive_pre_process.
  replace (j + 1 - 1) with j by lia.
  exact PreH7.
Qed.

Lemma proof_of_build_entail_wit_16 : build_entail_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_16_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_16_split_goal_2.
Qed. 

Lemma proof_of_build_return_wit_1_split_goal_1 : build_return_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold STBuilt.
  assert (j = K_pre) by lia.
  subst j.
  exact PreH10.
Qed.

Lemma proof_of_build_return_wit_1_split_goal_2 : build_return_wit_1_split_goal_2.
Proof.
  aggressive_pre_process.
  assert (j = K_pre) by lia.
  subst j.
  exact PreH9.
Qed.

Lemma proof_of_build_return_wit_1 : build_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_return_wit_1_split_goal_1.
  - Goal_apply proof_of_build_return_wit_1_split_goal_2.
Qed. 

Lemma proof_of_query_safety_wit_1_split_goal_1 : query_safety_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryIntervalBounds in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_1_split_goal_2 : query_safety_wit_1_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryIntervalBounds in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_1 : query_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_query_safety_wit_2_split_goal_1 : query_safety_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryIntervalBounds in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_2_split_goal_2 : query_safety_wit_2_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryIntervalBounds in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_2 : query_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_query_safety_wit_6_split_goal_1 : query_safety_wit_6_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryLogBounds, QueryLogLoopState in *.
  dump_pre_spatial.
  pose proof (worker_Power2_double_int_bound_30 k K_pre) as Hbound.
  lia.
Qed.

Lemma proof_of_query_safety_wit_6_split_goal_2 : query_safety_wit_6_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold QueryLogBounds, QueryLogLoopState in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_6 : query_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_query_safety_wit_8_split_goal_1 : query_safety_wit_8_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryIntervalBounds in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_8_split_goal_2 : query_safety_wit_8_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold QueryLogBounds, QueryLogLoopState in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_8 : query_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_8_split_goal_2.
Qed.

Lemma proof_of_query_safety_wit_10_split_goal_1 : query_safety_wit_10_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryLogBounds in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_10_split_goal_2 : query_safety_wit_10_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold QueryLogBounds in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_10 : query_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_query_safety_wit_11_split_goal_1 : query_safety_wit_11_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_11_split_goal_2 : query_safety_wit_11_split_goal_2.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_11 : query_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_query_safety_wit_12_split_goal_1 : query_safety_wit_12_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryLogBounds in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_12_split_goal_2 : query_safety_wit_12_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryIntervalBounds in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_query_safety_wit_12 : query_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_query_safety_wit_13_split_goal_1 : query_safety_wit_13_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_13_split_goal_2 : query_safety_wit_13_split_goal_2.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_13 : query_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_13_split_goal_2.
Qed.

Lemma proof_of_query_safety_wit_14_split_goal_1 : query_safety_wit_14_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryIntervalBounds, QueryLogBounds,
    QueryLogFinalState, QueryLogLoopState in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_query_safety_wit_14_split_goal_2 : query_safety_wit_14_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold QueryIntervalBounds, QueryLogBounds,
    QueryLogFinalState, QueryLogLoopState in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_query_safety_wit_14 : query_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_14_split_goal_2.
Qed.

Lemma proof_of_query_safety_wit_15_split_goal_1 : query_safety_wit_15_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryIntervalBounds, QueryLogBounds,
    QueryLogFinalState, QueryLogLoopState in *.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_query_safety_wit_15_split_goal_2 : query_safety_wit_15_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold QueryIntervalBounds, QueryLogBounds,
    QueryLogFinalState, QueryLogLoopState in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_15 : query_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_query_safety_wit_16_split_goal_1 : query_safety_wit_16_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold RMQSizeSafe, QueryIntervalBounds, QueryLogBounds,
    QueryLogFinalState, QueryLogLoopState in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_16_split_goal_2 : query_safety_wit_16_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold QueryIntervalBounds, QueryLogBounds,
    QueryLogFinalState, QueryLogLoopState in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_16 : query_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_16_split_goal_2.
Qed.

Lemma proof_of_query_entail_wit_1_split_goal_1 : query_entail_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  apply QueryLogLoopState_init.
  - unfold QueryIntervalBounds in PreH2; lia.
  - unfold QueryIntervalBounds in PreH2; lia.
Qed.

Lemma proof_of_query_entail_wit_1_split_goal_2 : query_entail_wit_1_split_goal_2.
Proof.
  aggressive_pre_process.
  apply QueryLogBounds_init.
  - unfold RMQSizeSafe in PreH1; lia.
  - unfold RMQSizeSafe in PreH1; lia.
  - unfold RMQSizeSafe in PreH1; lia.
  - unfold QueryIntervalBounds in PreH2; lia.
  - unfold QueryIntervalBounds in PreH2; lia.
  - unfold QueryIntervalBounds in PreH2; lia.
Qed.

Lemma proof_of_query_entail_wit_1 : query_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_query_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_query_entail_wit_2_split_goal_1 : query_entail_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  rewrite <- PreH4.
  eapply QueryLogLoopState_step; eauto.
Qed.

Lemma proof_of_query_entail_wit_2_split_goal_2 : query_entail_wit_2_split_goal_2.
Proof.
  aggressive_pre_process.
  rewrite <- PreH4.
  eapply QueryLogBounds_step; eauto.
Qed.

Lemma proof_of_query_entail_wit_2 : query_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_query_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_1 : query_entail_wit_3_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold STBuilt, STBuiltBeforeLevel in PreH8.
  unfold QueryIntervalBounds in PreH3.
  unfold QueryLogBounds in PreH9.
  unfold QueryLogLoopState in PreH10.
  destruct PreH3 as [Hleft_nonneg [Hleft_right Hright_n]].
  destruct PreH9 as
    [Hlen_pos [Hlen_n [HK_pos [Hn_pow [Hk_nonneg [Hk_K Hpow_pos]]]]]].
  destruct PreH10 as [_ [Hpow_eq Hpow_le]].
  apply PreH8.
  repeat split; lia.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_2 : query_entail_wit_3_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold STBuilt, STBuiltBeforeLevel in PreH8.
  unfold QueryIntervalBounds in PreH3.
  unfold QueryLogBounds in PreH9.
  unfold QueryLogLoopState in PreH10.
  destruct PreH3 as [Hleft_nonneg [Hleft_right Hright_n]].
  destruct PreH9 as
    [Hlen_pos [Hlen_n [HK_pos [Hn_pow [Hk_nonneg [Hk_K Hpow_pos]]]]]].
  destruct PreH10 as [_ [Hpow_eq Hpow_le]].
  apply PreH8.
  repeat split; lia.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_3 : query_entail_wit_3_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold STCellBounds.
  unfold QueryIntervalBounds in PreH3.
  unfold STTableShape in PreH6.
  unfold QueryLogBounds in PreH9.
  unfold QueryLogLoopState in PreH10.
  destruct PreH3 as [Hleft_nonneg [Hleft_right Hright_n]].
  destruct PreH9 as
    [Hlen_pos [Hlen_n [HK_pos [Hn_pow [Hk_nonneg [Hk_K Hpow_pos]]]]]].
  destruct PreH10 as [_ [Hpow_eq Hpow_le]].
  repeat split; try lia.
  all: try rewrite PreH6; nia.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_4 : query_entail_wit_3_split_goal_4.
Proof.
  aggressive_pre_process.
  unfold STCellBounds.
  unfold QueryIntervalBounds in PreH3.
  unfold STTableShape in PreH6.
  unfold QueryLogBounds in PreH9.
  unfold QueryLogLoopState in PreH10.
  destruct PreH3 as [Hleft_nonneg [Hleft_right Hright_n]].
  destruct PreH9 as
    [Hlen_pos [Hlen_n [HK_pos [Hn_pow [Hk_nonneg [Hk_K Hpow_pos]]]]]].
  destruct PreH10 as [_ [Hpow_eq Hpow_le]].
  repeat split; try lia.
  all: try rewrite PreH6; nia.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_5 : query_entail_wit_3_split_goal_5.
Proof.
  aggressive_pre_process.
  unfold QueryIntervalBounds in PreH3.
  unfold QueryLogBounds in PreH9.
  unfold QueryLogLoopState in PreH10.
  destruct PreH3 as [Hleft_nonneg [Hleft_right Hright_n]].
  destruct PreH9 as
    [Hlen_pos [Hlen_n [HK_pos [Hn_pow [Hk_nonneg [Hk_K Hpow_pos]]]]]].
  destruct PreH10 as [_ [Hpow_eq Hpow_le]].
  nia.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_6 : query_entail_wit_3_split_goal_6.
Proof.
  aggressive_pre_process.
  unfold QueryIntervalBounds in PreH3.
  unfold QueryLogBounds in PreH9.
  unfold QueryLogLoopState in PreH10.
  destruct PreH3 as [Hleft_nonneg [Hleft_right Hright_n]].
  destruct PreH9 as
    [Hlen_pos [Hlen_n [HK_pos [Hn_pow [Hk_nonneg [Hk_K Hpow_pos]]]]]].
  destruct PreH10 as [_ [Hpow_eq Hpow_le]].
  nia.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_7 : query_entail_wit_3_split_goal_7.
Proof.
  aggressive_pre_process.
  unfold QueryIntervalBounds in PreH3.
  unfold QueryLogBounds in PreH9.
  destruct PreH3 as [Hleft_nonneg [Hleft_right Hright_n]].
  destruct PreH9 as
    [Hlen_pos [Hlen_n [HK_pos [Hn_pow [Hk_nonneg [Hk_K Hpow_pos]]]]]].
  nia.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_8 : query_entail_wit_3_split_goal_8.
Proof.
  aggressive_pre_process.
  unfold QueryIntervalBounds in PreH3.
  unfold QueryLogBounds in PreH9.
  destruct PreH3 as [Hleft_nonneg [Hleft_right Hright_n]].
  destruct PreH9 as
    [Hlen_pos [Hlen_n [HK_pos [Hn_pow [Hk_nonneg [Hk_K Hpow_pos]]]]]].
  nia.
Qed.

Lemma proof_of_query_entail_wit_3_split_goal_9 : query_entail_wit_3_split_goal_9.
Proof.
  aggressive_pre_process.
  rewrite <- PreH4.
  unfold QueryLogFinalState.
  split.
  - exact PreH10.
  - unfold QueryLogLoopState in PreH10.
    destruct PreH10 as [Hk_nonneg [Hpow_eq Hpow_le]].
    pose proof (Power2_step_query k Hk_nonneg) as Hstep.
    lia.
Qed.

Lemma proof_of_query_entail_wit_3 : query_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_5.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_6.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_7.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_8.
  - Goal_apply proof_of_query_entail_wit_3_split_goal_9.
Qed. 

Lemma proof_of_query_entail_wit_5_split_goal_1 : query_entail_wit_5_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply RangeMaxValue_sparse_query_left; eauto.
Qed.

Lemma proof_of_query_entail_wit_5 : query_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_query_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_query_entail_wit_6_split_goal_1 : query_entail_wit_6_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply RangeMaxValue_sparse_query_right; eauto.
Qed.

Lemma proof_of_query_entail_wit_6 : query_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_query_entail_wit_6_split_goal_1.
Qed.
