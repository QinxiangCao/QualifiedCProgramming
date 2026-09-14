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
From SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication Require Import matrix_chain_multiplication_goal.
From SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication Require Import matrix_chain_multiplication_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib.
Local Open Scope sac.

Lemma proof_of_matrixChainMinCost_entail_wit_1_split_goal_1 : matrixChainMinCost_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainZeroPrefix.
  split.
  - reflexivity.
  - intros index Hindex. lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_1 : matrixChainMinCost_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_2_split_goal_1 : matrixChainMinCost_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainZeroPrefix in *.
  destruct PreH8 as [Hlength Hzero].
  split.
  - rewrite Zlength_app, Hlength. reflexivity.
  - intros index Hindex.
    destruct (Z_lt_ge_dec index i) as [Hlt | Hge].
    + rewrite app_Znth1.
      * apply Hzero. lia.
      * lia.
    + assert (index = i) by lia. subst index.
      rewrite app_Znth2.
      * rewrite Hlength. replace (i - i) with 0 by lia.
        rewrite Znth0_cons. reflexivity.
      * lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_2 : matrixChainMinCost_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_3 : matrixChainMinCost_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = matrix_count_pre * matrix_count_pre) by lia.
  subst i.
  destruct PreH8 as [Htable Hzero].
  Exists cost_l_2.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic
      (IntArray.seg_to_full cost_pre 0
         (matrix_count_pre * matrix_count_pre) cost_l_2).
    cancel (IntArray.full dimensions_pre
              (matrix_count_pre + 1) dimensions_l).
    replace (cost_pre + 0 * sizeof(INT)) with cost_pre by lia.
    replace (matrix_count_pre * matrix_count_pre - 0)
      with (matrix_count_pre * matrix_count_pre) by lia.
    cancel (IntArray.full cost_pre
              (matrix_count_pre * matrix_count_pre) cost_l_2).
  - split_pures.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact Htable.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial.
      unfold MatrixChainTableValuesBounded.
      intros index Hindex.
      rewrite Hzero by lia. lia.
    + dump_pre_spatial.
      apply matrix_chain_zero_table_lengths_done__initialization.
      * exact PreH2.
      * exact PreH4.
      * split; assumption.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_1 : matrixChainMinCost_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainLeftProgress.
  split.
  - exact PreH10.
  - intros left right Hleft. lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_5 : matrixChainMinCost_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_1 : matrixChainMinCost_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_2 : matrixChainMinCost_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_3 : matrixChainMinCost_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound (left + 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_4 : matrixChainMinCost_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound (left + 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_5 : matrixChainMinCost_entail_wit_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound left ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_6 : matrixChainMinCost_entail_wit_6_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound left ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_7 : matrixChainMinCost_entail_wit_6_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH11.
  specialize (PreH11
    (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1))
    ltac:(rewrite PreH5; nia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_8 : matrixChainMinCost_entail_wit_6_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH11.
  specialize (PreH11
    (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1))
    ltac:(rewrite PreH5; nia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_9 : matrixChainMinCost_entail_wit_6_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH11.
  specialize (PreH11 (left * matrix_count_pre + left)
    ltac:(rewrite PreH5; nia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_10 : matrixChainMinCost_entail_wit_6_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH11.
  specialize (PreH11 (left * matrix_count_pre + left)
    ltac:(rewrite PreH5; nia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_11 : matrixChainMinCost_entail_wit_6_split_goal_11.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_12 : matrixChainMinCost_entail_wit_6_split_goal_12.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6 : matrixChainMinCost_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_3.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_4.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_5.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_6.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_7.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_8.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_9.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_10.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_11.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_6_split_goal_12.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_1 : matrixChainMinCost_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply matrix_chain_split_progress_initial__candidate_progress.
  exact PreH34.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_2 : matrixChainMinCost_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainLeftProgress in PreH34.
  destruct PreH34 as [Hlengths _].
  unfold MatrixChainLengthsDone in Hlengths.
  destruct Hlengths as [_ Hdone].
  assert (Hleft_minimum :
    MatrixChainIntervalMinimum dimensions_l left left
      (Znth (left * matrix_count_pre + left) cost_l 0)).
  {
    eapply Hdone with (length := 1); lia.
  }
  assert (Hright_minimum :
    MatrixChainIntervalMinimum dimensions_l (left + 1)
      (left + chain_length - 1)
      (Znth ((left + 1) * matrix_count_pre +
             (left + chain_length - 1)) cost_l 0)).
  {
    eapply Hdone with (length := chain_length - 1); lia.
  }
  pose proof
    (matrix_chain_interval_minimum_upper_bound__candidate_progress
       dimensions_l matrix_count_pre left left
       (Znth (left * matrix_count_pre + left) cost_l 0)
       PreH32 ltac:(lia) ltac:(lia) ltac:(lia) Hleft_minimum)
    as Hleft_bound.
  pose proof
    (matrix_chain_interval_minimum_upper_bound__candidate_progress
       dimensions_l matrix_count_pre (left + 1)
       (left + chain_length - 1)
       (Znth ((left + 1) * matrix_count_pre +
              (left + chain_length - 1)) cost_l 0)
       PreH32 ltac:(lia) ltac:(lia) ltac:(lia) Hright_minimum)
    as Hright_bound.
  assert (Htwo_dimensions :
    Znth left dimensions_l 0 * Znth (left + 1) dimensions_l 0 <= 10000)
    by nia.
  assert (Hlast_lower :
    1 <= Znth ((left + chain_length - 1) + 1) dimensions_l 0).
  {
    replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
    exact PreH30.
  }
  assert (Hlast_upper :
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 100).
  {
    replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
    exact PreH31.
  }
  assert (Hproduct_step :
    (Znth left dimensions_l 0 * Znth (left + 1) dimensions_l 0) *
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <=
    10000 * Znth ((left + chain_length - 1) + 1) dimensions_l 0).
  {
    apply Z.mul_le_mono_nonneg_r; lia.
  }
  assert (Hproduct :
    Znth left dimensions_l 0 * Znth (left + 1) dimensions_l 0 *
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 1000000)
    by lia.
  nia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_7 : matrixChainMinCost_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_7_split_goal_2.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_1 : matrixChainMinCost_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_2 : matrixChainMinCost_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_3 : matrixChainMinCost_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound (split + 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_4 : matrixChainMinCost_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound (split + 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_5 : matrixChainMinCost_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound left ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_6 : matrixChainMinCost_entail_wit_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound left ltac:(lia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_7 : matrixChainMinCost_entail_wit_8_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH18.
  specialize (PreH18
    (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1))
    ltac:(rewrite PreH16; nia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_8 : matrixChainMinCost_entail_wit_8_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH18.
  specialize (PreH18
    (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1))
    ltac:(rewrite PreH16; nia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_9 : matrixChainMinCost_entail_wit_8_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH18.
  specialize (PreH18 (left * matrix_count_pre + split)
    ltac:(rewrite PreH16; nia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_10 : matrixChainMinCost_entail_wit_8_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH18.
  specialize (PreH18 (left * matrix_count_pre + split)
    ltac:(rewrite PreH16; nia)).
  lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_11 : matrixChainMinCost_entail_wit_8_split_goal_11.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_12 : matrixChainMinCost_entail_wit_8_split_goal_12.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8 : matrixChainMinCost_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_5.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_6.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_7.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_8.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_9.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_10.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_11.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_8_split_goal_12.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_9_split_goal_1 : matrixChainMinCost_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_9_split_goal_2 : matrixChainMinCost_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainSplitProgress in PreH38.
  destruct PreH38 as [Hleft_progress _].
  unfold MatrixChainLeftProgress in Hleft_progress.
  destruct Hleft_progress as [Hlengths _].
  unfold MatrixChainLengthsDone in Hlengths.
  destruct Hlengths as [_ Hdone].
  assert (Hleft_minimum :
    MatrixChainIntervalMinimum dimensions_l left split
      (Znth (left * matrix_count_pre + split) cost_l 0)).
  {
    eapply Hdone with (length := split - left + 1); lia.
  }
  assert (Hright_minimum :
    MatrixChainIntervalMinimum dimensions_l (split + 1)
      (left + chain_length - 1)
      (Znth ((split + 1) * matrix_count_pre +
             (left + chain_length - 1)) cost_l 0)).
  {
    eapply Hdone with (length := left + chain_length - split - 1); lia.
  }
  pose proof
    (matrix_chain_interval_minimum_upper_bound__candidate_progress
       dimensions_l matrix_count_pre left split
       (Znth (left * matrix_count_pre + split) cost_l 0)
       PreH36 ltac:(lia) ltac:(lia) ltac:(lia) Hleft_minimum)
    as Hleft_bound.
  pose proof
    (matrix_chain_interval_minimum_upper_bound__candidate_progress
       dimensions_l matrix_count_pre (split + 1)
       (left + chain_length - 1)
       (Znth ((split + 1) * matrix_count_pre +
              (left + chain_length - 1)) cost_l 0)
       PreH36 ltac:(lia) ltac:(lia) ltac:(lia) Hright_minimum)
    as Hright_bound.
  assert (Htwo_dimensions :
    Znth left dimensions_l 0 * Znth (split + 1) dimensions_l 0 <= 10000)
    by nia.
  assert (Hlast_lower :
    1 <= Znth ((left + chain_length - 1) + 1) dimensions_l 0).
  {
    replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
    exact PreH34.
  }
  assert (Hlast_upper :
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 100).
  {
    replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
    exact PreH35.
  }
  assert (Hproduct_step :
    (Znth left dimensions_l 0 * Znth (split + 1) dimensions_l 0) *
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <=
    10000 * Znth ((left + chain_length - 1) + 1) dimensions_l 0).
  {
    apply Z.mul_le_mono_nonneg_r; lia.
  }
  assert (Hproduct :
    Znth left dimensions_l 0 * Znth (split + 1) dimensions_l 0 *
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 1000000)
    by lia.
  nia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_9 : matrixChainMinCost_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_9_split_goal_2.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_10_1_split_goal_1 : matrixChainMinCost_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8 in PreH21.
  apply (matrix_chain_split_progress_better__min_update
    dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length
    left split best candidate);
    [lia | lia | exact PreH21 | exact PreH22].
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_10_1 : matrixChainMinCost_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_10_1_split_goal_1.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_10_2_split_goal_1 : matrixChainMinCost_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8 in PreH21.
  apply (matrix_chain_split_progress_not_better__min_update
    dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length
    left split best candidate);
    [lia | lia | exact PreH21 | exact PreH22].
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_10_2 : matrixChainMinCost_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_10_2_split_goal_1.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_11_split_goal_1 : matrixChainMinCost_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (matrix_chain_split_progress_complete__min_update
    dimensions_l cost_l_2 matrix_count_pre chain_length left
    (left + chain_length - 1) best).
  - exact PreH4.
  - exact PreH6.
  - reflexivity.
  - lia.
  - lia.
  - replace (left + chain_length - 1) with split by lia.
    exact PreH19.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_11_split_goal_2 : matrixChainMinCost_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (left + chain_length - 1) with split by lia.
  exact PreH19.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_11_split_goal_3 : matrixChainMinCost_entail_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_11 : matrixChainMinCost_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_11_split_goal_3.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_12_split_goal_1 : matrixChainMinCost_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcurrent :
      0 <= left * matrix_count_pre + (left + chain_length - 1) <
           Zlength cost_l_2).
  { rewrite PreH15. rewrite <- PreH7. lia. }
  unfold MatrixChainSplitProgress in PreH18.
  destruct PreH18 as [Hprogress _].
  unfold MatrixChainLeftProgress in *.
  destruct Hprogress as [Hlengths Hleft].
  split.
  - unfold MatrixChainLengthsDone in *.
    destruct Hlengths as [Hnext Hdone].
    split; [exact Hnext |].
    intros length0 left0 right0 Hlength0 Hright0 Hleft0 Hfits0.
    specialize (Hdone length0 left0 right0 Hlength0 Hright0 Hleft0 Hfits0).
    rewrite Znth_replace_Znth_Diff.
    + exact Hdone.
    + exact Hcurrent.
    + rewrite PreH15. nia.
    + intro Heq.
      assert (Hright0_range : 0 <= right0 < matrix_count_pre) by lia.
      assert (Hright_range :
          0 <= left + chain_length - 1 < matrix_count_pre) by lia.
      destruct (Z.lt_trichotomy left0 left) as [Hlt | [Heql | Hgt]].
      * assert (left0 * matrix_count_pre + right0 <
                left * matrix_count_pre) by nia.
        nia.
      * subst left0. nia.
      * assert (left * matrix_count_pre + (left + chain_length - 1) <
                left0 * matrix_count_pre) by nia.
        nia.
  - intros left0 right0 Hleft0 Hright0 Hfits0.
    destruct (Z.eq_dec left0 left) as [Heq | Hneq].
    + subst left0.
      assert (right0 = left + chain_length - 1) by lia.
      subst right0.
      rewrite Znth_replace_Znth_Same by exact Hcurrent.
      replace (left + chain_length - 1) with right by lia.
      exact PreH19.
    + assert (Hleft0_old : 0 <= left0 < left) by lia.
      specialize (Hleft left0 right0 Hleft0_old Hright0 Hfits0).
      rewrite Znth_replace_Znth_Diff.
      * exact Hleft.
      * exact Hcurrent.
      * rewrite PreH15. nia.
      * intro Hindices.
        assert (Hright0_range : 0 <= right0 < matrix_count_pre) by lia.
        assert (Hright_range :
            0 <= left + chain_length - 1 < matrix_count_pre) by lia.
        assert (left0 * matrix_count_pre + right0 <
                left * matrix_count_pre) by nia.
        nia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_12_split_goal_2 : matrixChainMinCost_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcurrent :
      0 <= left * matrix_count_pre + (left + chain_length - 1) <
           Zlength cost_l_2).
  { rewrite PreH15. rewrite <- PreH7. lia. }
  unfold MatrixChainTableValuesBounded in *.
  intros index Hindex.
  rewrite Zlength_replace_Znth in Hindex.
  destruct (Z.eq_dec index
      (left * matrix_count_pre + (left + chain_length - 1))) as [Heq | Hneq].
  - subst index.
    rewrite Znth_replace_Znth_Same by exact Hcurrent.
    lia.
  - rewrite Znth_replace_Znth_Diff.
    + apply PreH17. exact Hindex.
    + exact Hcurrent.
    + exact Hindex.
    + intro Heq. apply Hneq. symmetry. exact Heq.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_12_split_goal_3 : matrixChainMinCost_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH15.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_12 : matrixChainMinCost_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_12_split_goal_2.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_12_split_goal_3.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_13_split_goal_1 : matrixChainMinCost_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainLeftProgress in PreH12.
  destruct PreH12 as [Hlengths Hleft].
  unfold MatrixChainLengthsDone in *.
  destruct Hlengths as [Hlengths_lb Hlengths_done].
  split.
  - lia.
  - intros length0 left0 right0 Hlength0 Hright0 Hleft0 Hfits0.
    destruct (Z_lt_ge_dec length0 chain_length) as [Hlt | Hge].
    + eapply Hlengths_done; eauto; lia.
    + assert (length0 = chain_length) by lia.
      subst length0.
      eapply Hleft; eauto; lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_13 : matrixChainMinCost_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_13_split_goal_1.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_14_split_goal_1 : matrixChainMinCost_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hchain : chain_length = matrix_count_pre + 1) by lia.
  unfold MatrixChainMinimumCost.
  split.
  - exact PreH4.
  - unfold MatrixChainLengthsDone in PreH10.
    destruct PreH10 as [_ Hdone].
    eapply Hdone with (length := matrix_count_pre) (left := 0) (right := matrix_count_pre - 1).
    + rewrite Hchain. lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_14_split_goal_2 : matrixChainMinCost_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hchain : chain_length = matrix_count_pre + 1) by lia.
  unfold MatrixChainTableResult.
  split.
  - exact PreH5.
  - intros left0 right0 [Hleft0 [Horder Hright0]].
    unfold MatrixChainLengthsDone in PreH10.
    destruct PreH10 as [_ Hdone].
    eapply Hdone with
        (length := right0 - left0 + 1)
        (left := left0) (right := right0).
    + rewrite Hchain. lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_14_split_goal_3 : matrixChainMinCost_entail_wit_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (matrix_count_pre + 1) with chain_length by lia.
  exact PreH10.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_14_split_goal_4 : matrixChainMinCost_entail_wit_14_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH9.
  specialize (PreH9 (matrix_count_pre - 1)).
  rewrite PreH5 in PreH9.
  destruct PreH9 as [_ Hupper]; nia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_14_split_goal_5 : matrixChainMinCost_entail_wit_14_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH9.
  specialize (PreH9 (matrix_count_pre - 1)).
  rewrite PreH5 in PreH9.
  destruct PreH9 as [Hlower _]; nia.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_14 : matrixChainMinCost_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_14_split_goal_1.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_14_split_goal_2.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_14_split_goal_3.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_14_split_goal_4.
  - Goal_apply proof_of_matrixChainMinCost_entail_wit_14_split_goal_5.
Qed.
