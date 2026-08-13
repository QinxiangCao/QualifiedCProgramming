Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum Require Import split_array_largest_sum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_lib.
Local Open Scope sac.

Lemma proof_of_check_entail_wit_1 : check_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    all: dump_pre_spatial; try lia; eauto using prefix_split_state_zero.
Qed.

Lemma proof_of_check_entail_wit_2_1 : check_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    all: dump_pre_spatial; try lia; eauto using prefix_split_state_step_over_cap.
Qed.

Lemma proof_of_check_entail_wit_2_2 : check_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    all: dump_pre_spatial; try lia; eauto using prefix_split_state_extend_no_split.
    + pose proof (PreH11 i ltac:(lia)); lia.
    + eapply PrefixSplitState_extend; try eassumption; try lia.
      pose proof (PreH11 i ltac:(lia)); lia.
Qed.

Lemma proof_of_check_return_wit_1 : check_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; intros Hcontra; lia.
    + dump_pre_spatial.
      intros _. unfold CannotSplit.
      intros cnt' cur' Hstate.
      assert (Hi_len : i = Zlength l) by lia.
      subst i.
      pose proof (PrefixSplitState_unique _ _ _ _ _ _ _ PreH17 Hstate) as [Hcnt _].
      lia.
Qed.

Lemma proof_of_check_return_wit_2 : check_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial.
      intros _. unfold CanSplit.
      exists cnt, cur.
      split; [replace (Zlength l) with i by lia; exact PreH17 | lia].
    + dump_pre_spatial; intros Hcontra; lia.
Qed.

Lemma proof_of_check_return_wit_3 : check_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; intros Hcontra; lia.
    + dump_pre_spatial.
      intros _. unfold CannotSplit.
      intros cnt' cur' Hstate.
      pose proof (PrefixSplitState_items_bound _ _ _ _ _ Hstate i) as Hitem.
      exfalso.
      specialize (Hitem ltac:(lia)).
      lia.
Qed.

Lemma proof_of_splitArrayLargestSum_safety_wit_3 : splitArrayLargestSum_safety_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures.
  - dump_pre_spatial.
    assert (Hdiff_nonneg : 0 <= right - left) by lia.
    assert (Hquot_le : (right - left) ÷ 2 <= right - left) by
      (apply Z.quot_le_upper_bound; lia).
    lia.
  - dump_pre_spatial.
    assert (Hdiff_nonneg : 0 <= right - left) by lia.
    assert (Hquot_nonneg : 0 <= (right - left) ÷ 2) by
      (apply Z.quot_pos; lia).
    lia.
Qed. 

Lemma proof_of_splitArrayLargestSum_safety_wit_7 : splitArrayLargestSum_safety_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures.
  - dump_pre_spatial.
    assert (Hdiff_nonneg : 0 <= right - left) by lia.
    assert (Hquot_le : (right - left) ÷ 2 <= right - left) by
      (apply Z.quot_le_upper_bound; lia).
    lia.
  - dump_pre_spatial.
    assert (Hdiff_nonneg : 0 <= right - left) by lia.
    assert (Hquot_nonneg : 0 <= (right - left) ÷ 2) by
      (apply Z.quot_pos; lia).
    lia.
Qed. 

Lemma proof_of_splitArrayLargestSum_entail_wit_1 : splitArrayLargestSum_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ans.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_splitArrayLargestSum_entail_wit_2_1 : splitArrayLargestSum_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists res_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    + destruct (mid_quot_bounds left right PreH12 PreH5 PreH13) as [_ Hmid_upper].
      exact Hmid_upper.
    + assert (Hq_nonneg : 0 <= (right - left) ÷ 2) by (apply Z.quot_pos; lia).
      pose proof (Zplus_le_compat_l _ _ left Hq_nonneg) as Hleft_mid.
      replace (left + 0) with left in Hleft_mid by ring.
      exact Hleft_mid.
    + assert (Hcan_mid :
        CanSplit l m_pre (left + (right - left) ÷ 2)) by
        (apply PreH3; lia).
      pose proof (minmax_can_lower_bound
        l m_pre res_2 (left + (right - left) ÷ 2)) as Hcannot_bound.
      specialize (Hcannot_bound ltac:(rewrite PreH10; lia)).
      specialize (Hcannot_bound ltac:(intros k Hk; pose proof (PreH11 k ltac:(lia)); lia)).
      specialize (Hcannot_bound PreH17 Hcan_mid).
      lia.
Qed. 

Lemma proof_of_splitArrayLargestSum_entail_wit_2_2 : splitArrayLargestSum_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists res_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    + destruct (mid_quot_bounds left right PreH12 PreH5 PreH13) as [Hmid_nonneg _].
      lia.
    + assert (Hq_lt : (right - left) ÷ 2 < right - left) by
        (apply Z.quot_lt; lia).
      lia.
    + assert (Hcannot_mid :
        CannotSplit l m_pre (left + (right - left) ÷ 2)) by
        (apply PreH4; exact PreH18).
      pose proof (minmax_cannot_upper_bound
        l m_pre res_2 (left + (right - left) ÷ 2)) as Hcan_bound.
      specialize (Hcan_bound ltac:(
        assert (0 <= (right - left) ÷ 2) by (apply Z.quot_pos; lia);
        lia)).
      specialize (Hcan_bound ltac:(intros k Hk; pose proof (PreH11 k ltac:(lia)); lia)).
      specialize (Hcan_bound PreH17 Hcannot_mid).
      lia.
Qed. 

Lemma proof_of_splitArrayLargestSum_partial_solve_wit_1_pure : splitArrayLargestSum_partial_solve_wit_1_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; try solve [dump_pre_spatial; auto].
  - dump_pre_spatial.
    assert (Hdiff_nonneg : 0 <= right - left) by lia.
    assert (Hquot_le : (right - left) ÷ 2 <= right - left) by
      (apply Z.quot_le_upper_bound; lia).
    lia.
  - dump_pre_spatial.
    assert (Hdiff_nonneg : 0 <= right - left) by lia.
    assert (Hquot_nonneg : 0 <= (right - left) ÷ 2) by
      (apply Z.quot_pos; lia).
    lia.
Qed. 


Lemma proof_of_splitArrayLargestSum_return_wit_1 : splitArrayLargestSum_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    assert (left = res) by lia.
    subst res. 
    auto.
Qed.
