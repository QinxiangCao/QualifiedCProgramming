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
From SimpleC.EE.LLM_bench.Algorithms.max_sum_increasing_sequence Require Import max_sum_increasing_sequence_goal.
From SimpleC.EE.LLM_bench.Algorithms.max_sum_increasing_sequence Require Import max_sum_increasing_sequence_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.max_sum_increasing_sequence.max_sum_increasing_sequence_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.

Require Import AUXLib.MonotonicList.

Lemma msis_input_bounds : forall l k,
  Forall (Z.le 1) l -> Forall (Z.ge 10000) l ->
  0 <= k < Zlength l -> 1 <= Znth k l 0 <= 10000.
Proof.
  intros l k Hlo Hhi Hk.
  pose proof (proj1 (Forall_Znth _ 0 _) Hlo k Hk).
  pose proof (proj1 (Forall_Znth _ 0 _) Hhi k Hk). lia.
Qed.



Lemma proof_of_maxSumIncreasingSequence_safety_wit_6_split_goal_1 : maxSumIncreasingSequence_safety_wit_6_split_goal_1.
Proof.
  unfold maxSumIncreasingSequence_safety_wit_6_split_goal_1; intros.
  pose proof (PreH14 j ltac:(lia)) as Hj.
  pose proof (msis_input_bounds l i PreH16 PreH17 ltac:(lia)) as Hi.
  replace (j - 0) with j by lia. entailer!.
Qed.

Lemma proof_of_maxSumIncreasingSequence_safety_wit_6_split_goal_2 : maxSumIncreasingSequence_safety_wit_6_split_goal_2.
Proof.
  unfold maxSumIncreasingSequence_safety_wit_6_split_goal_2; intros.
  pose proof (PreH14 j ltac:(lia)) as Hj.
  pose proof (msis_input_bounds l i PreH16 PreH17 ltac:(lia)) as Hi.
  replace (j - 0) with j by lia. entailer!.
Qed.

Lemma proof_of_maxSumIncreasingSequence_safety_wit_6 : maxSumIncreasingSequence_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSumIncreasingSequence_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_maxSumIncreasingSequence_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_1 : maxSumIncreasingSequence_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hvalue0 : 1 <= Znth 0 l 0 <= 10000).
  { eapply msis_input_bounds; eauto; lia. }
  pose proof (msis_initial_semantics__initialization l ltac:(lia)) as [Hending0 Hprefix1].
  Exists (Znth 0 l 0 :: nil).
  split_pure_spatial.
  - sep_apply (IntArray.seg_single (&( "dp" )) 0 (Znth 0 l 0)).
    replace (0 + 1) with 1 by lia.
    entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + reflexivity.
    + intros k Hk. assert (k = 0) by lia; subst k; simpl; exact Hvalue0.
    + unfold MSISDPTablePrefix. intros k Hk. assert (k = 0) by lia; subst k; simpl; exact Hending0.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_2_split_goal_1 : maxSumIncreasingSequence_entail_wit_2_split_goal_1.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_2_split_goal_1; intros.
  assert (Hp : MSISDPTablePrefixFacts l d_2 i).
  { apply msis_table_facts; try lia; assumption. }
  pose proof (msis_inner_progress_zero__initialization l d_2 i Hp ltac:(lia) (msis_input_bounds l i PreH13 PreH14 ltac:(lia))) as Hnext.
  apply msis_inner_pure; exact Hnext.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_2_split_goal_2 : maxSumIncreasingSequence_entail_wit_2_split_goal_2.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_2_split_goal_2; intros.
  assert (Hp : MSISDPTablePrefixFacts l d_2 i).
  { apply msis_table_facts; try lia; assumption. }
  pose proof (msis_inner_progress_zero__initialization l d_2 i Hp ltac:(lia) (msis_input_bounds l i PreH13 PreH14 ltac:(lia))) as Hnext.
  apply (msis_inner_bounds _ _ _ _ Hnext); lia.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_2_split_goal_3 : maxSumIncreasingSequence_entail_wit_2_split_goal_3.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_2_split_goal_3; intros.
  assert (Hp : MSISDPTablePrefixFacts l d_2 i).
  { apply msis_table_facts; try lia; assumption. }
  pose proof (msis_inner_progress_zero__initialization l d_2 i Hp ltac:(lia) (msis_input_bounds l i PreH13 PreH14 ltac:(lia))) as Hnext.
  rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_2 : maxSumIncreasingSequence_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_3_1 : maxSumIncreasingSequence_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (j - 0) with j in * by lia.
  replace (i - 0) with i in * by lia.
  assert (Hp : MSISInnerProgressFacts l d_2 i j).
  { apply msis_inner_facts; try lia; assumption. }
  pose proof (replace_Znth_inner_progress_step__inner_transitions l d_2 i j Hp ltac:(lia) PreH2 ltac:(lia) (msis_input_bounds l i PreH17 PreH18 ltac:(lia))) as Hnext.
  Exists (replace_Znth i (Znth j d_2 0 + Znth i l 0) d_2).
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_seg (&( "dp" )) (i + 1) (replace_Znth i (Znth j d_2 0 + Znth i l 0) d_2)).
    entailer!.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + destruct Hnext as [_ [_ [Hlen _]]]. exact Hlen.
    + exact (msis_inner_bounds _ _ _ _ Hnext).
    + apply msis_inner_pure; exact Hnext.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_3_2_split_goal_1 : maxSumIncreasingSequence_entail_wit_3_2_split_goal_1.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_3_2_split_goal_1; intros.
  replace (j - 0) with j in * by lia.
  replace (i - 0) with i in * by lia.
  apply msis_inner_pure.
  eapply msis_inner_progress_skip_dominated__inner_transitions; try lia; try assumption.
  apply msis_inner_facts; try lia; assumption.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_3_2 : maxSumIncreasingSequence_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_3_3_split_goal_1 : maxSumIncreasingSequence_entail_wit_3_3_split_goal_1.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_3_3_split_goal_1; intros.
  replace (j - 0) with j in * by lia.
  replace (i - 0) with i in * by lia.
  apply msis_inner_pure.
  eapply msis_inner_progress_skip_nonincreasing__inner_transitions; try lia; try assumption.
  apply msis_inner_facts; try lia; assumption.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_3_3 : maxSumIncreasingSequence_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_3_3_split_goal_1.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_4_split_goal_1 : maxSumIncreasingSequence_entail_wit_4_split_goal_1.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_4_split_goal_1; intros.
  apply msis_table_pure.
  apply msis_inner_complete_dp_prefix__outer_transitions.
  assert (j = i) by lia; subst j.
  apply msis_inner_facts; try lia; assumption.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_4_split_goal_2 : maxSumIncreasingSequence_entail_wit_4_split_goal_2.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_4_split_goal_2; intros.
  apply PreH13; lia.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_4 : maxSumIncreasingSequence_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_1_split_goal_1 : maxSumIncreasingSequence_entail_wit_5_1_split_goal_1.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_5_1_split_goal_1; intros.
  replace (i - 0) with i in * by lia.
  assert (Hb : MSISBestSoFarFacts l i ans) by (split; [lia | exact PreH9]).
  pose proof (PreH12 i ltac:(lia)) as Hending.
  pose proof (msis_prefix_extend_by_ending__outer_transitions l i ans (Znth i d_2 0) Hb Hending) as Hnext.
  unfold MSISBestSoFarFacts in Hnext.
  rewrite Z.max_r in Hnext by lia.
  exact (proj2 Hnext).
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_1_split_goal_2 : maxSumIncreasingSequence_entail_wit_5_1_split_goal_2.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_5_1_split_goal_2; intros.
  apply PreH11; lia.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_1 : maxSumIncreasingSequence_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_5_1_split_goal_2.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_2_split_goal_1 : maxSumIncreasingSequence_entail_wit_5_2_split_goal_1.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_5_2_split_goal_1; intros.
  replace (i - 0) with i in * by lia.
  assert (Hb : MSISBestSoFarFacts l i ans) by (split; [lia | exact PreH9]).
  pose proof (PreH12 i ltac:(lia)) as Hending.
  pose proof (msis_prefix_extend_by_ending__outer_transitions l i ans (Znth i d_2 0) Hb Hending) as Hnext.
  unfold MSISBestSoFarFacts in Hnext.
  rewrite Z.max_l in Hnext by lia.
  exact (proj2 Hnext).
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_2_split_goal_2 : maxSumIncreasingSequence_entail_wit_5_2_split_goal_2.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_5_2_split_goal_2; intros.
  apply PreH11; lia.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_2 : maxSumIncreasingSequence_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_5_2_split_goal_2.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_6 : maxSumIncreasingSequence_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace i with numsSize_pre in * by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.seg_to_undef_seg (&( "dp" )) 0 (numsSize_pre) d).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "dp" )) 0 (numsSize_pre) 100000 ltac:(lia)).
    simpl. replace ((&( "dp" )) + 0) with (&( "dp" )) by lia.
    entailer!.
  - split_pures; dump_pre_spatial.
    unfold MSISMaximum; rewrite PreH4; exact PreH12.
Qed.