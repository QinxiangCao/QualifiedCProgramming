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
From SimpleC.EE.LLM_bench.Algorithms.longest_nondecreasing_subsequence Require Import longest_nondecreasing_subsequence_goal.
From SimpleC.EE.LLM_bench.Algorithms.longest_nondecreasing_subsequence Require Import longest_nondecreasing_subsequence_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.longest_nondecreasing_subsequence.longest_nondecreasing_subsequence_lib.
Local Open Scope sac.

Lemma proof_of_lengthOfLNDS_safety_wit_4_split_goal_1 : lengthOfLNDS_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (right - left) / 2) by (apply Z.div_pos; lia).
  assert ((right - left) / 2 <= right - left) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_lengthOfLNDS_safety_wit_4_split_goal_2 : lengthOfLNDS_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (right - left) / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_lengthOfLNDS_safety_wit_4 : lengthOfLNDS_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_lengthOfLNDS_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_1_split_goal_1 : lengthOfLNDS_entail_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold LNDTailsMinimality.
  intros idxs k v _ _ Hk _; lia.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_1_split_goal_2 : lengthOfLNDS_entail_wit_1_split_goal_2.
Proof.
  aggressive_pre_process.
  apply LNDSLengthPrefix_empty.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_1_split_goal_3 : lengthOfLNDS_entail_wit_1_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold LNDTailsRealizability.
  intros k Hk; lia.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_1_split_goal_4 : lengthOfLNDS_entail_wit_1_split_goal_4.
Proof.
  aggressive_pre_process.
  unfold LNDTailsRepresentation, sublist; simpl; auto.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_1 : lengthOfLNDS_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_3_split_goal_1 : lengthOfLNDS_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold UpperBoundPartition.
  split; intros k Hk; lia.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_3 : lengthOfLNDS_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLNDS_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_4_split_goal_1 : lengthOfLNDS_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  assert ((right - left) / 2 < right - left) by
    (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_4_split_goal_2 : lengthOfLNDS_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  assert (0 <= (right - left) / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_4 : lengthOfLNDS_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_5_1_split_goal_1 : lengthOfLNDS_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold LNDTailsRepresentation in PreH16.
  destruct PreH16 as [Htailslen Hinc].
  eapply UpperBoundPartition_right_preserve__partition_search_steps;
    try eassumption; try lia.
  rewrite Znth_sublist0 by lia.
  exact PreH1.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_5_1 : lengthOfLNDS_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_5_1_split_goal_1.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_5_2_split_goal_1 : lengthOfLNDS_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold LNDTailsRepresentation in PreH16.
  destruct PreH16 as [Htailslen Hinc].
  eapply UpperBoundPartition_left_preserve__partition_search_steps;
    try eassumption; try lia.
  rewrite Znth_sublist0 by lia.
  exact PreH1.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_5_2 : lengthOfLNDS_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_5_2_split_goal_1.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_6_split_goal_1 : lengthOfLNDS_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace right with left in PreH18 by lia.
  exact PreH18.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_6 : lengthOfLNDS_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLNDS_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_7 : lengthOfLNDS_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hupdate :
    replace_Znth left x tails_cur =
      sublist 0 left tails_cur ++
      x :: sublist (left + 1) numsSize_pre tails_cur).
  { rewrite <- PreH4.
    apply (replace_Znth_sublist Z 0); lia. }
  rewrite Hupdate.
  Exists tails_cur.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre numsSize_pre l).
    cancel (IntArray.full tails_pre numsSize_pre
      (sublist 0 left tails_cur ++
       x :: sublist (left + 1) numsSize_pre tails_cur)).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_1_split_goal_1 : lengthOfLNDS_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst left.
  pose proof (LNDTailsPublic_append_update__append_transition
    numsSize_pre l tails_old i len x len PreH4 PreH5
    ltac:(lia) ltac:(lia) PreH10 ltac:(reflexivity)
    PreH14 PreH15 PreH16 PreH17 PreH18)
    as Hupdate.
  cbv zeta in Hupdate.
  destruct Hupdate as [_ [Hmin _]].
  exact Hmin.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_1_split_goal_2 : lengthOfLNDS_entail_wit_8_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst left.
  pose proof (LNDTailsPublic_append_update__append_transition
    numsSize_pre l tails_old i len x len PreH4 PreH5
    ltac:(lia) ltac:(lia) PreH10 ltac:(reflexivity)
    PreH14 PreH15 PreH16 PreH17 PreH18)
    as Hupdate.
  cbv zeta in Hupdate.
  destruct Hupdate as [_ [_ [Hopt _]]].
  exact Hopt.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_1_split_goal_3 : lengthOfLNDS_entail_wit_8_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst left.
  pose proof (LNDTailsPublic_append_update__append_transition
    numsSize_pre l tails_old i len x len PreH4 PreH5
    ltac:(lia) ltac:(lia) PreH10 ltac:(reflexivity)
    PreH14 PreH15 PreH16 PreH17 PreH18)
    as Hupdate.
  cbv zeta in Hupdate.
  destruct Hupdate as [_ [_ [_ [Hreal _]]]].
  exact Hreal.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_1_split_goal_4 : lengthOfLNDS_entail_wit_8_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst left.
  pose proof (LNDTailsPublic_append_update__append_transition
    numsSize_pre l tails_old i len x len PreH4 PreH5
    ltac:(lia) ltac:(lia) PreH10 ltac:(reflexivity)
    PreH14 PreH15 PreH16 PreH17 PreH18)
    as Hupdate.
  cbv zeta in Hupdate.
  destruct Hupdate as [_ [_ [_ [_ Hrep]]]].
  exact Hrep.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_1_split_goal_5 : lengthOfLNDS_entail_wit_8_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst left.
  pose proof (LNDTailsPublic_append_update__append_transition
    numsSize_pre l tails_old i len x len PreH4 PreH5
    ltac:(lia) ltac:(lia) PreH10 ltac:(reflexivity)
    PreH14 PreH15 PreH16 PreH17 PreH18)
    as Hupdate.
  cbv zeta in Hupdate.
  exact (proj1 Hupdate).
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_1 : lengthOfLNDS_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_1_split_goal_1.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_1_split_goal_2.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_1_split_goal_3.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_1_split_goal_4.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_1_split_goal_5.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_1 : lengthOfLNDS_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (LNDTailsPublic_replace_update__replace_transition
    l tails_old i len x left numsSize_pre PreH5 ltac:(lia) PreH10
    ltac:(lia) ltac:(lia) ltac:(lia) PreH14 PreH15 PreH16 PreH17 PreH18) as Hnew.
  destruct Hnew as [_ [_ [_ Hmin]]].
  exact Hmin.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_2 : lengthOfLNDS_entail_wit_8_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (LNDTailsPublic_replace_update__replace_transition
    l tails_old i len x left numsSize_pre PreH5 ltac:(lia) PreH10
    ltac:(lia) ltac:(lia) ltac:(lia) PreH14 PreH15 PreH16 PreH17 PreH18) as Hnew.
  destruct Hnew as [_ [_ [Hopt _]]].
  exact Hopt.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_3 : lengthOfLNDS_entail_wit_8_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (LNDTailsPublic_replace_update__replace_transition
    l tails_old i len x left numsSize_pre PreH5 ltac:(lia) PreH10
    ltac:(lia) ltac:(lia) ltac:(lia) PreH14 PreH15 PreH16 PreH17 PreH18) as Hnew.
  destruct Hnew as [_ [Hreal _]].
  exact Hreal.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_4 : lengthOfLNDS_entail_wit_8_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (LNDTailsPublic_replace_update__replace_transition
    l tails_old i len x left numsSize_pre PreH5 ltac:(lia) PreH10
    ltac:(lia) ltac:(lia) ltac:(lia) PreH14 PreH15 PreH16 PreH17 PreH18) as Hnew.
  exact (proj1 Hnew).
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_5 : lengthOfLNDS_entail_wit_8_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_sublist0, Zlength_cons, Zlength_sublist by lia.
  lia.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_2 : lengthOfLNDS_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_1.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_2.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_3.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_4.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_5.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_10_split_goal_1 : lengthOfLNDS_entail_wit_10_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold LNDSLength, LNDSOptimalLength in *.
  replace (Zlength l) with i by lia.
  exact PreH12.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_10 : lengthOfLNDS_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_10_split_goal_1.
Qed.
