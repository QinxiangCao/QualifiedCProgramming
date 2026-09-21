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
From SimpleC.EE.LLM_bench.Algorithms.minimal_representation Require Import minimal_representation_goal.

Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.









































































Lemma proof_of_minimal_representation_entail_wit_1_split_goal_spatial : minimal_representation_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&("b")) (2 * n_pre) 2000).
  { dump_pre_spatial; lia. }
  sep_apply_l_atomic (IntArray.undef_seg_to_undef_full (&("b")) 0 (2 * n_pre)).
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r.
  replace (2 * n_pre - 0) with (2 * n_pre) by lia.
  cancel (IntArray.undef_seg (&("b")) (2 * n_pre) 2000).
  change (sublist 0 0 l) with (@nil Z).
  replace (n_pre + 0) with n_pre by lia.
  sep_apply_l_atomic
    (IntArray.undef_full_split_to_undef_seg (&("b")) n_pre (2 * n_pre)).
  - dump_pre_spatial.
    lia.
  - rewrite (IntArray.seg_empty (&("b")) n_pre n_pre).
    split_pure_spatial.
    + cancel (IntArray.undef_seg (&("b")) 0 n_pre).
      cancel (IntArray.undef_seg (&("b")) n_pre (2 * n_pre)).
    + dump_pre_spatial.
      lia.
Qed.

Lemma proof_of_minimal_representation_entail_wit_1_split_goal_1 : minimal_representation_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_minimal_representation_entail_wit_1 : minimal_representation_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_minimal_representation_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_minimal_representation_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_2_split_goal_spatial : minimal_representation_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (sublist 0 (p + 1) l)
    with (sublist 0 p l ++ Znth p l 0 :: nil).
  2: {
    rewrite (sublist_split 0 (p + 1) p l) by lia.
    rewrite (sublist_single 0 p l) by lia.
    reflexivity.
  }
  replace (n_pre + (p + 1)) with ((n_pre + p) + 1) by lia.
  cancel (IntArray.seg (&("b")) n_pre ((n_pre + p) + 1)
    (sublist 0 p l ++ Znth p l 0 :: nil)).
Qed.

Lemma proof_of_minimal_representation_entail_wit_2_split_goal_1 : minimal_representation_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (sublist 0 (p + 1) l)
    with (sublist 0 p l ++ Znth p l 0 :: nil).
  2: {
    rewrite (sublist_split 0 (p + 1) p l) by lia.
    rewrite (sublist_single 0 p l) by lia.
    reflexivity.
  }
  dump_pre_spatial.
  reflexivity.
Qed.

Lemma proof_of_minimal_representation_entail_wit_2 : minimal_representation_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_minimal_representation_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_minimal_representation_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_3 : minimal_representation_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hp : p = n_pre) by lia. subst p.
  rewrite (sublist_self l n_pre) by exact (eq_sym PreH4).
  replace (n_pre + n_pre) with (2 * n_pre) by lia.
  pose proof (MRCandidateState_initial__candidate_boundaries
    l best ltac:(lia) PreH9) as Hstate.
  Left.
  sep_apply_l_atomic
    (IntArray.seg_merge_to_full (&("b")) 0 n_pre (2 * n_pre) l l).
  - dump_pre_spatial; lia.
  - replace ((&("b")) + 0 * sizeof (INT)) with (&("b")) by lia.
    replace (2 * n_pre - 0) with (2 * n_pre) by lia.
    repeat rewrite IntArray.undef_seg_empty.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; try lia; assumption.
Qed.

Lemma proof_of_minimal_representation_entail_wit_4_1_split_goal_1 : minimal_representation_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MRRotationPrefixEq.
  intros offset Hoffset.
  lia.
Qed.

Lemma proof_of_minimal_representation_entail_wit_4_1 : minimal_representation_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_minimal_representation_entail_wit_4_1_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_4_2_split_goal_1 : minimal_representation_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MRRotationPrefixEq.
  intros offset Hoffset.
  lia.
Qed.

Lemma proof_of_minimal_representation_entail_wit_4_2 : minimal_representation_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_minimal_representation_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_5_split_goal_1 : minimal_representation_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MRRotationPrefixEq, MRRotationValue in *.
  intros offset Hoffset.
  destruct (Z.lt_trichotomy offset k) as [Hlt | [Heq | Hgt]].
  - apply PreH17.
    lia.
  - subst offset.
    exact PreH1.
  - lia.
Qed.

Lemma proof_of_minimal_representation_entail_wit_5 : minimal_representation_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_minimal_representation_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_6_1 : minimal_representation_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hstate : MRCandidateState l best (i + k + 2) j).
  {
    pose proof
      (MRCandidateState_advance_left__candidate_transitions
         l best i j k PreH18
         ltac:(unfold MRValidStart; lia)
         ltac:(unfold MRValidStart; lia)
         ltac:(lia) PreH20 ltac:(unfold MRRotationValue; lia) PreH19)
      as [Hcollision Hnoncollision].
    apply Hcollision.
    lia.
  }
  Right.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
    cancel (IntArray.full (&("b")) (2 * n_pre) (l ++ l)).
    cancel (IntArray.undef_full out_pre n_pre). try cancel.
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
    replace (i + k + 1 + 1) with (i + k + 2) by lia.
    exact Hstate.
Qed.

Lemma proof_of_minimal_representation_entail_wit_6_2 : minimal_representation_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hstate : MRCandidateState l best (i + k + 1) j).
  {
    pose proof
      (MRCandidateState_advance_left__candidate_transitions
         l best i j k PreH18
         ltac:(unfold MRValidStart; lia)
         ltac:(unfold MRValidStart; lia)
         ltac:(lia) PreH20 ltac:(unfold MRRotationValue; lia) PreH19)
      as [Hcollision Hnoncollision].
    apply Hnoncollision.
    exact PreH1.
  }
  Right.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
    cancel (IntArray.full (&("b")) (2 * n_pre) (l ++ l)).
    cancel (IntArray.undef_full out_pre n_pre). try cancel.
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.

Lemma proof_of_minimal_representation_entail_wit_6_3 : minimal_representation_entail_wit_6_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hstate : MRCandidateState l best i (j + k + 2)).
  {
    pose proof
      (MRCandidateState_advance_right__candidate_transitions
         l best i j k PreH18
         ltac:(unfold MRValidStart; lia)
         ltac:(unfold MRValidStart; lia)
         ltac:(lia) PreH20 ltac:(unfold MRRotationValue; lia) PreH19)
      as [Hcollision Hnoncollision].
    apply Hcollision.
    lia.
  }
  Left.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
    cancel (IntArray.full (&("b")) (2 * n_pre) (l ++ l)).
    cancel (IntArray.undef_full out_pre n_pre). try cancel.
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
    replace (j + k + 1 + 1) with (j + k + 2) by lia.
    exact Hstate.
Qed.

Lemma proof_of_minimal_representation_entail_wit_6_4 : minimal_representation_entail_wit_6_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hstate : MRCandidateState l best i (j + k + 1)).
  {
    pose proof
      (MRCandidateState_advance_right__candidate_transitions
         l best i j k PreH18
         ltac:(unfold MRValidStart; lia)
         ltac:(unfold MRValidStart; lia)
         ltac:(lia) PreH20 ltac:(unfold MRRotationValue; lia) PreH19)
      as [Hcollision Hnoncollision].
    apply Hnoncollision.
    lia.
  }
  Left.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
    cancel (IntArray.full (&("b")) (2 * n_pre) (l ++ l)).
    cancel (IntArray.undef_full out_pre n_pre). try cancel.
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.

Lemma proof_of_minimal_representation_entail_wit_7_1_split_goal_1 : minimal_representation_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MRCandidateState in PreH16.
  destruct PreH16 as [Hbest | [Hbest | [Hfrontier _]]]; lia.
Qed.

Lemma proof_of_minimal_representation_entail_wit_7_1 : minimal_representation_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_minimal_representation_entail_wit_7_1_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_7_2_split_goal_1 : minimal_representation_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MRCandidateState in PreH17.
  destruct PreH17 as [Hbest | [Hbest | [Hfrontier _]]]; lia.
Qed.

Lemma proof_of_minimal_representation_entail_wit_7_2 : minimal_representation_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_minimal_representation_entail_wit_7_2_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_7_3 : minimal_representation_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hvalidi : MRValidStart l i).
  { unfold MRValidStart. rewrite PreH5. lia. }
  assert (Hvalidj : MRValidStart l j).
  { unfold MRValidStart. rewrite PreH5. lia. }
  assert (Heq : MRRotationEq l i j).
  { unfold MRRotationEq. rewrite PreH5. rewrite <- PreH1. exact PreH17. }
  pose proof (MRCandidateState_equal_exit__candidate_boundaries
    l best i j Hvalidi Hvalidj PreH12 PreH15 PreH16 Heq)
    as [Hlt Hge].
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; assumption.
Qed.

Lemma proof_of_minimal_representation_entail_wit_8_1_split_goal_1 : minimal_representation_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_minimal_representation_entail_wit_8_1 : minimal_representation_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_minimal_representation_entail_wit_8_1_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_8_2_split_goal_1 : minimal_representation_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_minimal_representation_entail_wit_8_2 : minimal_representation_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_minimal_representation_entail_wit_8_2_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_8_3_split_goal_1 : minimal_representation_entail_wit_8_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_minimal_representation_entail_wit_8_3 : minimal_representation_entail_wit_8_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_minimal_representation_entail_wit_8_3_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_8_4_split_goal_1 : minimal_representation_entail_wit_8_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_minimal_representation_entail_wit_8_4 : minimal_representation_entail_wit_8_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_minimal_representation_entail_wit_8_4_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_9_split_goal_1 : minimal_representation_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hstart : MRValidStart l best) by
    (unfold MRValidStart; lia).
  assert (Hk : 0 <= k < Zlength l) by lia.
  pose proof
    (MRRotation_Znth__output_finalization l best k Hstart Hk) as HZnth.
  rewrite <- HZnth.
  rewrite (sublist_split 0 (k + 1) k (MRRotation l best)) by
    (try rewrite (MRRotation_Zlength__output_finalization l best Hstart); lia).
  rewrite (sublist_single 0 k (MRRotation l best)) by
    (rewrite (MRRotation_Zlength__output_finalization l best Hstart); lia).
  reflexivity.
Qed.

Lemma proof_of_minimal_representation_entail_wit_9 : minimal_representation_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_minimal_representation_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_minimal_representation_entail_wit_10 : minimal_representation_entail_wit_10.
Proof.
  unfold minimal_representation_entail_wit_10. right. intros.
  assert (Hstart : MRValidStart l best) by (unfold MRValidStart; lia).
  assert (Hk : k = n_pre) by lia. subst k.
  rewrite (sublist_self (MRRotation l best) n_pre) by
    (rewrite (MRRotation_Zlength__output_finalization l best Hstart); lia).
  sep_apply (IntArray.seg_to_full out_pre 0 n_pre (MRRotation l best)).
  sep_apply (IntArray.full_to_undef_full (&("b")) (2 * n_pre) (l ++ l)).
  sep_apply (IntArray.undef_full_to_undef_seg (&("b")) (2 * n_pre)).
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&("b")) 0 (2 * n_pre) 2000); try lia.
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r.
  repeat rewrite Z.sub_0_r. entailer!.
Qed.
