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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.longest_nondecreasing_subsequence.longest_nondecreasing_subsequence_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.


Ltac lnd_partition_range :=
  try rewrite Zlength_sublist by lia; lia.
Ltac lnd_partition_view :=
  repeat match goal with
  | H : UpperBoundPartition ?tails ?len ?x ?left ?right |- _ =>
      let HF := fresh "Hpartition" in
      pose proof (proj1 (UpperBoundPartition_indexed tails len x left right
        ltac:(lnd_partition_range) ltac:(lnd_partition_range)) H) as HF;
      clear H; rename HF into H
  end;
  try match goal with
  | |- UpperBoundPartition ?tails ?len ?x ?left ?right =>
      apply (proj2 (UpperBoundPartition_indexed tails len x left right
        ltac:(lnd_partition_range) ltac:(lnd_partition_range)))
  end.


































































Lemma proof_of_lengthOfLNDS_safety_wit_7_split_goal_1 : lengthOfLNDS_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (right - left) / 2) by (apply Z.div_pos; lia).
  assert ((right - left) / 2 <= right - left) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_lengthOfLNDS_safety_wit_7_split_goal_2 : lengthOfLNDS_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (right - left) / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_4_split_goal_1 : lengthOfLNDS_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  unfold UpperBoundPartitionIndexed.
  split; intros k Hk; lia.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_5_split_goal_1 : lengthOfLNDS_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  rewrite zdiv_equiv by lia.
  assert ((right - left) / 2 < right - left) by
    (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_5_split_goal_2 : lengthOfLNDS_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  rewrite zdiv_equiv by lia.
  assert (0 <= (right - left) / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_6_1_split_goal_1 : lengthOfLNDS_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  assert (Htailslen : Zlength (sublist 0 len tails_cur_2) = len).
  { rewrite Zlength_sublist0 by lia; reflexivity. }
  pose proof PreH16 as Hinc.
  eapply UpperBoundPartition_right_preserve__partition_search_steps;
    try eassumption; try lia.
  rewrite Znth_sublist0 by lia.
  exact PreH1.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_6_2_split_goal_1 : lengthOfLNDS_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  assert (Htailslen : Zlength (sublist 0 len tails_cur_2) = len).
  { rewrite Zlength_sublist0 by lia; reflexivity. }
  pose proof PreH16 as Hinc.
  eapply UpperBoundPartition_left_preserve__partition_search_steps;
    try eassumption; try lia.
  rewrite Znth_sublist0 by lia.
  exact PreH1.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_1_split_goal_1 : lengthOfLNDS_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
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
  all: lnd_partition_view.
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
  all: lnd_partition_view.
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
  all: lnd_partition_view.
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
  all: lnd_partition_view.
  subst left.
  pose proof (LNDTailsPublic_append_update__append_transition
    numsSize_pre l tails_old i len x len PreH4 PreH5
    ltac:(lia) ltac:(lia) PreH10 ltac:(reflexivity)
    PreH14 PreH15 PreH16 PreH17 PreH18)
    as Hupdate.
  cbv zeta in Hupdate.
  exact (proj1 Hupdate).
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_1 : lengthOfLNDS_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  pose proof (LNDTailsPublic_replace_update__replace_transition
    l tails_old i len x left numsSize_pre PreH5 ltac:(lia) PreH10
    ltac:(lia) ltac:(lia) ltac:(lia) PreH14 PreH15 PreH16 PreH17 PreH18) as Hnew.
  destruct Hnew as [_ [_ [_ Hmin]]].
  exact Hmin.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_2 : lengthOfLNDS_entail_wit_8_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  pose proof (LNDTailsPublic_replace_update__replace_transition
    l tails_old i len x left numsSize_pre PreH5 ltac:(lia) PreH10
    ltac:(lia) ltac:(lia) ltac:(lia) PreH14 PreH15 PreH16 PreH17 PreH18) as Hnew.
  destruct Hnew as [_ [_ [Hopt _]]].
  exact Hopt.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_3 : lengthOfLNDS_entail_wit_8_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  pose proof (LNDTailsPublic_replace_update__replace_transition
    l tails_old i len x left numsSize_pre PreH5 ltac:(lia) PreH10
    ltac:(lia) ltac:(lia) ltac:(lia) PreH14 PreH15 PreH16 PreH17 PreH18) as Hnew.
  destruct Hnew as [_ [Hreal _]].
  exact Hreal.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_4 : lengthOfLNDS_entail_wit_8_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  pose proof (LNDTailsPublic_replace_update__replace_transition
    l tails_old i len x left numsSize_pre PreH5 ltac:(lia) PreH10
    ltac:(lia) ltac:(lia) ltac:(lia) PreH14 PreH15 PreH16 PreH17 PreH18) as Hnew.
  exact (proj1 Hnew).
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_5 : lengthOfLNDS_entail_wit_8_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  rewrite Zlength_app, Zlength_sublist0, Zlength_cons, Zlength_sublist by lia.
  lia.
Qed.

Lemma proof_of_lengthOfLNDS_safety_wit_7 : lengthOfLNDS_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_lengthOfLNDS_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_1 : lengthOfLNDS_entail_wit_1.
Proof.
  aggressive_pre_process. reflexivity.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_2 : lengthOfLNDS_entail_wit_2.
Proof.
  aggressive_pre_process. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_3 : lengthOfLNDS_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace fill with numsSize_pre in * by lia.
  Exists initialized.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.seg_to_full (&( "tails" )) 0 numsSize_pre initialized).
    replace ((&( "tails" )) + 0 * sizeof(INT)) with (&( "tails" )) by lia.
    replace (numsSize_pre - 0) with numsSize_pre by lia. entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: first
      [ solve [unfold LNDTailsRepresentation, sublist; simpl; auto]
      | solve [unfold LNDTailsRealizability; intros k Hk; lia]
      | solve [apply LNDSLengthPrefix_empty]
      | solve [unfold LNDTailsMinimality; intros k Hk; lia] ].
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_4 : lengthOfLNDS_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLNDS_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_5 : lengthOfLNDS_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_6_1 : lengthOfLNDS_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_6_1_split_goal_1.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_6_2 : lengthOfLNDS_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_6_2_split_goal_1.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_7 : lengthOfLNDS_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: lnd_partition_view.
  assert (Heq : right = left) by lia.
  subst right.
  assert (Hupdate :
    replace_Znth left x tails_cur =
      sublist 0 left tails_cur ++
      x :: sublist (left + 1) numsSize_pre tails_cur).
  { rewrite <- PreH5.
    apply (replace_Znth_sublist Z 0); lia. }
  rewrite Hupdate.
  Exists tails_cur.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre numsSize_pre l).
    cancel (IntArray.full (&( "tails" )) numsSize_pre
      (sublist 0 left tails_cur ++
       x :: sublist (left + 1) numsSize_pre tails_cur)).
    all: entailer!.
  - split_pures; dump_pre_spatial; try lia; auto.
    all: lnd_partition_view; assumption.
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

Lemma proof_of_lengthOfLNDS_entail_wit_8_2 : lengthOfLNDS_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_1.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_2.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_3.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_4.
  - Goal_apply proof_of_lengthOfLNDS_entail_wit_8_2_split_goal_5.
Qed.

Lemma proof_of_lengthOfLNDS_entail_wit_10 : lengthOfLNDS_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_undef_full (&( "tails" )) numsSize_pre tails_cur).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "tails" )) numsSize_pre).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "tails" )) 0 numsSize_pre 100000 ltac:(lia)).
    simpl. replace ((&( "tails" )) + 0) with (&( "tails" )) by lia. entailer!.
  - dump_pre_spatial.
    unfold LNDSLength, LNDSOptimalLength in *.
    replace (Zlength l) with i by lia. exact PreH12.
Qed.
