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
From SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence Require Import longest_increasing_subsequence_goal.
From SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence Require Import longest_increasing_subsequence_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence.longest_increasing_subsequence_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.




Lemma proof_of_lengthOfLIS_entail_wit_1_split_goal_1 : lengthOfLIS_entail_wit_1_split_goal_1.
Proof.
  unfold lengthOfLIS_entail_wit_1_split_goal_1; intros.
  unfold LISBestSoFar; left; auto.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_1_split_goal_2 : lengthOfLIS_entail_wit_1_split_goal_2.
Proof.
  unfold lengthOfLIS_entail_wit_1_split_goal_2; intros.
  unfold LISDPTablePrefix; intros; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_1_split_goal_3 : lengthOfLIS_entail_wit_1_split_goal_3.
Proof.
  unfold lengthOfLIS_entail_wit_1_split_goal_3; intros.
  lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_1_split_goal_4 : lengthOfLIS_entail_wit_1_split_goal_4.
Proof.
  unfold lengthOfLIS_entail_wit_1_split_goal_4; intros.
  reflexivity.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_1 : lengthOfLIS_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_1_split_goal_4.

Qed.

Lemma proof_of_lengthOfLIS_entail_wit_2_split_goal_1 : lengthOfLIS_entail_wit_2_split_goal_1.
Proof.
  unfold lengthOfLIS_entail_wit_2_split_goal_1; intros.
  assert (Hp : LISDPTablePrefixFacts l d_2 i).
  { apply lis_table_facts; try lia; assumption. }
  pose proof (lis_inner_progress_init__inner_foundations l d_2 i Hp ltac:(lia)) as Hnext.
  apply lis_inner_pure; exact Hnext.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_2_split_goal_2 : lengthOfLIS_entail_wit_2_split_goal_2.
Proof.
  unfold lengthOfLIS_entail_wit_2_split_goal_2; intros.
  assert (Hp : LISDPTablePrefixFacts l d_2 i).
  { apply lis_table_facts; try lia; assumption. }
  pose proof (lis_inner_progress_init__inner_foundations l d_2 i Hp ltac:(lia)) as Hnext.
  apply (lis_inner_bounds _ _ _ _ Hnext); lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_2_split_goal_3 : lengthOfLIS_entail_wit_2_split_goal_3.
Proof.
  unfold lengthOfLIS_entail_wit_2_split_goal_3; intros.
  assert (Hp : LISDPTablePrefixFacts l d_2 i).
  { apply lis_table_facts; try lia; assumption. }
  pose proof (lis_inner_progress_init__inner_foundations l d_2 i Hp ltac:(lia)) as Hnext.
  rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_2 : lengthOfLIS_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_2_split_goal_3.

Qed.

Lemma proof_of_lengthOfLIS_entail_wit_3_1 : lengthOfLIS_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (j - 0) with j in * by lia.
  replace (i - 0) with i in * by lia.
  assert (Hp : LISInnerProgressFacts l d_2 i j).
  { apply lis_inner_facts; try lia; assumption. }
  pose proof (lis_inner_progress_take_candidate__inner_transitions l d_2 i j Hp ltac:(lia) PreH2 ltac:(lia)) as Hnext.
  Exists (replace_Znth i (Znth j d_2 0 + 1) d_2).
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_seg (&( "dp" )) (i + 1) (replace_Znth i (Znth j d_2 0 + 1) d_2)).
    entailer!.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + destruct Hnext as [_ [_ [Hlen _]]]. exact Hlen.
    + exact (lis_inner_bounds _ _ _ _ Hnext).
    + apply lis_inner_pure; exact Hnext.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_3_2_split_goal_1 : lengthOfLIS_entail_wit_3_2_split_goal_1.
Proof.
  unfold lengthOfLIS_entail_wit_3_2_split_goal_1; intros.
  replace (j - 0) with j in * by lia.
  replace (i - 0) with i in * by lia.
  apply lis_inner_pure.
  eapply lis_inner_progress_skip_dominated__inner_transitions; try lia; try assumption.
  apply lis_inner_facts; try lia; assumption.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_3_2 : lengthOfLIS_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLIS_entail_wit_3_2_split_goal_1.

Qed.

Lemma proof_of_lengthOfLIS_entail_wit_3_3_split_goal_1 : lengthOfLIS_entail_wit_3_3_split_goal_1.
Proof.
  unfold lengthOfLIS_entail_wit_3_3_split_goal_1; intros.
  replace (j - 0) with j in * by lia.
  replace (i - 0) with i in * by lia.
  apply lis_inner_pure.
  eapply lis_inner_progress_skip_nonincreasing__inner_transitions; try lia; try assumption.
  apply lis_inner_facts; try lia; assumption.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_3_3 : lengthOfLIS_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLIS_entail_wit_3_3_split_goal_1.

Qed.

Lemma proof_of_lengthOfLIS_entail_wit_4_split_goal_1 : lengthOfLIS_entail_wit_4_split_goal_1.
Proof.
  unfold lengthOfLIS_entail_wit_4_split_goal_1; intros.
  apply lis_table_pure.
  apply lis_inner_progress_complete__inner_transitions.
  assert (j = i) by lia; subst j.
  apply lis_inner_facts; try lia; assumption.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_4_split_goal_2 : lengthOfLIS_entail_wit_4_split_goal_2.
Proof.
  unfold lengthOfLIS_entail_wit_4_split_goal_2; intros.
  apply PreH13; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_4 : lengthOfLIS_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_4_split_goal_2.

Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_1_split_goal_1 : lengthOfLIS_entail_wit_5_1_split_goal_1.
Proof.
  unfold lengthOfLIS_entail_wit_5_1_split_goal_1; intros.
  replace (i - 0) with i in * by lia.
  pose proof (PreH11 i ltac:(lia)) as Hbounds.
  pose proof (PreH12 i ltac:(lia)) as Hending.
  unfold LISBestSoFar in PreH9.
  destruct PreH9 as [[Hzero Hans] | [Hpositive Hprefix]].
  - exfalso; lia.
  - assert (Hnext : LISBestSoFarFacts l (i + 1) (Z.max ans (Znth i d_2 0))).
    { eapply lis_best_so_far_step__outer_best_update; eauto; lia. }
    unfold LISBestSoFarFacts in Hnext.
    unfold LISBestSoFar. replace (Znth i d_2 0) with (Z.max ans (Znth i d_2 0)) by lia.
    exact (proj2 Hnext).
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_1_split_goal_2 : lengthOfLIS_entail_wit_5_1_split_goal_2.
Proof.
  unfold lengthOfLIS_entail_wit_5_1_split_goal_2; intros.
  apply PreH11; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_1 : lengthOfLIS_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_5_1_split_goal_2.

Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_2_split_goal_1 : lengthOfLIS_entail_wit_5_2_split_goal_1.
Proof.
  unfold lengthOfLIS_entail_wit_5_2_split_goal_1; intros.
  replace (i - 0) with i in * by lia.
  pose proof (PreH11 i ltac:(lia)) as Hbounds.
  pose proof (PreH12 i ltac:(lia)) as Hending.
  unfold LISBestSoFar in PreH9.
  destruct PreH9 as [[Hzero Hans] | [Hpositive Hprefix]].
  - subst i ans.
    assert (Hcur : Znth 0 d_2 0 = 1) by lia.
    rewrite Hcur in Hending.
    pose proof (lis_best_so_far_step__outer_best_update l 0 0 1 ltac:(lia) (lis_prefix_empty__outer_best_update l) Hending) as Hnext.
    exact (proj2 Hnext).
  - assert (Hnext : LISBestSoFarFacts l (i + 1) (Z.max ans (Znth i d_2 0))).
    { eapply lis_best_so_far_step__outer_best_update; eauto; lia. }
    unfold LISBestSoFarFacts in Hnext.
    unfold LISBestSoFar. replace ans with (Z.max ans (Znth i d_2 0)) by lia.
    exact (proj2 Hnext).
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_2_split_goal_2 : lengthOfLIS_entail_wit_5_2_split_goal_2.
Proof.
  unfold lengthOfLIS_entail_wit_5_2_split_goal_2; intros.
  apply PreH11; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_2 : lengthOfLIS_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_lengthOfLIS_entail_wit_5_2_split_goal_2.

Qed.

Lemma proof_of_lengthOfLIS_entail_wit_6 : lengthOfLIS_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace i with numsSize_pre in * by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.seg_to_undef_seg (&( "dp" )) 0 (numsSize_pre) d).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "dp" )) 0 (numsSize_pre) 100000 ltac:(lia)).
    simpl. replace ((&( "dp" )) + 0) with (&( "dp" )) by lia.
    entailer!.
  - split_pures; dump_pre_spatial.
    unfold LISBestSoFar in PreH12.
    destruct PreH12 as [[Hz _] | [_ Hp]]; [lia |].
    unfold LISLength; rewrite PreH4; exact Hp.
Qed.