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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P035_807B_t_shirt_hunt_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P035_807B_t_shirt_hunt_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_lib.
Local Open Scope sac.

Lemma proof_of_wins_safety_wit_13_split_goal_1 : wins_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel.
  rewrite Z.rem_mod_nonneg by lia.
  dump_pre_spatial.
  pose proof (Z.mod_pos_bound (z * 96 + 42) 475 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_wins_safety_wit_13_split_goal_2 : wins_safety_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel.
  rewrite Z.rem_mod_nonneg by lia.
  dump_pre_spatial.
  pose proof (Z.mod_pos_bound (z * 96 + 42) 475 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_wins_safety_wit_13 : wins_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_wins_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_wins_safety_wit_13_split_goal_2.
Qed.

Lemma proof_of_wins_entail_wit_1_split_goal_1 : wins_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.rem_mod_nonneg by (try apply Z.div_pos; lia).
  destruct (shirt_trace_exists__wins_scan score_pre) as [values Htrace].
  unfold ShirtScanState.
  exists values.
  split; [exact Htrace |].
  split; [lia |].
  split.
  - destruct Htrace as [_ [Hseed _]].
    symmetry. exact Hseed.
  - intros j Hj. lia.
Qed.

Lemma proof_of_wins_entail_wit_1_split_goal_2 : wins_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.rem_mod_nonneg by (try apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound (score_pre / 50) 475 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_wins_entail_wit_1_split_goal_3 : wins_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.rem_mod_nonneg by (try apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound (score_pre / 50) 475 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_wins_entail_wit_1 : wins_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_wins_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_wins_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_wins_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_wins_entail_wit_2_split_goal_1 : wins_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg in PreH1 |- * by lia.
  eapply shirt_scan_state_step__wins_scan.
  - exact PreH2.
  - exact PreH11.
  - lia.
Qed.

Lemma proof_of_wins_entail_wit_2_split_goal_2 : wins_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound (z * 96 + 42) 475 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_wins_entail_wit_2_split_goal_3 : wins_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound (z * 96 + 42) 475 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_wins_entail_wit_2 : wins_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_wins_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_wins_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_wins_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_wins_return_wit_1_split_goal_1 : wins_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NoShirtSelection, ShirtSelection.
  intro Hselection.
  destruct Hselection as
    [values2 [Hlen2 [Hseed2 [Hstep2 [j [Hj Hplace]]]]]].
  assert (Htrace2 : ShirtTrace score_pre values2).
  {
    unfold ShirtTrace.
    repeat split; assumption.
  }
  destruct PreH10 as
    [values1 [Htrace1 [[Hscanlo Hscanhi] [Hz Hnomatch]]]].
  assert (i = 25) by lia.
  subst i.
  apply (Hnomatch j Hj).
  rewrite (shirt_trace_unique_prefix__wins_scan
    score_pre values1 values2 Htrace1 Htrace2 j ltac:(lia)).
  exact Hplace.
Qed.

Lemma proof_of_wins_return_wit_1 : wins_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_wins_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_wins_return_wit_2_split_goal_1 : wins_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  unfold ShirtSelection.
  destruct PreH11 as
    [values [Htrace [[Hscanlo Hscanhi] [Hz Hnomatch]]]].
  destruct Htrace as [Hlen [Hseed Hstep]].
  exists values.
  repeat split.
  - exact Hlen.
  - exact Hseed.
  - exact Hstep.
  - exists (i + 1).
    split; [lia |].
    rewrite Hstep by lia.
    rewrite <- Hz.
    lia.
Qed.

Lemma proof_of_wins_return_wit_2 : wins_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_wins_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold AlignmentSearch.
  split.
  - lia.
  - intros candidate Hcandidate.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply alignment_search_extend__alignment_search; eauto.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (alignment_search_full_window__alignment_search
       x_pre y_pre score PreH5 (conj PreH8 PreH9) PreH10 PreH1) as Hwindow.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply alignment_to_candidate_search__alignment_search; eauto.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply candidate_search_room__candidate_capacity; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply candidate_search_step__candidate_transitions; eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold CandidateSearch in PreH10.
  destruct PreH10 as [_ [Haligned _]].
  eapply (aligned_gap_at_least_fifty__candidate_transitions
            x_pre score (x_pre + 50 * 475)); eauto.
  replace (x_pre + 50 * 475 - x_pre) with (50 * 475) by ring.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold FirstWinningCandidate.
  split; assumption.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (zero_success_is_spec__final_result p_pre x_pre y_pre score);
    assumption.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply (first_winning_is_spec__final_result p_pre x_pre y_pre score).
  - lia.
  - exact PreH9.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.
