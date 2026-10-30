From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P017_887A_div_64_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P017_887A_div_64_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P017_887A_div_64_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixScan, sublist.
  simpl.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (terminator_nonzero_index__prefix_scan_transitions
       text i (conj PreH5 PreH6) PreH12) as [Hi Hread].
  assert (Hchar : Znth i text 0 = 49).
  { rewrite <- Hread. exact PreH1. }
  eapply prefix_scan_append_one__prefix_scan_transitions; eauto.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (terminator_nonzero_index__prefix_scan_transitions
       text i (conj PreH5 PreH6) PreH12) as [Hi Hread].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (terminator_nonzero_index__prefix_scan_transitions
       text i (conj PreH5 PreH6) PreH12) as [Hi Hread].
  assert (Hchar : Znth i text 0 = 48).
  {
    destruct (PreH4 i (conj PreH5 Hi)) as [H48 | H49].
    - exact H48.
    - exfalso. apply PreH1. rewrite Hread. exact H49.
  }
  assert (seen_one = 1) by lia.
  subst seen_one.
  eapply prefix_scan_append_zero_seen__prefix_scan_transitions; eauto.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (terminator_nonzero_index__prefix_scan_transitions
       text i (conj PreH5 PreH6) PreH12) as [Hi Hread].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (terminator_nonzero_index__prefix_scan_transitions
       text i (conj PreH5 PreH6) PreH12) as [Hi Hread].
  assert (Hchar : Znth i text 0 = 48).
  {
    destruct (PreH4 i (conj PreH5 Hi)) as [H48 | H49].
    - exact H48.
    - exfalso. apply PreH1. rewrite Hread. exact H49.
  }
  subst seen_one.
  eapply prefix_scan_append_zero_unseen__prefix_scan_transitions; eauto.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (terminator_nonzero_index__prefix_scan_transitions
       text i (conj PreH5 PreH6) PreH12) as [Hi Hread].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec. split.
  - left. reflexivity.
  - split.
    + intros Hcontra. lia.
    + intros (indices & digits & Hchosen & Hpositive & Hdivisible).
      destruct (terminator_full_prefix__final_spec
        text i ltac:(lia) PreH4 PreH12) as [Hi Hprefix].
      subst i. rewrite Hprefix in PreH11.
      pose proof (chosen_divisible64_forces_six_source_zeros__final_spec
        text indices digits seen_one zeros PreH4 Hchosen
        Hpositive Hdivisible PreH11) as Hsix.
      lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec. split.
  - right. reflexivity.
  - split.
    + intros _.
      destruct (terminator_full_prefix__final_spec
        text i ltac:(lia) PreH4 PreH12) as [Hi Hprefix].
      subst i. rewrite Hprefix in PreH11.
      destruct (six_source_zeros_choose_64__final_spec
        text seen_one zeros PreH11 ltac:(lia))
        as (indices & Hchosen & Hvalue).
      exists indices, (49 :: 48 :: 48 :: 48 :: 48 :: 48 :: 48 :: nil).
      split; [exact Hchosen|]. split; [rewrite Hvalue; lia|].
      exists 1. lia.
    + intros _. reflexivity.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.
