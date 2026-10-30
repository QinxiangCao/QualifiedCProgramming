From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P053_1393C_pinkie_pie_eats_patty_cakes_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P053_1393C_pinkie_pie_eats_patty_cakes_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_13_split_goal_1 : solver_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof
    (terminal_frequency_bounds__terminal_result
       values counts n_pre i mx c
       PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11
       PreH12 PreH13 PreH14 PreH15) as Hterminal.
  destruct Hterminal as [Hi [Hmx Hc]].
  rewrite Z.quot_div_nonneg by lia.
  assert (Hquotient_upper :
    (n_pre - c) / (mx - 1) <= n_pre - c).
  { apply Z.div_le_upper_bound; nia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_2 : solver_safety_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof
    (terminal_frequency_bounds__terminal_result
       values counts n_pre i mx c
       PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11
       PreH12 PreH13 PreH14 PreH15) as Hterminal.
  destruct Hterminal as [Hi [Hmx Hc]].
  rewrite Z.quot_div_nonneg by lia.
  assert (Hquotient_nonnegative :
    0 <= (n_pre - c) / (mx - 1)).
  { apply Z_div_nonneg_nonneg; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_14_split_goal_1 : solver_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  pose proof
    (terminal_frequency_bounds__terminal_result
       values counts n_pre i mx c
       PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11
       PreH12 PreH13 PreH14 PreH15) as Hterminal.
  destruct Hterminal as [Hi [Hmx Hc]].
  left.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_14_split_goal_2 : solver_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof
    (terminal_frequency_bounds__terminal_result
       values counts n_pre i mx c
       PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11
       PreH12 PreH13 PreH14 PreH15) as Hterminal.
  destruct Hterminal as [Hi [Hmx Hc]].
  lia.
Qed.

Lemma proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  rewrite Znth_repeat.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CountPrefix.
  split.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
    lia.
  - intros value Hvalue.
    unfold repeat_Z.
    rewrite Znth_repeat.
    unfold sublist.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH4.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply count_prefix_step__counting_invariant.
  - lia.
  - pose proof (PreH8 i ltac:(lia)) as Hvalue.
    lia.
  - exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH13 k_2 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply maximum_frequency_prefix_zero__counting_invariant.
  unfold CountPrefix in PreH12.
  destruct PreH12 as [Hlength _].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace n_pre with i by lia.
  exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH8.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (maximum_frequency_prefix_raise__frequency_transitions counts_2 i mx c);
    try assumption; try lia.
  unfold CountPrefix in PreH15.
  destruct PreH15 as [Hcounts_length Hcounts_values].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (maximum_frequency_prefix_tie__frequency_transitions counts_2 i mx c);
    try assumption; try lia.
  unfold CountPrefix in PreH16.
  destruct PreH16 as [Hcounts_length Hcounts_values].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_3_split_goal_1 : solver_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (maximum_frequency_prefix_below__frequency_transitions counts_2 i mx c);
    try assumption; try lia.
  - unfold CountPrefix in PreH16.
    destruct PreH16 as [Hcounts_length Hcounts_values].
    lia.
  - specialize (PreH18 i ltac:(lia)).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre + 1) by lia.
  pose proof (terminal_frequency_bounds__terminal_result
    values counts_2 n_pre i mx c
    PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    as Hterminal.
  rewrite Z.quot_div_nonneg by lia.
  rewrite PreH3.
  apply terminal_frequency_summary_implies_Spec with
      (counts := counts_2) (mx := mx) (multiplicity := c).
  - rewrite <- PreH3. exact PreH14.
  - rewrite <- PreH3, <- Hi. exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre + 1) by lia.
  rewrite <- Hi.
  exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (terminal_frequency_bounds__terminal_result
    values counts_2 n_pre i mx c
    PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    as Hterminal.
  exact (proj1 (proj2 (proj2 Hterminal))).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (terminal_frequency_bounds__terminal_result
    values counts_2 n_pre i mx c
    PreH3 PreH7 PreH8 PreH9 PreH1 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    as Hterminal.
  exact (proj1 (proj1 (proj2 Hterminal))).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_5 : solver_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH6 k H).
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_5.
Qed.
