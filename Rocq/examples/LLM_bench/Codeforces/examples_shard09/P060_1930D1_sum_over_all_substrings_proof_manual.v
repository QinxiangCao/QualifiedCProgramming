From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P060_1930D1_sum_over_all_substrings_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P060_1930D1_sum_over_all_substrings_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P060_1930D1_sum_over_all_substrings_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply CompletedRows_initial.
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

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists 0 total.
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre bits).
  - split_pures.
    all: try solve [dump_pre_spatial; lia].
    all: try solve [dump_pre_spatial; assumption].
    all: try solve [dump_pre_spatial; apply CurrentRow_initial].
    all: try solve [dump_pre_spatial; apply PrefixCoverSummary_initial; lia].
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_1 : solver_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbinary : Forall (fun c => c = 48 \/ c = 49) bits).
  {
    apply Forall_forall. intros c Hc.
    apply In_nth with (d := 0) in Hc.
    destruct Hc as [j [Hj Hc]].
    specialize (PreH7 (Z.of_nat j)).
    unfold Znth in PreH7. rewrite Nat2Z.id in PreH7.
    rewrite Hc in PreH7.
    apply PreH7.
    rewrite PreH6, Zlength_correct. lia.
  }
  eapply PrefixCoverSummary_uncovered_one_FValue.
  - exact PreH23.
  - lia.
  - lia.
  - exact Hbinary.
  - exact PreH2.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_1 : solver_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbinary : Forall (fun c => c = 48 \/ c = 49) bits).
  {
    apply Forall_forall. intros c Hc.
    apply In_nth with (d := 0) in Hc.
    destruct Hc as [j [Hj Hc]].
    specialize (PreH6 (Z.of_nat j)).
    unfold Znth in PreH6. rewrite Nat2Z.id in PreH6.
    rewrite Hc in PreH6.
    apply PreH6.
    rewrite PreH5, Zlength_correct. lia.
  }
  eapply PrefixCoverSummary_no_new_cover_FValue.
  - exact PreH22.
  - lia.
  - lia.
  - exact Hbinary.
  - left. exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_3_split_goal_1 : solver_entail_wit_3_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbinary : Forall (fun c => c = 48 \/ c = 49) bits).
  {
    apply Forall_forall. intros c Hc.
    apply In_nth with (d := 0) in Hc.
    destruct Hc as [j [Hj Hc]].
    specialize (PreH7 (Z.of_nat j)).
    unfold Znth in PreH7. rewrite Nat2Z.id in PreH7.
    rewrite Hc in PreH7.
    apply PreH7.
    rewrite PreH6, Zlength_correct. lia.
  }
  eapply PrefixCoverSummary_no_new_cover_FValue.
  - exact PreH23.
  - lia.
  - lia.
  - exact Hbinary.
  - right. exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (row_total_2 + (cnt + 1)) base_2.
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre bits).
  - split_pures.
    all: try solve [dump_pre_spatial; lia].
    all: try solve [dump_pre_spatial; exact PreH8].
    all: try solve [dump_pre_spatial; exact PreH22].
    all: try solve [dump_pre_spatial;
      eapply CurrentRow_extend; [lia | exact PreH23 | exact PreH1]].
    all: try solve [dump_pre_spatial;
      eapply PrefixCoverSummary_extend_uncovered_one;
      [exact PreH24 | lia | exact PreH3 | lia | exact PreH1]].
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (row_total_2 + cnt) base_2.
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre bits).
  - split_pures.
    all: try solve [dump_pre_spatial; lia].
    all: try solve [dump_pre_spatial; exact PreH7].
    all: try solve [dump_pre_spatial; exact PreH21].
    all: try solve [dump_pre_spatial;
      eapply CurrentRow_extend; [lia | exact PreH22 | exact PreH1]].
    all: try solve [dump_pre_spatial;
      eapply PrefixCoverSummary_extend_no_new_cover;
      [exact PreH23 | lia | left; exact PreH2 | exact PreH1]].
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (row_total_2 + cnt) base_2.
  split_pure_spatial.
  - cancel (CharArray.full s_pre n_pre bits).
  - split_pures.
    all: try solve [dump_pre_spatial; lia].
    all: try solve [dump_pre_spatial; exact PreH8].
    all: try solve [dump_pre_spatial; exact PreH22].
    all: try solve [dump_pre_spatial;
      eapply CurrentRow_extend; [lia | exact PreH23 | exact PreH1]].
    all: try solve [dump_pre_spatial;
      eapply PrefixCoverSummary_extend_no_new_cover;
      [exact PreH24 | lia | right; exact PreH2 | exact PreH1]].
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (k = n_pre) by lia.
  subst k.
  apply CompletedRows_extend.
  - rewrite <- PreH4. lia.
  - exact PreH19.
  - rewrite <- PreH4. exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply CompletedRows_final_Spec.
  replace (Zlength bits) with i by lia.
  exact PreH10.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
