From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P026_2000D_right_left_wrong_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P026_2000D_right_left_wrong_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P026_2000D_right_left_wrong_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (prefix_next_int64_bounds__prefix_construction
       values prefix i n_pre PreH6 PreH3 ltac:(lia) PreH4 PreH10 PreH11)
    as Hbounds.
  replace (i - 0) with i by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (prefix_next_int64_bounds__prefix_construction
       values prefix i n_pre PreH6 PreH3 ltac:(lia) PreH4 PreH10 PreH11)
    as Hbounds.
  replace (i - 0) with i by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_1 : solver_safety_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (prefix_interval_sum_bounds__pair_update values prefix n_pre l r
    PreH8 PreH10 PreH6 PreH11 PreH15 PreH14) as [Hint Hinterval].
  assert (HL : Znth l directions 0 = 76) by (apply PreH16; lia).
  pose proof (GreedyProgress_take_pair__pair_update values directions l r score
    PreH11 PreH1 ltac:(rewrite PreH9; exact PreH14) HL PreH2 PreH19) as Hprogress.
  pose proof (GreedyProgress_score_bound__pair_update values directions
    (l + 1) (r - 1)
    (score + SpecHelpers.sum_range l r (fun i => Znth i values 0)) n_pre
    PreH8 PreH9 ltac:(lia) ltac:(lia) ltac:(lia) PreH5 PreH6 Hprogress) as Hbound.
  dump_pre_spatial.
  rewrite Hint. int_auto.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_2 : solver_safety_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (prefix_interval_sum_bounds__pair_update values prefix n_pre l r
    PreH8 PreH10 PreH6 PreH11 PreH15 PreH14) as [Hint Hinterval].
  dump_pre_spatial.
  rewrite Hint. int_auto.
Qed.

Lemma proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (prefix_interval_sum_bounds__pair_update values prefix n_pre l r
    PreH8 PreH10 PreH6 PreH11 PreH15 PreH14) as [Hint Hinterval].
  dump_pre_spatial.
  rewrite Hint. int_auto.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (prefix_interval_sum_bounds__pair_update values prefix n_pre l r
    PreH8 PreH10 PreH6 PreH11 PreH15 PreH14) as [Hint Hinterval].
  dump_pre_spatial.
  rewrite Hint. int_auto.
Qed.

Lemma proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (0 :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic (Int64Array.seg_single pre_pre 0 0).
    replace (0 + 1) with 1 by lia.
    cancel (IntArray.full a_pre n_pre values).
    cancel (CharArray.full s_pre n_pre directions).
    cancel (Int64Array.seg pre_pre 0 1 (0 :: nil)).
    cancel (Int64Array.undef_seg pre_pre 1 (n_pre + 1)).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + exact (PrefixSumsPrefix_zero__prefix_construction values).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  eapply PrefixSumsPrefix_snoc__prefix_construction.
  - exact PreH10.
  - rewrite <- PreH6. lia.
  - exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  pose proof
    (PrefixSumsPrefix_complete__prefix_construction
       values prefix_2 ltac:(lia) PreH11)
    as Hcomplete.
  Exists prefix_2.
  split_pure_spatial.
  - rewrite (Int64Array.undef_seg_empty pre_pre (n_pre + 1)).
    sep_apply_l_atomic
      (Int64Array.seg_to_full pre_pre 0 (n_pre + 1) prefix_2).
    replace (pre_pre + 0 * sizeof(INT64)) with pre_pre by lia.
    replace (n_pre + 1 - 0) with (n_pre + 1) by lia.
    cancel (IntArray.full a_pre n_pre values).
    cancel (CharArray.full s_pre n_pre directions).
    cancel (Int64Array.full pre_pre (n_pre + 1) prefix_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply GreedyProgress_initial__control_projection.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH3.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH4.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply GreedyProgress_skip_non_L__frontier_skip; eauto.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_2 : solver_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH4.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_2 : solver_entail_wit_7_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply GreedyProgress_skip_non_R__frontier_skip; eauto.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_1 : solver_entail_wit_9_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (prefix_interval_sum_bounds__pair_update values prefix_2 n_pre l r
    PreH8 PreH10 PreH6 PreH11 PreH15 PreH14) as [Hint Hinterval].
  assert (HL : Znth l directions 0 = 76) by (apply PreH16; lia).
  rewrite Hint.
  apply GreedyProgress_take_pair__pair_update; try assumption.
  rewrite PreH9. exact PreH14.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_2 : solver_entail_wit_9_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (prefix_interval_sum_bounds__pair_update values prefix_2 n_pre l r
    PreH8 PreH10 PreH6 PreH11 PreH15 PreH14) as [Hint Hinterval].
  assert (HL : Znth l directions 0 = 76) by (apply PreH16; lia).
  pose proof (GreedyProgress_take_pair__pair_update values directions l r score
    PreH11 PreH1 ltac:(rewrite PreH9; exact PreH14) HL PreH2 PreH19) as Hprogress.
  pose proof (GreedyProgress_score_bound__pair_update values directions
    (l + 1) (r - 1)
    (score + SpecHelpers.sum_range l r (fun i => Znth i values 0)) n_pre
    PreH8 PreH9 ltac:(lia) ltac:(lia) ltac:(lia) PreH5 PreH6 Hprogress) as Hbound.
  rewrite Hint. exact Hbound.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_3 : solver_entail_wit_9_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (prefix_interval_sum_bounds__pair_update values prefix_2 n_pre l r
    PreH8 PreH10 PreH6 PreH11 PreH15 PreH14) as [Hint Hinterval].
  rewrite Hint. lia.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_4 : solver_entail_wit_9_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_5 : solver_entail_wit_9_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6. exact H.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_1 : solver_entail_wit_9_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_2 : solver_entail_wit_9_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_2_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply (terminal_GreedyProgress_Spec__final_result n_pre directions values score r l);
    auto.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (Int64Array.full_to_full_shape pre_pre (n_pre + 1) prefix).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
