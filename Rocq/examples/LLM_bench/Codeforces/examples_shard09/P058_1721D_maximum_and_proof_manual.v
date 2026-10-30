From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P058_1721D_maximum_and_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P058_1721D_maximum_and_proof_auto.
Import naive_C_Rules.
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P058_1721D_maximum_and_lib.
Local Open Scope sac.

Lemma proof_of_feasible_entail_wit_1_split_goal_1 : feasible_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MaskedBuffersPrefix, MaskedLeft, MaskedComplementRight.
  simpl.
  auto.
Qed.

Lemma proof_of_feasible_entail_wit_1_split_goal_2 : feasible_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH8. auto.
Qed.

Lemma proof_of_feasible_entail_wit_1_split_goal_3 : feasible_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH7. auto.
Qed.

Lemma proof_of_feasible_entail_wit_1 : feasible_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_feasible_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_feasible_entail_wit_2_split_goal_1 : feasible_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply masked_buffers_prefix_snoc__feasible_buffers; eauto; lia.
Qed.

Lemma proof_of_feasible_entail_wit_2_split_goal_2 : feasible_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH9. auto.
Qed.

Lemma proof_of_feasible_entail_wit_2_split_goal_3 : feasible_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH8. auto.
Qed.

Lemma proof_of_feasible_entail_wit_2 : feasible_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_feasible_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_feasible_entail_wit_3_split_goal_1 : feasible_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH8. auto.
Qed.

Lemma proof_of_feasible_entail_wit_3_split_goal_2 : feasible_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH7. auto.
Qed.

Lemma proof_of_feasible_entail_wit_3 : feasible_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_feasible_entail_wit_4 : feasible_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  Exists ka_values_2 kb_values_2.
  split_pure_spatial.
  - rewrite (UIntArray.undef_seg_empty ka_pre n_pre).
    rewrite (UIntArray.undef_seg_empty kb_pre n_pre).
    sep_apply_l_atomic
      (UIntArray.seg_to_full ka_pre 0 n_pre ka_values_2).
    sep_apply_l_atomic
      (UIntArray.seg_to_full kb_pre 0 n_pre kb_values_2).
    replace (ka_pre + 0 * sizeof(UINT)) with ka_pre by lia.
    replace (kb_pre + 0 * sizeof(UINT)) with kb_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (UIntArray.full ka_pre n_pre ka_values_2).
    cancel (UIntArray.full kb_pre n_pre kb_values_2).
    cancel (UIntArray.full a_pre n_pre left).
    cancel (UIntArray.full b_pre n_pre right).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_feasible_entail_wit_5 : feasible_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists l1_2 l1 ka_values_2 kb_values_2.
  split_pure_spatial.
  - cancel (UIntArray.full a_pre n_pre left).
    cancel (UIntArray.full b_pre n_pre right).
    cancel (UIntArray.full ka_pre n_pre l1).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_feasible_entail_wit_6 : feasible_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists sorted_kb_2 sorted_ka_2 ka_values_2 kb_values_2.
  split_pure_spatial.
  - cancel (UIntArray.full a_pre n_pre left).
    cancel (UIntArray.full b_pre n_pre right).
    cancel (UIntArray.full ka_pre n_pre sorted_ka_2).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold sublist; simpl; reflexivity.
Qed.

Lemma proof_of_feasible_entail_wit_7 : feasible_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (masked_buffers_sorted_lengths__feasible_sort_compare
       left right mask_pre ka_values_2 kb_values_2
       sorted_ka_2 sorted_kb_2 n_pre
       PreH5 PreH6 PreH13 PreH14 PreH15) as [Hlen_ka Hlen_kb].
  Exists sorted_kb_2 sorted_ka_2 ka_values_2 kb_values_2.
  split_pure_spatial.
  - cancel (UIntArray.full a_pre n_pre left).
    cancel (UIntArray.full b_pre n_pre right).
    cancel (UIntArray.full ka_pre n_pre sorted_ka_2).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    eapply sublist_prefix_snoc_from_znth_eq__feasible_sort_compare; eauto; lia.
Qed.

Lemma proof_of_feasible_return_wit_1_split_goal_1 : feasible_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros _.
  eapply mask_feasible_from_complete_sorted_prefix__feasible_sort_compare;
    eauto; try lia.
  now replace i with n_pre in PreH17 by lia.
Qed.

Lemma proof_of_feasible_return_wit_1_split_goal_spatial : feasible_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (UIntArray.full_to_full_shape ka_pre n_pre sorted_ka).
  sep_apply_l_atomic (UIntArray.full_to_full_shape kb_pre n_pre sorted_kb).
  cancel.
Qed.

Lemma proof_of_feasible_return_wit_1 : feasible_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_feasible_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_feasible_return_wit_2_split_goal_1 : feasible_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros _.
  apply (proj1 (mono_nondec_iff_increasing sorted_ka)) in PreH16.
  apply (proj1 (mono_nondec_iff_increasing sorted_kb)) in PreH17.
  eapply sorted_first_mismatch_refutes_mask_feasible__feasible_sort_compare;
    eauto; try lia.
Qed.

Lemma proof_of_feasible_return_wit_2_split_goal_spatial : feasible_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (UIntArray.full_to_full_shape kb_pre n_pre sorted_kb).
  sep_apply_l_atomic (UIntArray.full_to_full_shape ka_pre n_pre sorted_ka).
  cancel.
Qed.

Lemma proof_of_feasible_return_wit_2 : feasible_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_feasible_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GreedyMaskPrefixOptimal.
  repeat split.
  - apply mask_feasible_zero__solver_init_bounds. lia.
  - intros v Hv.
    pose proof (and_candidate_range30__solver_init_bounds left right v Hv)
      as Hrange.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    change (v / 1073741824 <= 0).
    rewrite Z.div_small by lia.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto || assumption).
  apply PreH4. exact H.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto || assumption).
  apply PreH3. exact H.
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
  rewrite unsigned_last_nbits_eq.
  - apply lor_single_bit_range30__solver_init_bounds; try lia.
  - rewrite Z.shiftl_1_l.
    split.
    + pose proof (Z.pow_pos_nonneg 2 bit ltac:(lia) ltac:(lia)). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hretval : retval = 1) by lia.
  specialize (PreH3 Hretval).
  assert (Hbit32 :
    unsigned_last_nbits (Z.shiftl 1 bit) 32 = Z.shiftl 1 bit).
  {
    apply unsigned_last_nbits_eq.
    rewrite Z.shiftl_1_l.
    split.
    - apply Z.pow_nonneg. lia.
    - apply Z.pow_lt_mono_r; lia.
  }
  rewrite Hbit32 in PreH3.
  pose proof
    (greedy_mask_take_feasible_bit__solver_transitions
      left right bit ans PreH25 PreH24 PreH3) as Hnext.
  destruct (Z.eq_dec bit 0) as [Hbit0 | Hbit0].
  - Right.
    split_pure_spatial.
    + cancel.
    + split_pures;
        try (dump_pre_spatial; lia);
        try (dump_pre_spatial; assumption).
      dump_pre_spatial.
      rewrite Hbit32.
      exact Hnext.
  - Left.
    split_pure_spatial.
    + sep_apply_l_atomic
        (UIntArray.full_shape_to_undef_full ka_pre n_pre).
      sep_apply_l_atomic
        (UIntArray.full_shape_to_undef_full kb_pre n_pre).
      cancel.
    + split_pures;
        try (dump_pre_spatial; lia);
        try (dump_pre_spatial; assumption).
      dump_pre_spatial.
      rewrite Hbit32.
      exact Hnext.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH4 PreH26).
  assert (Hbit32 :
    unsigned_last_nbits (Z.shiftl 1 bit) 32 = Z.shiftl 1 bit).
  {
    apply unsigned_last_nbits_eq.
    rewrite Z.shiftl_1_l.
    split.
    - apply Z.pow_nonneg. lia.
    - apply Z.pow_lt_mono_r; lia.
  }
  rewrite Hbit32 in PreH4.
  assert (Hlen : Zlength left = Zlength right) by lia.
  pose proof
    (greedy_mask_skip_infeasible_bit__solver_transitions
      left right bit ans PreH25 Hlen PreH24 PreH4) as Hnext.
  destruct (Z.eq_dec bit 0) as [Hbit0 | Hbit0].
  - Right.
    split_pure_spatial.
    + cancel.
    + split_pures;
        try (dump_pre_spatial; lia);
        try (dump_pre_spatial; assumption).
  - Left.
    split_pure_spatial.
    + sep_apply_l_atomic
        (UIntArray.full_shape_to_undef_full ka_pre n_pre).
      sep_apply_l_atomic
        (UIntArray.full_shape_to_undef_full kb_pre n_pre).
      cancel.
    + split_pures;
        try (dump_pre_spatial; lia);
        try (dump_pre_spatial; assumption).
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply greedy_mask_at_minus_one_spec__solver_final with (bit := bit); auto; lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto || assumption).
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_2 : solver_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto || assumption).
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_2.
Qed.
