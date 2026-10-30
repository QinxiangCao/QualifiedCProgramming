From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P028_474B_worms_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P028_474B_worms_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P028_474B_worms_lib.
Local Open Scope sac.

Lemma proof_of_locate_pile_safety_wit_2_split_goal_1 : locate_pile_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (hi - lo) / 2) by (apply Z.div_pos; lia).
  assert ((hi - lo) / 2 <= hi - lo) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_locate_pile_safety_wit_2_split_goal_2 : locate_pile_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (hi - lo) / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_locate_pile_safety_wit_2 : locate_pile_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_locate_pile_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_locate_pile_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_locate_pile_entail_wit_1_split_goal_1 : locate_pile_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixSums in PreH8.
  destruct PreH8 as [_ Hprefix].
  specialize (Hprefix 0 ltac:(lia)).
  unfold SpecHelpers.sum_range in Hprefix.
  rewrite SumLib.ZRange.sum_range_unfold in Hprefix.
  change (Znth 0 prefix 0 = 0) in Hprefix.
  change (Znth 0 prefix 0 < q_pre).
  rewrite Hprefix.
  apply Z.lt_le_trans with 1; lia.
Qed.

Lemma proof_of_locate_pile_entail_wit_1_split_goal_2 : locate_pile_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH5 k H).
Qed.

Lemma proof_of_locate_pile_entail_wit_1 : locate_pile_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_locate_pile_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_locate_pile_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_locate_pile_entail_wit_2_split_goal_1 : locate_pile_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  assert ((hi - lo) / 2 < hi - lo) by
    (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_locate_pile_entail_wit_2_split_goal_2 : locate_pile_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  assert (0 <= (hi - lo) / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_locate_pile_entail_wit_2 : locate_pile_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_locate_pile_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_locate_pile_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_locate_pile_entail_wit_3_2_split_goal_1 : locate_pile_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (((lo + (hi - lo) ÷ 2) + 1) - 1) with
      (lo + (hi - lo) ÷ 2) by lia.
  exact PreH1.
Qed.

Lemma proof_of_locate_pile_entail_wit_3_2 : locate_pile_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_locate_pile_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_locate_pile_return_wit_1_split_goal_1 : locate_pile_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlohi : lo = hi) by lia.
  subst hi.
  unfold PileIndex.
  split.
  - lia.
  - unfold PrefixSums in PreH7.
    destruct PreH7 as [_ Hprefix].
    pose proof (Hprefix (lo - 1) ltac:(lia)) as Hprefix_lo_minus_one.
    pose proof (Hprefix lo ltac:(lia)) as Hprefix_lo.
    replace ((lo - 1) - 1) with (lo - 2) in Hprefix_lo_minus_one by lia.
    split.
    + rewrite <- Hprefix_lo_minus_one.
      exact PreH13.
    + rewrite <- Hprefix_lo.
      exact PreH14.
Qed.

Lemma proof_of_locate_pile_return_wit_1 : locate_pile_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_locate_pile_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_6_split_goal_1 : solver_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixSumsPrefix in PreH13.
  destruct PreH13 as [_ Hprefix].
  specialize (Hprefix i ltac:(lia)).
  pose proof
    (sum_range_upper_bound__prefix_step pile_sizes n_pre i PreH8
       ltac:(lia) PreH5) as Hsum.
  dump_pre_spatial.
  replace (i - 0) with i by lia.
  rewrite Hprefix.
  replace
    (SpecHelpers.sum_range 0 (i - 1) (fun k => Znth k pile_sizes 0) +
       Znth i pile_sizes 0)
    with (SpecHelpers.sum_range 0 i (fun k => Znth k pile_sizes 0))
    by (exact (sum_range_succ__prefix_step i
          (fun k : Z => Znth k pile_sizes 0) ltac:(lia))).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_6_split_goal_2 : solver_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixSumsPrefix in PreH13.
  destruct PreH13 as [_ Hprefix].
  specialize (Hprefix i ltac:(lia)).
  pose proof
    (sum_range_upper_bound__prefix_step pile_sizes n_pre i PreH8
       ltac:(lia) PreH5) as Hsum.
  dump_pre_spatial.
  replace (i - 0) with i by lia.
  rewrite Hprefix.
  replace
    (SpecHelpers.sum_range 0 (i - 1) (fun k => Znth k pile_sizes 0) +
       Znth i pile_sizes 0)
    with (SpecHelpers.sum_range 0 i (fun k => Znth k pile_sizes 0))
    by (exact (sum_range_succ__prefix_step i
          (fun k : Z => Znth k pile_sizes 0) ltac:(lia))).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold PrefixSumsPrefix.
  split.
  - rewrite Zlength_cons, Zlength_nil.
    rewrite <- PreH10.
    lia.
  - intros i Hi.
    rewrite Zlength_cons, Zlength_nil in Hi.
    assert (i = 0) by lia.
    subst i.
    simpl.
    unfold SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.sum_range.
    rewrite SumLib.ZRange.sum_Z_range_empty by lia.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_spatial : solver_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (Int64Array.seg_single pre_pre 0 0).
  sep_apply_l_atomic
    (Int64Array.missing_i_shape_to_seg_shape_head pre_pre 0 (n_pre + 1)).
  - dump_pre_spatial.
    lia.
  - replace (0 + 1) with 1 by lia.
    cancel (IntArray.full_shape out_pre m_pre).
    cancel (Int64Array.seg pre_pre 0 1 (0 :: nil)).
    cancel (Int64Array.seg_shape pre_pre 1 (n_pre + 1)).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (0 :: nil).
  split_pure_spatial.
  - replace (0 + 1) with 1 by lia.
    cancel (IntArray.full piles_pre n_pre pile_sizes).
    cancel (Int64Array.full queries_pre m_pre worm_queries).
    cancel (IntArray.full_shape out_pre m_pre).
    cancel (Int64Array.seg pre_pre 0 1 (0 :: nil)).
    cancel (Int64Array.seg_shape pre_pre 1 (n_pre + 1)).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    rewrite Zlength_cons, Zlength_nil.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_spatial : solver_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Int64Array.missing_i_shape_unfold; try lia.
  Left.
  repeat cancel.
  split_pure_spatial.
  - cancel (Int64Array.seg_shape pre_pre (i + 1 + 1) (n_pre + 1)).
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  assert (Hreplace :
    replace_Znth (i + 1) (Znth i prefix 0 + Znth i pile_sizes 0)
      (prefix ++ (old_next :: nil)) =
    prefix ++ ((Znth i prefix 0 + Znth i pile_sizes 0) :: nil)).
  { rewrite <- PreH12.
    apply replace_Znth_app_last__prefix_step. }
  rewrite Hreplace.
  Exists (prefix ++ ((Znth i prefix 0 + Znth i pile_sizes 0) :: nil)).
  split_pure_spatial.
  - replace (i + 2) with (i + 1 + 1) by lia.
    sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
         pre_pre (i + 1) (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (Int64Array.full_to_seg pre_pre (i + 1 + 1)
           (prefix ++ ((Znth i prefix 0 + Znth i pile_sizes 0) :: nil))).
      repeat cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial. exact PreH11.
    + dump_pre_spatial.
      rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + dump_pre_spatial.
      apply prefix_sums_extend__prefix_step; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists prefix_next.
  split_pure_spatial.
  - replace ((i + 1) + 1) with (i + 2) by lia.
    repeat cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  pose proof
    (prefix_sums_prefix_complete__prefix_exit
       pile_sizes prefix_2 ltac:(lia) PreH14)
    as Hcomplete.
  Exists prefix_2.
  split_pure_spatial.
  - rewrite (Int64Array.seg_shape_empty pre_pre (n_pre + 1)).
    sep_apply_l_atomic
      (Int64Array.seg_to_full pre_pre 0 (n_pre + 1) prefix_2).
    replace (pre_pre + 0 * sizeof(INT64)) with pre_pre by lia.
    replace (n_pre + 1 - 0) with (n_pre + 1) by lia.
    cancel (IntArray.full piles_pre n_pre pile_sizes).
    cancel (Int64Array.full queries_pre m_pre worm_queries).
    cancel (IntArray.full_shape out_pre m_pre).
    cancel (Int64Array.full pre_pre (n_pre + 1) prefix_2).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_spatial : solver_entail_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply IntArray.full_shape_to_seg_shape.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_3 : solver_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_spatial : solver_entail_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite IntArray.missing_i_shape_unfold; try lia.
  Left.
  split_pure_spatial.
  - cancel (IntArray.seg_shape out_pre (i + 1) m_pre).
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
  assert (Hreplace :
    replace_Znth i retval (result +:: old_out) = result +:: retval).
  {
    rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (i - Zlength result) with 0 by lia.
    reflexivity.
  }
  rewrite Hreplace.
  Exists (result +:: retval) prefix_2.
  assert (Hlen_next : Zlength (result +:: retval) = i + 1).
  {
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  }
  assert (Hindex_next :
    forall j, 0 <= j < i + 1 ->
      PileIndex pile_sizes (Znth j worm_queries 0)
        (Znth j (result +:: retval) 0)).
  {
    eapply PileIndex_app_single__query_step; eauto.
  }
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.full_to_seg out_pre (i + 1) (result +:: retval)).
    sep_apply_l_atomic
      (IntArray.missing_i_shape_to_seg_shape_head out_pre i m_pre).
    + dump_pre_spatial. lia.
    + cancel (IntArray.full piles_pre n_pre pile_sizes).
      cancel (Int64Array.full queries_pre m_pre worm_queries).
      cancel (IntArray.seg out_pre 0 (i + 1) (result +:: retval)).
      cancel (IntArray.seg_shape out_pre (i + 1) m_pre).
      cancel (Int64Array.full pre_pre (n_pre + 1) prefix_2).
  - split_pures; dump_pre_spatial; eauto.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_3 : solver_entail_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
  exact (PreH5 k H).
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i.
  assert (Hlen : Zlength result_2 = m_pre) by lia.
  rewrite Hlen in *.
  Exists result_2.
  split_pure_spatial.
  - rewrite IntArray.seg_shape_empty.
    sep_apply_l_atomic (IntArray.seg_to_full out_pre 0 m_pre result_2).
    sep_apply_l_atomic (Int64Array.full_to_full_shape pre_pre (n_pre + 1) prefix).
    replace (out_pre + 0 * sizeof(INT)) with out_pre by lia.
    replace (m_pre - 0) with m_pre by lia.
    cancel.
  - dump_pre_spatial.
    unfold Spec, PileIndex in *.
    split.
    + lia.
    + intros j Hj.
      apply PreH15.
      lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_5_pure_split_goal_1 : solver_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
  unfold PrefixSums in PreH16.
  dump_pre_spatial.
  rewrite PreH14.
  exact (proj1 PreH16).
Qed.

Lemma proof_of_solver_partial_solve_wit_5_pure_split_goal_2 : solver_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_5_pure_split_goal_3 : solver_partial_solve_wit_5_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto || eauto).
  dump_pre_spatial.
  eapply query_bound_by_prefix_total__query_step; eauto; lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_5_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_5_pure_split_goal_3.
Qed.
