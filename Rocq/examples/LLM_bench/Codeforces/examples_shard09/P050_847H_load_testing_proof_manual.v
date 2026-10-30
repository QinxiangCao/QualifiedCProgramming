From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P050_847H_load_testing_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P050_847H_load_testing_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P050_847H_load_testing_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (cons (Znth 0 values 0) (@nil Z)).
  split_pure_spatial.
  - sep_apply_l_atomic (Int64Array.seg_single inc_pre 0 (Znth 0 values 0)).
    replace (0 + 1) with 1 by lia.
    cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. rewrite Zlength_cons, Zlength_nil. lia.
    + dump_pre_spatial. apply left_profile_singleton__left_profile. lia.
    + dump_pre_spatial.
      intros k Hk.
      assert (k = 0) by lia. subst k.
      rewrite Znth0_cons.
      specialize (PreH3 0 ltac:(lia)).
      lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply left_profile_snoc_input__left_profile.
  - exact PreH10.
  - exact PreH9.
  - lia.
  - replace (i - 1 - 0) with (i - 1) in PreH1 by lia.
    exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app_cons. lia.
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
  replace (i - 1 - 0) with (i - 1) in * by lia.
  eapply left_profile_snoc_successor__left_profile.
  - exact PreH10.
  - exact PreH9.
  - lia.
  - exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia. subst i.
  Exists inc_values_2.
  rewrite H.
  rewrite Int64Array.undef_seg_empty.
  split_pure_spatial.
  - sep_apply (Int64Array.seg_to_full inc_pre 0 n_pre inc_values_2).
    replace (inc_pre + 0 * sizeof(INT64)) with inc_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial.
      intros k Hk.
      apply PreH10.
      rewrite H. exact Hk.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (Znth (n_pre - 1) values 0 :: nil) inc_values_2.
  replace (n_pre - 2 + 1) with (n_pre - 1) by lia.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.seg_single dec_pre (n_pre - 1)
        (Znth (n_pre - 1) values 0)).
    replace (n_pre - 1 + 1) with n_pre by lia.
    cancel (Int64Array.full a_pre n_pre values).
    cancel (Int64Array.full inc_pre n_pre inc_values_2).
    cancel (Int64Array.undef_seg dec_pre 0 (n_pre - 1)).
    cancel (Int64Array.seg dec_pre (n_pre - 1) n_pre
      (Znth (n_pre - 1) values 0 :: nil)).
    cancel (Int64Array.undef_full pre_pre n_pre).
    cancel (Int64Array.undef_full suf_pre n_pre).
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try (rewrite Zlength_cons, Zlength_nil; lia).
    + pose proof
        (right_profile_singleton__right_profile values ltac:(lia)) as Hprof.
      replace (Zlength values - 1) with (n_pre - 1) in Hprof by lia.
      exact Hprof.
    + intros k Hk.
      rewrite Zlength_cons, Zlength_nil in Hk.
      replace k with 0 by lia.
      rewrite Znth0_cons.
      specialize (PreH4 (n_pre - 1) ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i + 1) - (i + 1)) with 0 in PreH1 by lia.
  Exists (Znth i values 0 :: dec_values_2) inc_values_2.
  replace (i - 1 + 1) with i by lia.
  split_pure_spatial.
  - rewrite (Int64Array.seg_unfold dec_pre i n_pre dec_values_2
      (Znth i values 0)) by lia.
    cancel (Int64Array.full a_pre n_pre values).
    cancel (Int64Array.full inc_pre n_pre inc_values_2).
    cancel (Int64Array.undef_seg dec_pre 0 i).
    cancel (((dec_pre + i * sizeof(INT64))) # Int64 |-> Znth i values 0).
    cancel (Int64Array.seg dec_pre (i + 1) n_pre dec_values_2).
    cancel (Int64Array.undef_full pre_pre n_pre).
    cancel (Int64Array.undef_full suf_pre n_pre).
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try (rewrite Zlength_cons; lia).
    + apply right_profile_cons_input__right_profile; try assumption; lia.
    + intros k Hk.
      rewrite Zlength_cons in Hk.
      destruct (Z.eq_dec k 0) as [-> | Hk0].
      * rewrite Znth0_cons.
        specialize (PreH6 i ltac:(lia)). lia.
      * rewrite Znth_cons by lia.
        apply PreH14. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i + 1) - (i + 1)) with 0 in * by lia.
  Exists (Znth 0 dec_values_2 0 + 1 :: dec_values_2) inc_values_2.
  replace (i - 1 + 1) with i by lia.
  split_pure_spatial.
  - rewrite (Int64Array.seg_unfold dec_pre i n_pre dec_values_2
      (Znth 0 dec_values_2 0 + 1)) by lia.
    cancel (Int64Array.full a_pre n_pre values).
    cancel (Int64Array.full inc_pre n_pre inc_values_2).
    cancel (Int64Array.undef_seg dec_pre 0 i).
    cancel (((dec_pre + i * sizeof(INT64))) # Int64 |->
      (Znth 0 dec_values_2 0 + 1)).
    cancel (Int64Array.seg dec_pre (i + 1) n_pre dec_values_2).
    cancel (Int64Array.undef_full pre_pre n_pre).
    cancel (Int64Array.undef_full suf_pre n_pre).
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try (rewrite Zlength_cons; lia).
    + apply (right_profile_cons_successor__right_profile
        values dec_values_2 i); try assumption; lia.
    + intros k Hk.
      rewrite Zlength_cons in Hk.
      destruct (Z.eq_dec k 0) as [-> | Hk0].
      * rewrite Znth0_cons.
        split.
        -- specialize (PreH14 0 ltac:(lia)). lia.
        -- apply right_profile_head_upper_bound__right_profile with values.
           ++ lia.
           ++ intros j Hj. specialize (PreH6 j ltac:(lia)). lia.
           ++ exact PreH12.
      * rewrite Znth_cons by lia.
        apply PreH14. lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = -1) by lia.
  subst i.
  Exists dec_values_2 inc_values_2.
  replace (-1 + 1) with 0 by lia.
  rewrite Int64Array.undef_seg_empty.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.seg_to_full dec_pre 0 n_pre dec_values_2).
    replace (dec_pre + 0 * sizeof(INT64)) with dec_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (Int64Array.full a_pre n_pre values).
    cancel (Int64Array.full inc_pre n_pre inc_values_2).
    cancel (Int64Array.full dec_pre n_pre dec_values_2).
    cancel (Int64Array.undef_full pre_pre n_pre).
    cancel (Int64Array.undef_full suf_pre n_pre).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    intros k Hk. apply PreH13. rewrite PreH10. lia.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH6 as Hleft.
  unfold LeftProfilePrefix in Hleft.
  destruct Hleft as [_ [Hleft_dom _]].
  Exists ((Znth 0 inc_values_2 0 - Znth 0 values 0) :: nil)
    dec_values_2 inc_values_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.seg_single pre_pre 0
        (Znth 0 inc_values_2 0 - Znth 0 values 0)).
    replace (0 + 1) with 1 by lia.
    cancel (Int64Array.full a_pre n_pre values).
    cancel (Int64Array.full inc_pre n_pre inc_values_2).
    cancel (Int64Array.full dec_pre n_pre dec_values_2).
    cancel (Int64Array.seg pre_pre 0 1
      ((Znth 0 inc_values_2 0 - Znth 0 values 0) :: nil)).
    cancel (Int64Array.undef_seg pre_pre 1 n_pre).
    cancel (Int64Array.undef_full suf_pre n_pre).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + apply partial_prefix_costs_singleton__prefix_costs; lia.
    + intros k Hk.
      specialize (PreH9 k Hk).
      specialize (PreH10 k Hk).
      lia.
    + intros k Hk.
      assert (k = 0) by lia. subst k.
      rewrite Znth0_cons.
      specialize (PreH9 0 ltac:(lia)).
      specialize (PreH4 0 ltac:(lia)).
      specialize (Hleft_dom 0 ltac:(rewrite PreH5; lia)).
      lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 1 - 0) with (i - 1) by lia.
  eapply partial_prefix_costs_snoc__prefix_costs.
  - exact PreH13.
  - exact PreH12.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app_cons, PreH12.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  assert (Hpre_len : Zlength pre_values_2 = n_pre) by lia.
  subst i.
  pose proof
    (partial_prefix_costs_full__prefix_costs
      values inc_values_2 pre_values_2 PreH13 ltac:(lia))
    as Hfull.
  Exists pre_values_2 dec_values_2 inc_values_2.
  split_pure_spatial.
  - rewrite Hpre_len.
    rewrite (Int64Array.undef_seg_empty pre_pre n_pre).
    sep_apply_l_atomic
      (Int64Array.seg_to_full pre_pre 0 n_pre pre_values_2).
    replace (pre_pre + 0 * sizeof(INT64)) with pre_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (Int64Array.full a_pre n_pre values).
    cancel (Int64Array.full inc_pre n_pre inc_values_2).
    cancel (Int64Array.full dec_pre n_pre dec_values_2).
    cancel (Int64Array.full pre_pre n_pre pre_values_2).
    cancel (Int64Array.undef_full suf_pre n_pre).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    intros k Hk.
    specialize (PreH14 k Hk).
    specialize (PreH15 k ltac:(rewrite Hpre_len; exact Hk)).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH8 as Hright.
  unfold RightProfileSuffix in Hright.
  destruct Hright as [Hright_len [Hright_dom Hright_rest]].
  specialize (Hright_dom (n_pre - 1) ltac:(rewrite PreH7; lia)).
  replace (Zlength values - Zlength dec_values_2 + (n_pre - 1))
    with (n_pre - 1) in Hright_dom by lia.
  Exists ((Znth (n_pre - 1) dec_values_2 0 -
            Znth (n_pre - 1) values 0) :: nil).
  Exists pre_values_2.
  Exists dec_values_2.
  Exists inc_values_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.seg_single suf_pre (n_pre - 1)
        (Znth (n_pre - 1) dec_values_2 0 -
         Znth (n_pre - 1) values 0)).
    replace (n_pre - 1 + 1) with n_pre by lia.
    replace (n_pre - 2 + 1) with (n_pre - 1) by lia.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + rewrite PreH3.
      apply partial_suffix_costs_singleton__suffix_costs; lia.
    + intros k Hk.
      rewrite Zlength_cons, Zlength_nil in Hk.
      assert (k = 0) by lia. subst k.
      rewrite Znth0_cons.
      specialize (PreH11 (n_pre - 1) ltac:(lia)).
      specialize (PreH4 (n_pre - 1) ltac:(lia)).
      lia.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (new_cost :=
    Znth 0 suf_values_2 0 +
    (Znth i dec_values_2 0 - Znth i values 0)).
  assert (Hnew_partial :
    PartialSuffixCosts values dec_values_2 (new_cost :: suf_values_2)).
  {
    unfold new_cost.
    apply partial_suffix_costs_cons__suffix_costs with (i := i).
    - rewrite PreH8. lia.
    - lia.
    - lia.
    - exact PreH15.
  }
  assert (Hdec_bounds : forall k, 0 <= k < Zlength dec_values_2 ->
    1 <= Znth k dec_values_2 0 <= 1000100000).
  {
    intros k Hk.
    pose proof (PreH16 k ltac:(rewrite <- PreH8; exact Hk)) as Hb.
    lia.
  }
  assert (Hnew_bounds : forall k,
    0 <= k < Zlength (new_cost :: suf_values_2) ->
    0 <= Znth k (new_cost :: suf_values_2) 0 <= 100010000000000).
  {
    eapply (partial_suffix_costs_values_bounded__suffix_costs
      values dec_values_2 (new_cost :: suf_values_2)).
    - lia.
    - lia.
    - exact PreH9.
    - exact Hnew_partial.
    - intros k Hk. apply PreH5. lia.
    - exact Hdec_bounds.
  }
  Exists (new_cost :: suf_values_2).
  Exists pre_values_2.
  Exists dec_values_2.
  Exists inc_values_2.
  split_pure_spatial.
  - unfold new_cost.
    replace (i + 1 - (i + 1)) with 0 by lia.
    sep_apply_l_atomic (Int64Array.seg_single suf_pre i
      (Znth 0 suf_values_2 0 +
       (Znth i dec_values_2 0 - Znth i values 0))).
    replace (i - 1 + 1) with i by lia.
    cancel (Int64Array.full a_pre n_pre values).
    cancel (Int64Array.full inc_pre n_pre inc_values_2).
    cancel (Int64Array.full dec_pre n_pre dec_values_2).
    cancel (Int64Array.full pre_pre n_pre pre_values_2).
    cancel (Int64Array.undef_seg suf_pre 0 i).
    sep_apply
      (Int64Array.seg_merge_to_seg suf_pre i (i + 1) n_pre
        ((Znth 0 suf_values_2 0 +
          (Znth i dec_values_2 0 - Znth i values 0)) :: nil)
        suf_values_2).
    + simpl.
      cancel.
    + lia.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + rewrite Zlength_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = -1) by lia. subst i.
  assert (Hsuf_len : Zlength suf_values_2 = n_pre) by lia.
  assert (Hsuf_full : SuffixCosts values dec_values_2 suf_values_2).
  {
    apply partial_suffix_costs_full__suffix_costs.
    - lia.
    - exact PreH15.
  }
  Exists suf_values_2.
  Exists pre_values_2.
  Exists dec_values_2.
  Exists inc_values_2.
  rewrite Int64Array.undef_seg_empty.
  split_pure_spatial.
  - sep_apply (Int64Array.seg_to_full suf_pre 0 n_pre suf_values_2).
    replace (suf_pre + 0 * sizeof(INT64)) with suf_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    intros k Hk.
    specialize (PreH16 k Hk).
    pose proof (PreH17 k ltac:(rewrite Hsuf_len; exact Hk)) as Hsuf_bound.
    tauto.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH13; assumption.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_2 : solver_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold BestPeakPrefix.
  left; lia.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_3 : solver_entail_wit_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH4; assumption.
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_1 : solver_entail_wit_14_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (peak_cost_bounds__best_peak_update
    values inc_values_2 dec_values_2 pre_values_2 suf_values_2 n_pre i
    PreH6 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    ltac:(lia)
    ltac:(intros k Hk; pose proof (PreH7 k Hk); pose proof (PreH21 k Hk); tauto))
    as Hcost.
  unfold PeakCostValue in Hcost.
  rewrite Z.max_r in Hcost by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_2 : solver_entail_wit_14_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (peak_cost_bounds__best_peak_update
    values inc_values_2 dec_values_2 pre_values_2 suf_values_2 n_pre i
    PreH6 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    ltac:(lia)
    ltac:(intros k Hk; pose proof (PreH7 k Hk); pose proof (PreH21 k Hk); tauto))
    as Hcost.
  unfold PeakCostValue in Hcost.
  rewrite Z.max_r in Hcost by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_3 : solver_entail_wit_14_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH18 as [[Hi Hbest] | [Hi [Hilen [peak [Hpeak [Hbest Hleast]]]]]].
  - subst i best.
    replace
      (Znth 0 pre_values_2 0 + Znth 0 suf_values_2 0 -
       (Znth 0 inc_values_2 0 - Znth 0 values 0) -
       (Znth 0 dec_values_2 0 - Znth 0 values 0) +
       (Znth 0 dec_values_2 0 - Znth 0 values 0))
      with (PeakCostValue values inc_values_2 dec_values_2 pre_values_2 suf_values_2 0).
    + apply best_peak_prefix_first__best_peak_update.
      * reflexivity.
      * rewrite <- PreH6; lia.
      * unfold BestPeakPrefix; left; lia.
    + unfold PeakCostValue.
      rewrite Z.max_r by lia.
      lia.
  - pose proof (peak_cost_bounds__best_peak_update
      values inc_values_2 dec_values_2 pre_values_2 suf_values_2 n_pre peak
      PreH6 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      ltac:(lia)
      ltac:(intros k Hk; pose proof (PreH7 k Hk); pose proof (PreH21 k Hk); tauto))
      as Hcost.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_1 : solver_entail_wit_14_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (peak_cost_bounds__best_peak_update
    values inc_values_2 dec_values_2 pre_values_2 suf_values_2 n_pre i
    PreH6 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    ltac:(lia)
    ltac:(intros k Hk; pose proof (PreH7 k Hk); pose proof (PreH21 k Hk); tauto))
    as Hcost.
  unfold PeakCostValue in Hcost.
  rewrite Z.max_l in Hcost by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_2 : solver_entail_wit_14_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (peak_cost_bounds__best_peak_update
    values inc_values_2 dec_values_2 pre_values_2 suf_values_2 n_pre i
    PreH6 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    ltac:(lia)
    ltac:(intros k Hk; pose proof (PreH7 k Hk); pose proof (PreH21 k Hk); tauto))
    as Hcost.
  unfold PeakCostValue in Hcost.
  rewrite Z.max_l in Hcost by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_3 : solver_entail_wit_14_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH18 as [[Hi Hbest] | [Hi [Hilen [peak [Hpeak [Hbest Hleast]]]]]].
  - subst i best.
    replace
      (Znth 0 pre_values_2 0 + Znth 0 suf_values_2 0 -
       (Znth 0 inc_values_2 0 - Znth 0 values 0) -
       (Znth 0 dec_values_2 0 - Znth 0 values 0) +
       (Znth 0 inc_values_2 0 - Znth 0 values 0))
      with (PeakCostValue values inc_values_2 dec_values_2 pre_values_2 suf_values_2 0).
    + apply best_peak_prefix_first__best_peak_update.
      * reflexivity.
      * rewrite <- PreH6; lia.
      * unfold BestPeakPrefix; left; lia.
    + unfold PeakCostValue.
      rewrite Z.max_l by lia.
      lia.
  - pose proof (peak_cost_bounds__best_peak_update
      values inc_values_2 dec_values_2 pre_values_2 suf_values_2 n_pre peak
      PreH6 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
      ltac:(lia)
      ltac:(intros k Hk; pose proof (PreH7 k Hk); pose proof (PreH21 k Hk); tauto))
      as Hcost.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_1 : solver_entail_wit_14_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (peak_cost_bounds__best_peak_update
    values inc_values_2 dec_values_2 pre_values_2 suf_values_2 n_pre i
    PreH7 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    ltac:(lia)
    ltac:(intros k Hk; pose proof (PreH8 k Hk); pose proof (PreH22 k Hk); tauto))
    as Hcost.
  unfold PeakCostValue in Hcost.
  rewrite Z.max_l in Hcost by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_3_split_goal_2 : solver_entail_wit_14_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply best_peak_prefix_take_current__best_peak_update.
  - exact PreH19.
  - lia.
  - exact PreH1.
  - unfold PeakCostValue.
    rewrite Z.max_l by lia.
    lia.
  - rewrite <- PreH7; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_4_split_goal_1 : solver_entail_wit_14_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (peak_cost_bounds__best_peak_update
    values inc_values_2 dec_values_2 pre_values_2 suf_values_2 n_pre i
    PreH7 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    ltac:(lia)
    ltac:(intros k Hk; pose proof (PreH8 k Hk); pose proof (PreH22 k Hk); tauto))
    as Hcost.
  unfold PeakCostValue in Hcost.
  rewrite Z.max_r in Hcost by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_14_4_split_goal_2 : solver_entail_wit_14_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply best_peak_prefix_take_current__best_peak_update.
  - exact PreH19.
  - lia.
  - exact PreH1.
  - unfold PeakCostValue.
    rewrite Z.max_r by lia.
    lia.
  - rewrite <- PreH7; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_4 : solver_entail_wit_14_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_5_split_goal_1 : solver_entail_wit_14_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply best_peak_prefix_keep_previous__best_peak_update.
  - exact PreH19.
  - lia.
  - unfold PeakCostValue.
    rewrite Z.max_l by lia.
    lia.
  - rewrite <- PreH7; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_5 : solver_entail_wit_14_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_14_6_split_goal_1 : solver_entail_wit_14_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply best_peak_prefix_keep_previous__best_peak_update.
  - exact PreH19.
  - lia.
  - unfold PeakCostValue.
    rewrite Z.max_r by lia.
    lia.
  - rewrite <- PreH7; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_6 : solver_entail_wit_14_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_6_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (i = n_pre) by lia.
  subst i.
  apply (best_peak_full_implies_spec__final_result
    values inc_values dec_values pre_values suf_values best).
  - lia.
  - lia.
  - lia.
  - lia.
  - exact PreH7.
  - exact PreH9.
  - exact PreH11.
  - exact PreH13.
  - intros k Hk. apply PreH5. lia.
  - rewrite <- PreH4. exact PreH16.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (Int64Array.full_to_full_shape inc_pre n_pre inc_values).
  sep_apply_l_atomic (Int64Array.full_to_full_shape dec_pre n_pre dec_values).
  sep_apply_l_atomic (Int64Array.full_to_full_shape pre_pre n_pre pre_values).
  sep_apply_l_atomic (Int64Array.full_to_full_shape suf_pre n_pre suf_values).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
