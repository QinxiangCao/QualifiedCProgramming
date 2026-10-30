From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P020_433A_kitahara_harukis_gift_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P020_433A_kitahara_harukis_gift_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_4_split_goal_1 : solver_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (weight_values_of_explicit_require weights n_pre PreH3 PreH2) as Hweights.
  pose proof (weight_at_from_pre__prefix_scan weights i Hweights ltac:(lia)) as Hweight.
  assert (Hweight_nonneg : 0 <= Znth i weights 0) by
    (destruct Hweight; lia).
  rewrite zdiv_equiv by lia.
  pose proof (unit_weight_at_from_pre__prefix_scan weights i Hweights ltac:(lia)) as Hunit.
  unfold UnitWeight in Hunit.
  destruct Hunit as [Hunit | Hunit].
  - assert (Htotal_bound : total <= 200) by lia.
    assert (Hunit_bound : Znth i weights 0 / 100 <= 2) by lia.
    dump_pre_spatial. change INT_MAX with 2147483647. lia.
  - assert (Htotal_bound : total <= 200) by lia.
    assert (Hunit_bound : Znth i weights 0 / 100 <= 2) by lia.
    dump_pre_spatial. change INT_MAX with 2147483647. lia.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_2 : solver_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (weight_values_of_explicit_require weights n_pre PreH3 PreH2) as Hweights.
  pose proof (weight_at_from_pre__prefix_scan weights i Hweights ltac:(lia)) as Hweight.
  assert (Hweight_nonneg : 0 <= Znth i weights 0) by
    (destruct Hweight; lia).
  rewrite zdiv_equiv by lia.
  pose proof (unit_weight_at_from_pre__prefix_scan weights i Hweights ltac:(lia)) as Hunit.
  unfold UnitWeight in Hunit.
  destruct Hunit as [Hunit | Hunit].
  - dump_pre_spatial. change INT_MIN with (-2147483648). lia.
  - dump_pre_spatial. change INT_MIN with (-2147483648). lia.
Qed.

Lemma proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixUnitTotal, UnitSum.
  rewrite Zsublist_nil by lia.
  simpl.
  pose proof (Zlength_nonneg weights).
  lia.
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

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (weight_values_of_explicit_require weights n_pre PreH3 PreH2) as Hweights.
  pose proof (weight_at_from_pre__prefix_scan weights i Hweights ltac:(lia)) as Hweight.
  assert (Hweight_nonneg : 0 <= Znth i weights 0) by
    (destruct Hweight; lia).
  rewrite zdiv_equiv by lia.
  apply prefix_unit_total_step__prefix_scan; auto.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (weight_values_of_explicit_require weights n_pre PreH3 PreH2) as Hweights.
  pose proof (weight_at_from_pre__prefix_scan weights i Hweights ltac:(lia)) as Hweight.
  assert (Hweight_nonneg : 0 <= Znth i weights 0) by
    (destruct Hweight; lia).
  rewrite zdiv_equiv by lia.
  pose proof (unit_weight_at_from_pre__prefix_scan weights i Hweights ltac:(lia)) as Hunit.
  unfold UnitWeight in Hunit.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (weight_values_of_explicit_require weights n_pre PreH3 PreH2) as Hweights.
  pose proof (weight_at_from_pre__prefix_scan weights i Hweights ltac:(lia)) as Hweight.
  assert (Hweight_nonneg : 0 <= Znth i weights 0) by
    (destruct Hweight; lia).
  rewrite zdiv_equiv by lia.
  pose proof (unit_weight_at_from_pre__prefix_scan weights i Hweights ltac:(lia)) as Hunit.
  unfold UnitWeight in Hunit.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SolverReturnBridge. intuition.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec. right. split; [reflexivity |].
  intros [chosen [Hlen [Hbits Hgrams]]].
  assert (Hi : i = n_pre) by lia. subst i.
  unfold PrefixUnitTotal in PreH10.
  destruct PreH10 as [_ Htotal].
  rewrite (sublist_self weights n_pre) in Htotal by lia.
  pose proof (weight_values_of_explicit_require weights n_pre PreH3 PreH2) as Hweights.
  pose proof
    (proj1
       (fair_split_unit_balance__final_result
          weights chosen Hweights Hlen Hbits) Hgrams) as Hunits.
  rewrite Z.rem_mod_nonneg in PreH11 by lia.
  apply PreH11.
  apply (proj2 (Z.mod_divide total 2 ltac:(lia))).
  exists
    (fold_right Z.add 0
       (map (fun q => fst q * UnitWeight (snd q))
          (combine chosen weights))).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia. subst i. exact PreH10.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace i with n_pre in PreH10 by lia.
  dump_pre_spatial.
  exact PreH10.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_spatial : solver_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  simpl.
  rewrite Z.add_0_r.
  cancel (CharArray.undef_full &( "reach") 205).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_spatial : solver_entail_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  simpl.
  rewrite Z.add_0_r.
  cancel (CharArray.full &( "reach") 205 (repeat_Z 0 205)).
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ReachTable.
  split.
  - rewrite Zlength_replace_Znth.
    unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    reflexivity.
  - split.
    + intros k Hk.
      destruct (Z.eq_dec k 0) as [-> | Hne].
      * right.
        apply Znth_replace_Znth_Same.
        unfold repeat_Z.
        rewrite Zlength_correct, repeat_length.
        lia.
      * left.
        rewrite Znth_replace_Znth_Diff.
        -- unfold repeat_Z. apply Znth_repeat.
        -- unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
        -- unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
        -- lia.
    + intros k Hk.
      rewrite Zsublist_nil by lia.
      destruct (Z.eq_dec k 0) as [-> | Hne].
      * split.
        -- intros _.
           exists (@nil Z).
           split.
           ++ rewrite Zlength_nil. reflexivity.
           ++ split; [constructor | reflexivity].
        -- intros _.
           rewrite Znth_replace_Znth_Same.
           ++ lia.
           ++ unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
      * split.
        -- rewrite Znth_replace_Znth_Diff.
           ++ unfold repeat_Z. rewrite Znth_repeat. congruence.
           ++ unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
           ++ unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
           ++ lia.
        -- intros [chosen [Hlen [Hbits Hsum]]].
           exfalso. apply Hne.
           rewrite Zlength_nil in Hlen.
           assert (chosen = (@nil Z)) as ->.
           ++ destruct chosen as [| x xs]; [reflexivity |].
              rewrite Zlength_cons in Hlen.
              pose proof (Zlength_nonneg xs). lia.
           ++ simpl in Hsum. exact Hsum.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply reach_table_to_inner_at_total__reach_initialization.
  exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH9 as [_ Htotal].
  rewrite (sublist_self weights n_pre PreH3) in Htotal.
  pose proof (weight_values_of_explicit_require weights n_pre PreH3 PreH2) as Hweights.
  pose proof (pre_unit_sum_lower_bound__reach_initialization weights Hweights) as Hsum.
  assert (1 <= total) as Htotal_pos by lia.
  specialize (PreH2 i ltac:(lia)).
  destruct PreH2 as [Hweight | Hweight].
  - rewrite Hweight. change (0 <= total). lia.
  - rewrite Hweight. change (1 <= total). exact Htotal_pos.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH2 i ltac:(lia)).
  destruct PreH2 as [Hweight | Hweight].
  - rewrite Hweight. change (1 <= 2). lia.
  - rewrite Hweight. change (2 <= 2). lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH2 i ltac:(lia)).
  destruct PreH2 as [Hweight | Hweight].
  - rewrite Hweight. cbn. lia.
  - rewrite Hweight. cbn. lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_5 : solver_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (weight_values_of_explicit_require weights n_pre PreH3 PreH2) as Hweights.
  eapply reach_inner_finish__inner_dp_transitions.
  - exact Hweights.
  - split; [exact PreH10 | lia].
  - exact PreH12.
  - exact PreH13.
  - exact PreH1.
  - exact PreH15.
  - exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (weight_values_of_explicit_require weights n_pre PreH3 PreH2) as Hweights.
  eapply reach_inner_mark_step__inner_dp_transitions.
  - exact Hweights.
  - split; [exact PreH10 | rewrite <- PreH3; exact PreH11].
  - exact PreH12.
  - exact PreH13.
  - exact PreH1.
  - exact PreH16.
  - exact PreH7.
  - exact PreH17.
  - exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (weight_values_of_explicit_require weights n_pre PreH3 PreH2) as Hweights.
  eapply reach_inner_skip_step__inner_dp_transitions.
  - exact Hweights.
  - split; [exact PreH10 | lia].
  - exact PreH12.
  - exact PreH13.
  - exact PreH1.
  - exact PreH17.
  - exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (Hhalf_nonneg : 0 <= total / 2) by (apply Z.div_pos; lia).
  assert (Hhalf_le : total / 2 <= 100) by
    (apply Z.div_le_upper_bound; lia).
  unfold ReachTable in PreH12.
  destruct PreH12 as [_ [Hbit _]].
  apply solver_return_bridge_of_bit__final_result.
  pose proof (Hbit (total / 2) ltac:(lia)) as Hx.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (Hi : i = n_pre) by lia. subst i.
  assert (Hhalf_nonneg : 0 <= total / 2) by (apply Z.div_pos; lia).
  assert (Hhalf_le_total : total / 2 <= total) by
    (apply Z.div_le_upper_bound; lia).
  unfold PrefixUnitTotal in PreH9.
  destruct PreH9 as [_ Htotal].
  rewrite (sublist_self weights n_pre) in Htotal by lia.
  unfold ReachTable in PreH12.
  destruct PreH12 as [_ [Hbit Hreach]].
  rewrite (sublist_self weights n_pre) in Hreach by lia.
  pose proof (Hbit (total / 2) ltac:(lia)) as Hx.
  pose proof (Hreach (total / 2) ltac:(lia)) as Hselect.
  rewrite Z.rem_mod_nonneg in PreH8 by lia.
  pose proof (weight_values_of_explicit_require weights n_pre PreH3 PreH2) as Hweights.
  pose proof
    (fair_split_iff_half_selectable__final_result
       weights total Hweights Htotal PreH8) as Hfair.
  unfold Spec.
  destruct Hx as [Hx | Hx].
  - right. split; [exact Hx |].
    intro Hcontra.
    apply (proj2 Hselect).
    + apply (proj1 Hfair). exact Hcontra.
    + rewrite Hx. lia.
  - left. split; [exact Hx |].
    apply (proj2 Hfair).
    apply (proj1 Hselect).
    rewrite Hx. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_3 : solver_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia. subst i. exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_4 : solver_entail_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (total / 2 <= 100) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_5 : solver_entail_wit_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_6 : solver_entail_wit_12_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_6.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  Exists (Znth (total / 2) reach_l 0).
  split_pure_spatial.
  - cancel (IntArray.full w_pre n_pre weights).
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists 0.
  split_pure_spatial.
  - cancel (IntArray.full w_pre n_pre weights).
  - split_pures; dump_pre_spatial; assumption.
Qed.
