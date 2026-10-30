From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P007_1313A_fast_food_restaurant_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P007_1313A_fast_food_restaurant_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P007_1313A_fast_food_restaurant_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_10_split_goal_1 : solver_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  rewrite Z.mul_1_l.
  pose proof (signed_Lastnbits_range (2 ^ (s - 1)) 32 ltac:(lia)) as Hrange.
  change (-2147483648 <= signed_last_nbits (2 ^ (s - 1)) 32 < 2147483648) in Hrange.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_2 : solver_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  rewrite Z.mul_1_l.
  pose proof (signed_Lastnbits_range (2 ^ (s - 1)) 32 ltac:(lia)) as Hrange.
  change (-2147483648 <= signed_last_nbits (2 ^ (s - 1)) 32 < 2147483648) in Hrange.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_3 : solver_safety_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_4 : solver_safety_wit_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  rewrite Z.mul_1_l.
  pose proof (signed_Lastnbits_range (2 ^ d) 32 ltac:(lia)) as Hrange.
  change (-2147483648 <= signed_last_nbits (2 ^ d) 32 < 2147483648) in Hrange.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  rewrite Z.mul_1_l.
  pose proof (signed_Lastnbits_range (2 ^ d) 32 ltac:(lia)) as Hrange.
  change (-2147483648 <= signed_last_nbits (2 ^ d) 32 < 2147483648) in Hrange.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_3 : solver_safety_wit_17_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_4 : solver_safety_wit_17_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  assert (d = 0 \/ d = 1 \/ d = 2) as Hd by lia.
  destruct Hd as [-> | [-> | ->]].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia. rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia. rewrite Znth_cons by lia.
    rewrite Znth0_cons. lia.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  assert (d = 0 \/ d = 1 \/ d = 2) as Hd by lia.
  destruct Hd as [-> | [-> | ->]].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia. rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia. rewrite Znth_cons by lia.
    rewrite Znth0_cons. lia.
Qed.

Lemma proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply best_before_mask_by_bits_zero__prefix_initialization.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists 0 0 0.
  unfold repeat_Z.
  simpl.
  split_pure_spatial.
  - cancel (IntArray.full (&( "need" )) 3
      (cons 0 (cons 0 (cons 0 (@nil Z))))).
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try assumption.
    apply family_prefix_by_bits_one_zero__prefix_initialization.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcnt_bound : cnt <= s - 1).
  {
    pose proof PreH23 as Hprefix_copy.
    unfold FamilyPrefixByBits in Hprefix_copy.
    destruct Hprefix_copy as [Hcnt _]. rewrite Hcnt.
    pose proof (set_card_Z_range_bounds__dish_prefix_transitions 1 s
      (fun k => SelectedByMask fam k) ltac:(lia)) as Hcard_bound.
    exact (proj2 Hcard_bound).
  }
  Exists need_c_2 need_b_2 need_a_2.
  split_pure_spatial.
  - cancel (IntArray.full (&("need")) 3 (need_a_2 :: need_b_2 :: need_c_2 :: nil)).
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    apply family_to_selected_dish_zero_by_bits__dish_prefix_transitions.
    + lia.
    + unfold SelectedByMask.
      apply machine_mask_bit_selected__dish_prefix_transitions; try lia.
      replace (signed_last_nbits (Z.shiftl 1 (s - 1)) 32)
        with (Z.shiftl 1 (s - 1)) in PreH24.
      * exact PreH24.
      * assert (s = 1 \/ s = 2 \/ s = 3 \/ s = 4 \/
                s = 5 \/ s = 6 \/ s = 7) by lia.
        destruct H as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
          reflexivity.
    + exact PreH23.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbit : Z.testbit s d = true).
  {
    apply machine_mask_bit_selected__dish_prefix_transitions; try lia.
    replace (signed_last_nbits (Z.shiftl 1 d) 32)
      with (Z.shiftl 1 d) in PreH26.
    - exact PreH26.
    - assert (d = 0 \/ d = 1 \/ d = 2) by lia.
      destruct H as [-> | [-> | ->]]; reflexivity.
  }
  set (new := replace_Znth d
    (Znth d (need_a_2 :: need_b_2 :: need_c_2 :: nil) 0 + 1)
    (need_a_2 :: need_b_2 :: need_c_2 :: nil)).
  Exists (Znth 2 new 0) (Znth 1 new 0) (Znth 0 new 0).
  assert (Hstep := selected_dish_step_true_by_bits__dish_prefix_transitions
    fam s d cnt need_a_2 need_b_2 need_c_2 PreH13 ltac:(lia) PreH25 Hbit).
  fold new in Hstep.
  destruct (selected_dish_prefix_by_bits_bounds__dish_prefix_transitions
    fam s (d + 1) cnt (Znth 0 new 0) (Znth 1 new 0) (Znth 2 new 0)
    ltac:(lia) Hstep) as (Hnewa & Hnewb & Hnewc).
  split_pure_spatial.
  - change (IntArray.full (&("need")) 3 new |--
      IntArray.full (&("need")) 3
        (Znth 0 new 0 :: Znth 1 new 0 :: Znth 2 new 0 :: nil)).
    assert (Hnewlen : Zlength new = 3).
    { unfold new. rewrite Zlength_replace_Znth. reflexivity. }
    assert (Hnew : new =
      (Znth 0 new 0 :: Znth 1 new 0 :: Znth 2 new 0 :: nil)).
    { unfold new. assert (d = 0 \/ d = 1 \/ d = 2) by lia.
      destruct H as [-> | [-> | ->]]; reflexivity. }
    rewrite <- Hnew. cancel (IntArray.full (&("need")) 3 new).
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists need_c_2 need_b_2 need_a_2.
  split_pure_spatial.
  - cancel (IntArray.full (&("need")) 3 (need_a_2 :: need_b_2 :: need_c_2 :: nil)).
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    apply selected_dish_step_false_by_bits__dish_prefix_transitions;
      try assumption; try lia.
    apply machine_mask_bit_unselected__dish_prefix_transitions; try lia.
    replace (signed_last_nbits (Z.shiftl 1 d) 32)
      with (Z.shiftl 1 d) in PreH26.
    + exact PreH26.
    + assert (d = 0 \/ d = 1 \/ d = 2) by lia.
      destruct H as [-> | [-> | ->]]; reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists need_c_2 need_b_2 need_a_2.
  split_pure_spatial.
  - cancel (IntArray.full (&("need")) 3 (need_a_2 :: need_b_2 :: need_c_2 :: nil)).
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    replace d with 3 in PreH25 by lia.
    apply selected_dish_three_to_family_by_bits__dish_prefix_transitions.
    exact PreH25.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists need_c_2 need_b_2 need_a_2.
  split_pure_spatial.
  - cancel (IntArray.full (&("need")) 3 (need_a_2 :: need_b_2 :: need_c_2 :: nil)).
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    apply family_prefix_skip_unselected_by_bits__dish_prefix_transitions;
      try assumption; try lia.
    unfold SelectedByMask.
    intro Hselected.
    assert (Hbit : Z.testbit fam (s - 1) = false).
    {
      apply machine_mask_bit_unselected__dish_prefix_transitions; try lia.
      replace (signed_last_nbits (Z.shiftl 1 (s - 1)) 32)
        with (Z.shiftl 1 (s - 1)) in PreH24.
      - exact PreH24.
      - assert (s = 1 \/ s = 2 \/ s = 3 \/ s = 4 \/
                  s = 5 \/ s = 6 \/ s = 7) by lia.
        destruct H as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
          reflexivity.
    }
    congruence.
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_1 : solver_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (s = 8) as Hs by lia.
  subst s.
  cbn in PreH2, PreH3, PreH4.
  pose proof
    (family_prefix_by_bits_eight_mask_feeds__best_before_mask_update
       fam cnt need_a need_b need_c PreH27) as Hprefix.
  destruct Hprefix as (_ & _ & _ & _ & Hfeeds).
  eapply best_before_mask_by_bits_succ_improve__best_before_mask_update.
  - lia.
  - exact PreH16.
  - apply Hfeeds; assumption.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_1 : solver_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (s = 8) as Hs by lia.
  subst s.
  change (need_c > c_pre) in PreH1.
  unfold FamilyPrefixByBits in PreH26.
  destruct PreH26 as (_ & _ & _ & Hneed_c).
  eapply best_before_mask_by_bits_succ_keep_infeasible__best_before_mask_update.
  - lia.
  - exact PreH15.
  - intros guests Hfeeds.
    unfold MaskFeedsByBits in Hfeeds.
    destruct Hfeeds as (_ & _ & _ & Hstock_c).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_3_split_goal_1 : solver_entail_wit_6_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (s = 8) as Hs by lia.
  subst s.
  change (need_a > a_pre) in PreH1.
  unfold FamilyPrefixByBits in PreH24.
  destruct PreH24 as (_ & Hneed_a & _ & _).
  eapply best_before_mask_by_bits_succ_keep_infeasible__best_before_mask_update.
  - lia.
  - exact PreH13.
  - intros guests Hfeeds.
    unfold MaskFeedsByBits in Hfeeds.
    destruct Hfeeds as (_ & Hstock_a & _ & _).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_6_3 : solver_entail_wit_6_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_4_split_goal_1 : solver_entail_wit_6_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (s = 8) as Hs by lia.
  subst s.
  change (need_b > b_pre) in PreH1.
  unfold FamilyPrefixByBits in PreH25.
  destruct PreH25 as (_ & _ & Hneed_b & _).
  eapply best_before_mask_by_bits_succ_keep_infeasible__best_before_mask_update.
  - lia.
  - exact PreH14.
  - intros guests Hfeeds.
    unfold MaskFeedsByBits in Hfeeds.
    destruct Hfeeds as (_ & _ & Hstock_b & _).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_6_4 : solver_entail_wit_6_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_5_split_goal_1 : solver_entail_wit_6_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (s = 8) as Hs by lia.
  subst s.
  cbn in PreH2, PreH3, PreH4.
  pose proof
    (family_prefix_by_bits_eight_mask_feeds__best_before_mask_update
       fam cnt need_a need_b need_c PreH27) as Hprefix.
  destruct Hprefix as (_ & _ & _ & _ & Hfeeds).
  eapply best_before_mask_by_bits_succ_keep_feasible__best_before_mask_update.
  - lia.
  - exact PreH16.
  - apply Hfeeds; assumption.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_6_5 : solver_entail_wit_6_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_5_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hfam : fam = 128) by lia.
  rewrite Hfam in PreH12.
  apply (proj1 (best_before_mask_by_bits_128_spec__final_result
    a_pre b_pre c_pre best PreH2 PreH4 PreH6)).
  exact PreH12.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
