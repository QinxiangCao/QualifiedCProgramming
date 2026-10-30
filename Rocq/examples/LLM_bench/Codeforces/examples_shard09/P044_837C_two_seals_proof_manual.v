From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P044_837C_two_seals_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P044_837C_two_seals_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_lib.
Local Open Scope sac.

Lemma proof_of_fits_return_wit_1_split_goal_1 : fits_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold FitsDims, TwoFit in *.
  simpl in *.
  rewrite Z.max_l in * by lia.
  lia.
Qed.

Lemma proof_of_fits_return_wit_1 : fits_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_fits_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_fits_return_wit_2_split_goal_1 : fits_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold FitsDims, TwoFit in *.
  simpl in *.
  rewrite Z.max_r in * by lia.
  lia.
Qed.

Lemma proof_of_fits_return_wit_2 : fits_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_fits_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_fits_return_wit_3_split_goal_1 : fits_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold FitsDims, TwoFit in *.
  simpl in *.
  lia.
Qed.

Lemma proof_of_fits_return_wit_3 : fits_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_fits_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_fits_return_wit_4_split_goal_1 : fits_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold FitsDims, TwoFit in *.
  simpl in *.
  lia.
Qed.

Lemma proof_of_fits_return_wit_4 : fits_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_fits_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_fits_return_wit_5_split_goal_1 : fits_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold FitsDims, TwoFit in *.
  simpl in *.
  lia.
Qed.

Lemma proof_of_fits_return_wit_5 : fits_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_fits_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_fits_return_wit_6_split_goal_1 : fits_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold FitsDims, TwoFit.
  right.
  split.
  - apply Z.max_lub.
    + exact (Z.le_trans _ _ _ PreH2 PreH1).
    + exact PreH1.
  - exact PreH3.
Qed.

Lemma proof_of_fits_return_wit_6 : fits_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_fits_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_fits_return_wit_7_split_goal_1 : fits_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold FitsDims, TwoFit.
  right.
  split.
  - assert (Hle : w2_pre <= w1_pre) by lia.
    apply Z.max_lub.
    + exact PreH1.
    + exact (Z.le_trans _ _ _ Hle PreH1).
  - exact PreH3.
Qed.

Lemma proof_of_fits_return_wit_7 : fits_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_fits_return_wit_7_split_goal_1.
Qed.

Lemma proof_of_fits_return_wit_8_split_goal_1 : fits_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold FitsDims, TwoFit.
  left.
  split.
  - exact PreH3.
  - apply Z.max_lub.
    + exact (Z.le_trans _ _ _ PreH2 PreH1).
    + exact PreH1.
Qed.

Lemma proof_of_fits_return_wit_8 : fits_return_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_fits_return_wit_8_split_goal_1.
Qed.

Lemma proof_of_fits_return_wit_9_split_goal_1 : fits_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold FitsDims, TwoFit.
  left.
  split.
  - exact PreH3.
  - assert (Hle : h2_pre <= h1_pre) by lia.
    apply Z.max_lub.
    + exact PreH1.
    + exact (Z.le_trans _ _ _ Hle PreH1).
Qed.

Lemma proof_of_fits_return_wit_9 : fits_return_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_fits_return_wit_9_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_1 : solver_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 i ltac:(lia)) as Hi.
  pose proof (PreH19 j ltac:(lia)) as Hj.
  destruct Hi as [[[[[Hixlo Hixhi] Hiylo] Hiyhi] Hix] Hiy].
  destruct Hj as [[[[[Hjxlo Hjxhi] Hjylo] Hjyhi] Hjx] Hjy].
  rewrite Hix, Hiy, Hjx, Hjy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_2 : solver_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 i ltac:(lia)) as Hi.
  pose proof (PreH19 j ltac:(lia)) as Hj.
  destruct Hi as [[[[[Hixlo Hixhi] Hiylo] Hiyhi] Hix] Hiy].
  destruct Hj as [[[[[Hjxlo Hjxhi] Hjylo] Hjyhi] Hjx] Hjy].
  rewrite Hix, Hiy, Hjx, Hjy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_1 : solver_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 j ltac:(lia)) as Hj.
  destruct Hj as [[[[[Hjxlo Hjxhi] Hjylo] Hjyhi] Hjx] Hjy].
  rewrite Hjx, Hjy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_2 : solver_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 j ltac:(lia)) as Hj.
  destruct Hj as [[[[[Hjxlo Hjxhi] Hjylo] Hjyhi] Hjx] Hjy].
  rewrite Hjx, Hjy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_1 : solver_safety_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 i ltac:(lia)) as Hi.
  destruct Hi as [[[[[Hixlo Hixhi] Hiylo] Hiyhi] Hix] Hiy].
  rewrite Hix, Hiy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 i ltac:(lia)) as Hi.
  destruct Hi as [[[[[Hixlo Hixhi] Hiylo] Hiyhi] Hix] Hiy].
  rewrite Hix, Hiy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_1 : solver_safety_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 i ltac:(lia)) as Hi.
  pose proof (PreH19 j ltac:(lia)) as Hj.
  destruct Hi as [[[[[Hixlo Hixhi] Hiylo] Hiyhi] Hix] Hiy].
  destruct Hj as [[[[[Hjxlo Hjxhi] Hjylo] Hjyhi] Hjx] Hjy].
  rewrite Hix, Hiy, Hjx, Hjy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_2 : solver_safety_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 i ltac:(lia)) as Hi.
  pose proof (PreH19 j ltac:(lia)) as Hj.
  destruct Hi as [[[[[Hixlo Hixhi] Hiylo] Hiyhi] Hix] Hiy].
  destruct Hj as [[[[[Hjxlo Hjxhi] Hjylo] Hjyhi] Hjx] Hjy].
  rewrite Hix, Hiy, Hjx, Hjy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_27_split_goal_1 : solver_safety_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 j ltac:(lia)) as Hj.
  destruct Hj as [[[[[Hjxlo Hjxhi] Hjylo] Hjyhi] Hjx] Hjy].
  rewrite Hjx, Hjy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_27_split_goal_2 : solver_safety_wit_27_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 j ltac:(lia)) as Hj.
  destruct Hj as [[[[[Hjxlo Hjxhi] Hjylo] Hjyhi] Hjx] Hjy].
  rewrite Hjx, Hjy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_27_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_27_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_28_split_goal_1 : solver_safety_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 i ltac:(lia)) as Hi.
  destruct Hi as [[[[[Hixlo Hixhi] Hiylo] Hiyhi] Hix] Hiy].
  rewrite Hix, Hiy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_28_split_goal_2 : solver_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH19 i ltac:(lia)) as Hi.
  destruct Hi as [[[[[Hixlo Hixhi] Hiylo] Hiyhi] Hix] Hiy].
  rewrite Hix, Hiy.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_29_split_goal_1 : solver_safety_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 i ltac:(lia)) as Hi;
    pose proof (PreH19 j ltac:(lia)) as Hj;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_29_split_goal_2 : solver_safety_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 i ltac:(lia)) as Hi;
    pose proof (PreH19 j ltac:(lia)) as Hj;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_29_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_29_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_30_split_goal_1 : solver_safety_wit_30_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 j ltac:(lia)) as Hj;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_30_split_goal_2 : solver_safety_wit_30_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 j ltac:(lia)) as Hj;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_30_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_30_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_31_split_goal_1 : solver_safety_wit_31_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 i ltac:(lia)) as Hi;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_31_split_goal_2 : solver_safety_wit_31_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 i ltac:(lia)) as Hi;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_31_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_31_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_32_split_goal_1 : solver_safety_wit_32_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 i ltac:(lia)) as Hi;
    pose proof (PreH19 j ltac:(lia)) as Hj;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_32_split_goal_2 : solver_safety_wit_32_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 i ltac:(lia)) as Hi;
    pose proof (PreH19 j ltac:(lia)) as Hj;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_32_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_32_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_33_split_goal_1 : solver_safety_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 j ltac:(lia)) as Hj;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_33_split_goal_2 : solver_safety_wit_33_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 j ltac:(lia)) as Hj;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_33_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_33_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_34_split_goal_1 : solver_safety_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 i ltac:(lia)) as Hi;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_34_split_goal_2 : solver_safety_wit_34_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    pose proof (PreH19 i ltac:(lia)) as Hi;
    nia).
Qed.

Lemma proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_34_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_34_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply best_before_initial__invariant_init.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH7 k ltac:(assumption)).
  specialize (PreH13 k ltac:(assumption)).
  tauto.
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
  apply PreH13.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH13.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH13.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hj : j = n_pre) by lia.
  rewrite Hj in PreH20.
  eapply best_before_finish_j__loop_transitions; eauto.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply PreH13; eauto.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hri : ri = 2) by lia.
  rewrite Hri in PreH21.
  apply best_before_finish_ri__loop_transitions.
  exact PreH21.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply PreH13; eauto.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hrj : rj = 2) by lia.
  rewrite Hrj in PreH23.
  apply best_before_finish_rj__loop_transitions.
  exact PreH23.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply PreH13; eauto.
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
  assert (ri = 1) by lia.
  assert (rj = 1) by lia.
  subst ri rj.
  eapply best_before_take_current__choice_improve.
  - exact PreH30.
  - pose proof (PreH20 i ltac:(lia)) as Hi.
    pose proof (PreH20 j ltac:(lia)) as Hj.
    rewrite (Znth_indep seals i __default__Prod_Z_Z (0, 0)) in * by lia.
    rewrite (Znth_indep seals j __default__Prod_Z_Z (0, 0)) in * by lia.
    destruct Hi as [[[[[Hxi_lo Hxi_hi] Hyi_lo] Hyi_hi] Hxi] Hyi].
    destruct Hj as [[[[[Hxj_lo Hxj_hi] Hyj_lo] Hyj_hi] Hxj] Hyj].
    unfold SealChoice, rotate_seal.
    cbn.
    repeat split; try lia.
    + unfold FitsDims in PreH3.
      rewrite Hxi, Hyi, Hxj, Hyj in PreH3.
      rewrite PreH15, PreH16.
      exact PreH3.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_2 : solver_entail_wit_10_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH20 i ltac:(lia)) as Hi.
  pose proof (PreH20 j ltac:(lia)) as Hj.
  rewrite (Znth_indep seals i __default__Prod_Z_Z (0, 0)) in * by lia.
  rewrite (Znth_indep seals j __default__Prod_Z_Z (0, 0)) in * by lia.
  destruct Hi as [[[[[Hxi_lo Hxi_hi] Hyi_lo] Hyi_hi] Hxi] Hyi].
  destruct Hj as [[[[[Hxj_lo Hxj_hi] Hyj_lo] Hyj_hi] Hxj] Hyj].
  rewrite Hxi, Hyi, Hxj, Hyj.
  nia.
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (ri = 1) by lia.
  assert (rj = 0) by lia.
  subst ri rj.
  eapply best_before_take_current__choice_improve.
  - exact PreH30.
  - pose proof (PreH20 i ltac:(lia)) as Hi.
    pose proof (PreH20 j ltac:(lia)) as Hj.
    rewrite (Znth_indep seals i __default__Prod_Z_Z (0, 0)) in * by lia.
    rewrite (Znth_indep seals j __default__Prod_Z_Z (0, 0)) in * by lia.
    destruct Hi as [[[[[Hxi_lo Hxi_hi] Hyi_lo] Hyi_hi] Hxi] Hyi].
    destruct Hj as [[[[[Hxj_lo Hxj_hi] Hyj_lo] Hyj_hi] Hxj] Hyj].
    unfold SealChoice, rotate_seal.
    cbn.
    repeat split; try lia.
    unfold FitsDims in PreH3.
    rewrite Hxi, Hyi, Hxj, Hyj in PreH3.
    rewrite PreH15, PreH16.
    exact PreH3.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_2 : solver_entail_wit_10_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH20 i ltac:(lia)) as Hi.
  pose proof (PreH20 j ltac:(lia)) as Hj.
  rewrite (Znth_indep seals i __default__Prod_Z_Z (0, 0)) in * by lia.
  rewrite (Znth_indep seals j __default__Prod_Z_Z (0, 0)) in * by lia.
  destruct Hi as [[[[[Hxi_lo Hxi_hi] Hyi_lo] Hyi_hi] Hxi] Hyi].
  destruct Hj as [[[[[Hxj_lo Hxj_hi] Hyj_lo] Hyj_hi] Hxj] Hyj].
  rewrite Hxi, Hyi, Hxj, Hyj.
  nia.
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10_3_split_goal_1 : solver_entail_wit_10_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (ri = 0) by lia.
  assert (rj = 1) by lia.
  subst ri rj.
  eapply best_before_take_current__choice_improve.
  - exact PreH30.
  - pose proof (PreH20 i ltac:(lia)) as Hi.
    pose proof (PreH20 j ltac:(lia)) as Hj.
    rewrite (Znth_indep seals i __default__Prod_Z_Z (0, 0)) in * by lia.
    rewrite (Znth_indep seals j __default__Prod_Z_Z (0, 0)) in * by lia.
    destruct Hi as [[[[[Hxi_lo Hxi_hi] Hyi_lo] Hyi_hi] Hxi] Hyi].
    destruct Hj as [[[[[Hxj_lo Hxj_hi] Hyj_lo] Hyj_hi] Hxj] Hyj].
    unfold SealChoice, rotate_seal.
    cbn.
    repeat split; try lia.
    unfold FitsDims in PreH3.
    rewrite Hxi, Hyi, Hxj, Hyj in PreH3.
    rewrite PreH15, PreH16.
    exact PreH3.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_10_3_split_goal_2 : solver_entail_wit_10_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH20 i ltac:(lia)) as Hi.
  pose proof (PreH20 j ltac:(lia)) as Hj.
  rewrite (Znth_indep seals i __default__Prod_Z_Z (0, 0)) in * by lia.
  rewrite (Znth_indep seals j __default__Prod_Z_Z (0, 0)) in * by lia.
  destruct Hi as [[[[[Hxi_lo Hxi_hi] Hyi_lo] Hyi_hi] Hxi] Hyi].
  destruct Hj as [[[[[Hxj_lo Hxj_hi] Hyj_lo] Hyj_hi] Hxj] Hyj].
  rewrite Hxi, Hyi, Hxj, Hyj.
  nia.
Qed.

Lemma proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10_4_split_goal_1 : solver_entail_wit_10_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (ri = 0) by lia.
  assert (rj = 0) by lia.
  subst ri rj.
  eapply best_before_take_current__choice_improve.
  - exact PreH30.
  - pose proof (PreH20 i ltac:(lia)) as Hi.
    pose proof (PreH20 j ltac:(lia)) as Hj.
    rewrite (Znth_indep seals i __default__Prod_Z_Z (0, 0)) in * by lia.
    rewrite (Znth_indep seals j __default__Prod_Z_Z (0, 0)) in * by lia.
    destruct Hi as [[[[[Hxi_lo Hxi_hi] Hyi_lo] Hyi_hi] Hxi] Hyi].
    destruct Hj as [[[[[Hxj_lo Hxj_hi] Hyj_lo] Hyj_hi] Hxj] Hyj].
    unfold SealChoice, rotate_seal.
    cbn.
    repeat split; try lia.
    unfold FitsDims in PreH3.
    rewrite Hxi, Hyi, Hxj, Hyj in PreH3.
    rewrite PreH15, PreH16.
    exact PreH3.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_10_4_split_goal_2 : solver_entail_wit_10_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH20 i ltac:(lia)) as Hi.
  pose proof (PreH20 j ltac:(lia)) as Hj.
  rewrite (Znth_indep seals i __default__Prod_Z_Z (0, 0)) in * by lia.
  rewrite (Znth_indep seals j __default__Prod_Z_Z (0, 0)) in * by lia.
  destruct Hi as [[[[[Hxi_lo Hxi_hi] Hyi_lo] Hyi_hi] Hxi] Hyi].
  destruct Hj as [[[[[Hxj_lo Hxj_hi] Hyj_lo] Hyj_hi] Hxj] Hyj].
  rewrite Hxi, Hyi, Hxj, Hyj.
  nia.
Qed.

Lemma proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10_5_split_goal_1 : solver_entail_wit_10_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply best_before_skip_dominated__choice_retain_fit with
    (area := Znth i ys_spec_2 0 * Znth i xs_spec_2 0 +
             Znth j ys_spec_2 0 * Znth j xs_spec_2 0).
  - exact PreH30.
  - unfold SealChoice, rotate_seal, FitsDims in *.
    pose proof (PreH20 i ltac:(lia)) as Hi.
    pose proof (PreH20 j ltac:(lia)) as Hj.
    destruct Hi as (((((Hix & _) & Hiy) & _) & Hxi) & Hyi).
    destruct Hj as (((((Hjx & _) & Hjy) & _) & Hxj) & Hyj).
    assert (Hdefault_i : Znth i seals __default__Prod_Z_Z =
                         Znth i seals (0, 0)) by (apply Znth_indep; lia).
    assert (Hdefault_j : Znth j seals __default__Prod_Z_Z =
                         Znth j seals (0, 0)) by (apply Znth_indep; lia).
    rewrite Hdefault_i in Hxi, Hyi.
    rewrite Hdefault_j in Hxj, Hyj.
    repeat split; try lia.
    + destruct (Z.eq_dec ri 0); [contradiction |].
      destruct (Z.eq_dec rj 0); [contradiction |].
      simpl.
      rewrite <- Hxi, <- Hyi, <- Hxj, <- Hyj.
      rewrite PreH15, PreH16.
      exact PreH3.
    + destruct (Z.eq_dec ri 0); [contradiction |].
      destruct (Z.eq_dec rj 0); [contradiction |].
      simpl. rewrite <- Hyi, <- Hxi, <- Hyj, <- Hxj. reflexivity.
  - exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_10_5 : solver_entail_wit_10_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_6_split_goal_1 : solver_entail_wit_10_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- PreH4.
  apply best_before_skip_dominated__choice_retain_fit with
    (area := Znth i ys_spec_2 0 * Znth i xs_spec_2 0 +
             Znth j xs_spec_2 0 * Znth j ys_spec_2 0).
  - exact PreH30.
  - unfold SealChoice, rotate_seal, FitsDims in *.
    pose proof (PreH20 i ltac:(lia)) as Hi.
    pose proof (PreH20 j ltac:(lia)) as Hj.
    destruct Hi as (((((_ & _) & _) & _) & Hxi) & Hyi).
    destruct Hj as (((((_ & _) & _) & _) & Hxj) & Hyj).
    assert (Hdefault_i : Znth i seals __default__Prod_Z_Z =
                         Znth i seals (0, 0)) by (apply Znth_indep; lia).
    assert (Hdefault_j : Znth j seals __default__Prod_Z_Z =
                         Znth j seals (0, 0)) by (apply Znth_indep; lia).
    rewrite Hdefault_i in Hxi, Hyi.
    rewrite Hdefault_j in Hxj, Hyj.
    repeat split; try lia.
    + destruct (Z.eq_dec ri 0); [contradiction |].
      destruct (Z.eq_dec rj 0); [| contradiction].
      simpl.
      rewrite <- Hyi, <- Hxi.
      rewrite (surjective_pairing (Znth j seals (0, 0))).
      rewrite <- Hxj, <- Hyj.
      rewrite PreH15, PreH16.
      exact PreH3.
    + destruct (Z.eq_dec ri 0); [contradiction |].
      destruct (Z.eq_dec rj 0); [| contradiction].
      simpl. rewrite <- Hyi, <- Hxi, <- Hxj, <- Hyj. reflexivity.
  - exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_10_6 : solver_entail_wit_10_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_6_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_7_split_goal_1 : solver_entail_wit_10_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- PreH6.
  apply best_before_skip_dominated__choice_retain_fit with
    (area := Znth i xs_spec_2 0 * Znth i ys_spec_2 0 +
             Znth j ys_spec_2 0 * Znth j xs_spec_2 0).
  - exact PreH30.
  - unfold SealChoice, rotate_seal, FitsDims in *.
    pose proof (PreH20 i ltac:(lia)) as Hi.
    pose proof (PreH20 j ltac:(lia)) as Hj.
    destruct Hi as (((((_ & _) & _) & _) & Hxi) & Hyi).
    destruct Hj as (((((_ & _) & _) & _) & Hxj) & Hyj).
    assert (Hdefault_i : Znth i seals __default__Prod_Z_Z =
                         Znth i seals (0, 0)) by (apply Znth_indep; lia).
    assert (Hdefault_j : Znth j seals __default__Prod_Z_Z =
                         Znth j seals (0, 0)) by (apply Znth_indep; lia).
    rewrite Hdefault_i in Hxi, Hyi.
    rewrite Hdefault_j in Hxj, Hyj.
    repeat split; try lia.
    + destruct (Z.eq_dec ri 0); [| contradiction].
      destruct (Z.eq_dec rj 0); [contradiction |].
      simpl.
      rewrite (surjective_pairing (Znth i seals (0, 0))).
      rewrite <- Hxi, <- Hyi, <- Hyj, <- Hxj.
      rewrite PreH15, PreH16.
      exact PreH3.
    + destruct (Z.eq_dec ri 0); [| contradiction].
      destruct (Z.eq_dec rj 0); [contradiction |].
      simpl. rewrite <- Hxi, <- Hyi, <- Hyj, <- Hxj. reflexivity.
  - exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_10_7 : solver_entail_wit_10_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_7_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_8_split_goal_1 : solver_entail_wit_10_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst ri. subst rj.
  apply best_before_skip_dominated__choice_retain_fit with
    (area := Znth i xs_spec_2 0 * Znth i ys_spec_2 0 +
             Znth j xs_spec_2 0 * Znth j ys_spec_2 0).
  - exact PreH30.
  - unfold SealChoice, rotate_seal, FitsDims in *.
    pose proof (PreH20 i ltac:(lia)) as Hi.
    pose proof (PreH20 j ltac:(lia)) as Hj.
    destruct Hi as (((((_ & _) & _) & _) & Hxi) & Hyi).
    destruct Hj as (((((_ & _) & _) & _) & Hxj) & Hyj).
    assert (Hdefault_i : Znth i seals __default__Prod_Z_Z =
                         Znth i seals (0, 0)) by (apply Znth_indep; lia).
    assert (Hdefault_j : Znth j seals __default__Prod_Z_Z =
                         Znth j seals (0, 0)) by (apply Znth_indep; lia).
    rewrite Hdefault_i in Hxi, Hyi.
    rewrite Hdefault_j in Hxj, Hyj.
    repeat split; try lia.
    + simpl.
      rewrite (surjective_pairing (Znth i seals (0, 0))).
      rewrite (surjective_pairing (Znth j seals (0, 0))).
      rewrite <- Hxi, <- Hyi, <- Hxj, <- Hyj.
      rewrite PreH15, PreH16.
      exact PreH3.
    + simpl. rewrite <- Hxi, <- Hyi, <- Hxj, <- Hyj. reflexivity.
  - exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_10_8 : solver_entail_wit_10_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_8_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_9_split_goal_1 : solver_entail_wit_10_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply best_before_skip_invalid__choice_retain_invalid.
  - exact PreH29.
  - intros area Hchoice.
    assert (ri = 1) by lia.
    assert (rj = 1) by lia.
    subst ri rj.
    pose proof (PreH19 i ltac:(lia)) as Hiobs.
    pose proof (PreH19 j ltac:(lia)) as Hjobs.
    assert (Hxi : Znth i xs_spec_2 0 = fst (Znth i seals (0, 0))).
    { rewrite (Znth_indep seals i (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hyi : Znth i ys_spec_2 0 = snd (Znth i seals (0, 0))).
    { rewrite (Znth_indep seals i (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hxj : Znth j xs_spec_2 0 = fst (Znth j seals (0, 0))).
    { rewrite (Znth_indep seals j (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hyj : Znth j ys_spec_2 0 = snd (Znth j seals (0, 0))).
    { rewrite (Znth_indep seals j (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    unfold SealChoice, rotate_seal in Hchoice.
    simpl in Hchoice.
    destruct Hchoice as [_ [_ [_ [_ [Hfit _]]]]].
    apply PreH2.
    unfold FitsDims.
    rewrite Hyi, Hxi, Hyj, Hxj.
    subst a_pre b_pre.
    exact Hfit.
Qed.

Lemma proof_of_solver_entail_wit_10_9 : solver_entail_wit_10_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_9_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_10_split_goal_1 : solver_entail_wit_10_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst rj.
  eapply best_before_skip_invalid__choice_retain_invalid.
  - exact PreH29.
  - intros area Hchoice.
    assert (ri = 1) by lia.
    subst ri.
    pose proof (PreH19 i ltac:(lia)) as Hiobs.
    pose proof (PreH19 j ltac:(lia)) as Hjobs.
    assert (Hxi : Znth i xs_spec_2 0 = fst (Znth i seals (0, 0))).
    { rewrite (Znth_indep seals i (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hyi : Znth i ys_spec_2 0 = snd (Znth i seals (0, 0))).
    { rewrite (Znth_indep seals i (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hxj : Znth j xs_spec_2 0 = fst (Znth j seals (0, 0))).
    { rewrite (Znth_indep seals j (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hyj : Znth j ys_spec_2 0 = snd (Znth j seals (0, 0))).
    { rewrite (Znth_indep seals j (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    unfold SealChoice, rotate_seal in Hchoice.
    simpl in Hchoice.
    destruct Hchoice as [_ [_ [_ [_ [Hfit _]]]]].
    apply PreH2.
    unfold FitsDims.
    rewrite Hyi, Hxi, Hxj, Hyj.
    subst a_pre b_pre.
    exact Hfit.
Qed.

Lemma proof_of_solver_entail_wit_10_10 : solver_entail_wit_10_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_10_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_11_split_goal_1 : solver_entail_wit_10_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst ri.
  eapply best_before_skip_invalid__choice_retain_invalid.
  - exact PreH29.
  - intros area Hchoice.
    assert (rj = 1) by lia.
    subst rj.
    pose proof (PreH19 i ltac:(lia)) as Hiobs.
    pose proof (PreH19 j ltac:(lia)) as Hjobs.
    assert (Hxi : Znth i xs_spec_2 0 = fst (Znth i seals (0, 0))).
    { rewrite (Znth_indep seals i (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hyi : Znth i ys_spec_2 0 = snd (Znth i seals (0, 0))).
    { rewrite (Znth_indep seals i (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hxj : Znth j xs_spec_2 0 = fst (Znth j seals (0, 0))).
    { rewrite (Znth_indep seals j (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hyj : Znth j ys_spec_2 0 = snd (Znth j seals (0, 0))).
    { rewrite (Znth_indep seals j (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    unfold SealChoice, rotate_seal in Hchoice.
    simpl in Hchoice.
    destruct Hchoice as [_ [_ [_ [_ [Hfit _]]]]].
    apply PreH2.
    unfold FitsDims.
    rewrite Hxi, Hyi, Hyj, Hxj.
    subst a_pre b_pre.
    exact Hfit.
Qed.

Lemma proof_of_solver_entail_wit_10_11 : solver_entail_wit_10_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_11_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_12_split_goal_1 : solver_entail_wit_10_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst ri rj.
  eapply best_before_skip_invalid__choice_retain_invalid.
  - exact PreH29.
  - intros area Hchoice.
    pose proof (PreH19 i ltac:(lia)) as Hiobs.
    pose proof (PreH19 j ltac:(lia)) as Hjobs.
    assert (Hxi : Znth i xs_spec_2 0 = fst (Znth i seals (0, 0))).
    { rewrite (Znth_indep seals i (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hyi : Znth i ys_spec_2 0 = snd (Znth i seals (0, 0))).
    { rewrite (Znth_indep seals i (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hxj : Znth j xs_spec_2 0 = fst (Znth j seals (0, 0))).
    { rewrite (Znth_indep seals j (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    assert (Hyj : Znth j ys_spec_2 0 = snd (Znth j seals (0, 0))).
    { rewrite (Znth_indep seals j (0, 0) __default__Prod_Z_Z) by lia. tauto. }
    unfold SealChoice, rotate_seal in Hchoice.
    simpl in Hchoice.
    destruct Hchoice as [_ [_ [_ [_ [Hfit _]]]]].
    apply PreH2.
    unfold FitsDims.
    rewrite Hxi, Hyi, Hxj, Hyj.
    subst a_pre b_pre.
    exact Hfit.
Qed.

Lemma proof_of_solver_entail_wit_10_12 : solver_entail_wit_10_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_12_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH13 i H) as Hi.
  tauto.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_2 : solver_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply best_before_complete__final_result with (n := i_2); eauto.
  lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_2.
Qed.
