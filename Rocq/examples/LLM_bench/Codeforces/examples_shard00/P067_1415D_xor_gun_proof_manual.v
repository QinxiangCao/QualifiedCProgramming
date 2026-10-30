From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P067_1415D_xor_gun_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P067_1415D_xor_gun_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P067_1415D_xor_gun_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (no_equal_prefix_one__scan_setup values).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  apply PreH4.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  apply PreH3.
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
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5.
  exact H.
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
  eapply bitscan_shift_step__bit_shift_loops; eauto.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (bitscan_positive_step_bounds__bit_shift_loops
       vx_2 x bx PreH15 PreH24 PreH1 PreH21 (conj PreH22 PreH23))
    as Hbounds.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (bitscan_positive_step_bounds__bit_shift_loops
       vx_2 x bx PreH15 PreH24 PreH1 PreH21 (conj PreH22 PreH23))
    as Hbounds.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (bitscan_positive_step_bounds__bit_shift_loops
       vx_2 x bx PreH15 PreH24 PreH1 PreH21 (conj PreH22 PreH23))
    as Hbounds.
  tauto.
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
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5.
  exact H.
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
  eapply bitscan_shift_step__bit_shift_loops; eauto.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (bitscan_positive_step_bounds__bit_shift_loops
       vy_2 y by_count PreH17 PreH27 PreH1 PreH24 (conj PreH25 PreH26))
    as Hbounds.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (bitscan_positive_step_bounds__bit_shift_loops
       vy_2 y by_count PreH17 PreH27 PreH1 PreH24 (conj PreH25 PreH26))
    as Hbounds.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (bitscan_positive_step_bounds__bit_shift_loops
       vy_2 y by_count PreH17 PreH27 PreH1 PreH24 (conj PreH25 PreH26))
    as Hbounds.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply bitscan_shift_step__bit_shift_loops; eauto.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (bitscan_positive_step_bounds__bit_shift_loops
       vz_2 z bz PreH19 PreH30 PreH1 PreH27 (conj PreH28 PreH29))
    as Hbounds.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (bitscan_positive_step_bounds__bit_shift_loops
       vz_2 z bz PreH19 PreH30 PreH1 PreH27 (conj PreH28 PreH29))
    as Hbounds.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_4 : solver_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (bitscan_positive_step_bounds__bit_shift_loops
       vz_2 z bz PreH19 PreH30 PreH1 PreH27 (conj PreH28 PreH29))
    as Hbounds.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_8_1_split_goal_1 : solver_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply no_equal_prefix_step__equal_bit_boundary.
  - exact PreH32.
  - intros [Hequal_xy Hequal_yz].
    assert (Hbx : bx = Z.log2 vx).
    { eapply bitscan_terminal_log2__equal_bit_boundary.
      - lia.
      - lia.
      - unfold BitScanState in *; lia. }
    assert (Hby : by_count = Z.log2 vy).
    { eapply bitscan_terminal_log2__equal_bit_boundary.
      - lia.
      - lia.
      - unfold BitScanState in *; lia. }
    apply PreH1.
    rewrite Hbx, Hby, PreH10, PreH11.
    exact Hequal_xy.
Qed.

Lemma proof_of_solver_entail_wit_8_1_split_goal_2 : solver_entail_wit_8_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8_1_split_goal_3 : solver_entail_wit_8_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_8_2_split_goal_1 : solver_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply no_equal_prefix_step__equal_bit_boundary.
  - exact PreH33.
  - intros [Hequal_xy Hequal_yz].
    assert (Hby : by_count = Z.log2 vy).
    { eapply bitscan_terminal_log2__equal_bit_boundary.
      - lia.
      - lia.
      - unfold BitScanState in *; lia. }
    assert (Hbz : bz = Z.log2 vz).
    { eapply bitscan_terminal_log2__equal_bit_boundary.
      - lia.
      - lia.
      - unfold BitScanState in *; lia. }
    apply PreH1.
    rewrite Hby, Hbz, PreH12, PreH13.
    exact Hequal_yz.
Qed.

Lemma proof_of_solver_entail_wit_8_2_split_goal_2 : solver_entail_wit_8_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_8_2_split_goal_3 : solver_entail_wit_8_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply prefix_xor_table_zero__prefix_table.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_3 : solver_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_1 : solver_entail_wit_10_split_goal_1.
Proof. Abort.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength (&("pre")) 64
    (replace_Znth (i + 1)
      (Z.lxor (Znth i prefixes_2 0) (Znth i values 0)) prefixes_2)).
  Intros.
  Exists (replace_Znth (i + 1)
    (Z.lxor (Znth i prefixes_2 0) (Znth i values 0)) prefixes_2).
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (IntArray.full (&("pre")) 64
      (replace_Znth (i + 1)
        (Z.lxor (Znth i prefixes_2 0) (Znth i values 0)) prefixes_2)).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    eapply prefix_xor_table_replace_step__prefix_table.
    + exact PreH9.
    + lia.
    + rewrite Zlength_replace_Znth in H.
      lia.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply brute_search_state_origin__prefix_table.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace n_pre with i by lia.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_3 : solver_entail_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_4 : solver_entail_wit_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH5.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH5 k H).
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_2 : solver_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH5 k H).
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_1 : solver_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply brute_search_state_next_l__brute_search_cursor; eauto.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_2 : solver_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_3 : solver_entail_wit_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH5 k H).
Qed.

Lemma proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply brute_search_state_next_mid__brute_search_cursor; eauto.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_2 : solver_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_3 : solver_entail_wit_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH5 k H).
Qed.

Lemma proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_16_1_split_goal_1 : solver_entail_wit_16_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (prefix_table_destructive_window__brute_search_window
    values prefixes_2 n_pre l mid r PreH16 ltac:(lia) ltac:(lia)
    ltac:(lia) PreH2) as Hwindow.
  pose proof (brute_search_state_consume__brute_search_window
    values l mid r ans PreH17) as Hconsume.
  destruct Hconsume as [_ [Himproving _]].
  apply Himproving; auto.
Qed.

Lemma proof_of_solver_entail_wit_16_1 : solver_entail_wit_16_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_2_split_goal_1 : solver_entail_wit_16_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnot : ~ DestructiveWindow values l mid r).
  {
    intros [_ [_ Hxor]].
    specialize (PreH15 l ltac:(lia)) as Hl.
    specialize (PreH15 (mid + 1) ltac:(lia)) as Hmid.
    specialize (PreH15 (r + 1) ltac:(lia)) as Hright.
    rewrite <- Hl, <- Hmid, <- Hright in Hxor.
    lia.
  }
  pose proof (brute_search_state_consume__brute_search_window
    values l mid r ans PreH16) as Hconsume.
  destruct Hconsume as [Habsent _].
  apply Habsent; exact Hnot.
Qed.

Lemma proof_of_solver_entail_wit_16_2 : solver_entail_wit_16_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_16_3_split_goal_1 : solver_entail_wit_16_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (prefix_table_destructive_window__brute_search_window
    values prefixes_2 n_pre l mid r PreH16 ltac:(lia) ltac:(lia)
    ltac:(lia) PreH2) as Hwindow.
  pose proof (brute_search_state_consume__brute_search_window
    values l mid r ans PreH17) as Hconsume.
  destruct Hconsume as [_ [_ Hnonimproving]].
  apply Hnonimproving.
  - exact Hwindow.
  - lia.
  - intro Heq; lia.
Qed.

Lemma proof_of_solver_entail_wit_16_3 : solver_entail_wit_16_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_16_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (finished_window_search_spec_none__final_search_result values n_pre).
  - lia.
  - exact PreH3.
  - subst ans.
    replace l with n_pre in PreH13 by lia.
    exact PreH13.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (finished_window_search_spec_min__final_search_result
    values n_pre ans).
  - lia.
  - exact PreH3.
  - exact PreH1.
  - replace l with n_pre in PreH13 by lia.
    exact PreH13.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exfalso.
  pose proof
    (sorted_no_equal_bit_triples_length_bound__large_input_final
      values n_pre i PreH3 PreH4 PreH6 PreH7 PreH8 PreH9 PreH2 PreH10)
    as Hlength_bound.
  lia.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbx : bx = Z.log2 vx).
  { eapply bitscan_terminal_log2__equal_bit_boundary.
    - lia.
    - lia.
    - unfold BitScanState in *; lia. }
  assert (Hby : by_count = Z.log2 vy).
  { eapply bitscan_terminal_log2__equal_bit_boundary.
    - lia.
    - lia.
    - unfold BitScanState in *; lia. }
  assert (Hbz : bz = Z.log2 vz).
  { eapply bitscan_terminal_log2__equal_bit_boundary.
    - lia.
    - lia.
    - unfold BitScanState in *; lia. }
  assert (Hxy : Z.log2 vx = Z.log2 vy).
  { rewrite <- Hbx, <- Hby.
    exact PreH2. }
  assert (Hyz : Z.log2 vy = Z.log2 vz).
  { rewrite <- Hby, <- Hbz.
    exact PreH1. }
  eapply equal_adjacent_bits_spec_one__equal_bit_boundary
    with (n := n_pre) (i := i) (vx := vx) (vy := vy) (vz := vz);
    eauto; try lia.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_4_split_goal_1.
Qed.
