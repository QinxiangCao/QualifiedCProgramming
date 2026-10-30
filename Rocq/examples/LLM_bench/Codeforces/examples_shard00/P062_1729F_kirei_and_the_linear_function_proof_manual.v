From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P062_1729F_kirei_and_the_linear_function_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P062_1729F_kirei_and_the_linear_function_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P062_1729F_kirei_and_the_linear_function_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_6_split_goal_1 : solver_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH20 i ltac:(lia)) as Hprefix.
  pose proof (PreH10 i ltac:(lia)) as Hdigit.
  dump_pre_spatial.
  rewrite PreH4.
  rewrite Znth_app_left__arithmetic_safety by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_6_split_goal_2 : solver_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH20 i ltac:(lia)) as Hprefix.
  pose proof (PreH10 i ltac:(lia)) as Hdigit.
  dump_pre_spatial.
  rewrite PreH4.
  rewrite Znth_app_left__arithmetic_safety by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH20 i ltac:(lia)) as Hprefix.
  pose proof (PreH10 i ltac:(lia)) as Hdigit.
  dump_pre_spatial.
  rewrite PreH4.
  rewrite Znth_app_left__arithmetic_safety by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH20 i ltac:(lia)) as Hprefix.
  pose proof (PreH10 i ltac:(lia)) as Hdigit.
  dump_pre_spatial.
  rewrite PreH4.
  rewrite Znth_app_left__arithmetic_safety by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_1 : solver_safety_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH21 i (i + w_pre) ltac:(lia)) as Hwindow.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH21 i (i + w_pre) ltac:(lia)) as Hwindow.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_57_split_goal_1 : solver_safety_wit_57_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH15 z ltac:(lia)) as Hquery.
  decompose [and] Hquery; clear Hquery.
  pose proof
    (PreH21 (Znth z ql_data 0 - 1) (Znth z qr_data 0) ltac:(lia))
    as Hwindow.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_57_split_goal_2 : solver_safety_wit_57_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH15 z ltac:(lia)) as Hquery.
  decompose [and] Hquery; clear Hquery.
  pose proof
    (PreH21 (Znth z ql_data 0 - 1) (Znth z qr_data 0) ltac:(lia))
    as Hwindow.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_57 : solver_safety_wit_57.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_57_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_57_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (j_3 = 0) by lia; subst j_3.
  unfold repeat_Z.
  rewrite Znth_repeat.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  apply digit_prefix_repeat_zero__prefix_construction.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH15.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_5 : solver_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (Znth i (c_string text) 0) with (Znth i text 48).
  - pose proof
      (digit_prefix_replace_step__prefix_construction
        text prefix_values_2 i PreH16 ltac:(rewrite PreH18; lia) PreH19)
      as Hstep.
    exact Hstep.
  - rewrite PreH4.
    rewrite app_Znth1 by lia.
    apply Znth_indep; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (i = n) by lia; subst i.
  intros lo hi [Hlohi Hhin].
  exact
    (digit_prefix_difference_bounds__prefix_construction
      text prefix_values_2 n ltac:(lia) ltac:(lia)
      PreH19
      ltac:(intros j Hj; apply PreH10; lia)
      lo hi Hlohi Hhin).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace n with i by lia.
  exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_spatial : solver_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z; simpl.
  rewrite (IntArray.seg_empty (&( "pos" )) 0 0).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "pos" )) 18).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial; lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_spatial : solver_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (2 * (r + 1)) with (2 * r + 2) by lia.
  rewrite <- (repeat_Z_tail (-1) (2 * r)) by lia.
  rewrite <- (repeat_Z_tail (-1) (2 * r + 1)) by lia.
  replace (2 * r + 1 + 1) with (2 * r + 2) by lia.
  cancel (IntArray.seg (&( "pos" )) 0 (2 * r + 2)
    (repeat_Z (-1) (2 * r + 2))).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (r = 9) by lia.
  subst r.
  change (FlatPositionsPrefix text w_pre 0 (repeat (-1) 18%nat)).
  apply flat_positions_repeat_minus_one__position_initialization.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH20.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (r = 9) by lia.
  subst r.
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH15.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_5 : solver_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10.
  exact H.
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

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : forall lo hi : Z, _ -> (0 <= _ /\ _) |- _ =>
      pose proof (H i (i + w_pre) ltac:(lia)) as Hrange
  end.
  pose proof (Z.rem_bound_pos
    (Znth (i + w_pre) prefix_values 0 - Znth i prefix_values 0) 9
    ltac:(lia) ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : forall lo hi : Z, _ -> (0 <= _ /\ _) |- _ =>
      pose proof (H i (i + w_pre) ltac:(lia)) as Hrange
  end.
  pose proof (Z.rem_bound_pos
    (Znth (i + w_pre) prefix_values 0 - Znth i prefix_values 0) 9
    ltac:(lia) ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : forall lo hi : Z, _ -> (0 <= _ /\ _) |- _ =>
      pose proof (H i (i + w_pre) ltac:(lia)) as Hrange
  end.
  rewrite Z.rem_mod_nonneg in * by lia.
  eapply flat_positions_insert_first__position_update; eauto.
  eapply current_window_start__position_update with (n := n).
  - exact PreH13.
  - exact PreH27.
  - exact PreH19.
  - exact PreH12.
  - exact PreH31.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_2 : solver_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__position_update.
  assumption.
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
  match goal with
  | H : forall lo hi : Z, _ -> (0 <= _ /\ _) |- _ =>
      pose proof (H i (i + w_pre) ltac:(lia)) as Hrange
  end.
  rewrite Z.rem_mod_nonneg in * by lia.
  eapply flat_positions_insert_second__position_update; eauto.
  eapply current_window_start__position_update with (n := n).
  - exact PreH14.
  - exact PreH28.
  - exact PreH20.
  - exact PreH13.
  - exact PreH32.
  - int_auto.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_2 : solver_entail_wit_7_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth__position_update.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_3_split_goal_1 : solver_entail_wit_7_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | H : forall lo hi : Z, _ -> (0 <= _ /\ _) |- _ =>
      pose proof (H i (i + w_pre) ltac:(lia)) as Hrange
  end.
  rewrite Z.rem_mod_nonneg in * by lia.
  eapply flat_positions_skip_full__position_update; eauto.
  eapply current_window_start__position_update with (n := n).
  - exact PreH14.
  - exact PreH28.
  - exact PreH20.
  - exact PreH13.
  - exact PreH32.
  - int_auto.
  - int_auto.
Qed.

Lemma proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply query_output_prefix_nil__query_setup.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((n - w_pre) + 1) with i by lia.
  exact PreH22.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply PreH21; eassumption.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH11.
  apply Zlength_nonneg.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_5 : solver_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply PreH15; eassumption.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_6 : solver_entail_wit_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply PreH10; eassumption.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH33 z ltac:(lia)) as Hquery.
  destruct Hquery as [Hquery Hqk_lt].
  destruct Hquery as [Hquery Hqk_nonneg].
  destruct Hquery as [Hquery Hqr_le_n].
  destruct Hquery as [Hquery Hql_le_qr].
  destruct Hquery as [Hquery Hql_pos].
  pose proof
    (PreH39 (Znth z ql_data 0 - 1) (Znth z qr_data 0)
      ltac:(rewrite PreH20; lia)) as Hprefix_bounds.
  pose proof
    (Z.rem_bound_pos
      (Znth (Znth z qr_data 0) prefix_values 0 -
       Znth (Znth z ql_data 0 - 1) prefix_values 0)
      9 (proj1 Hprefix_bounds) ltac:(lia)) as Hremainder_bounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH33 z ltac:(lia)) as Hquery.
  destruct Hquery as [Hquery Hqk_lt].
  destruct Hquery as [Hquery Hqk_nonneg].
  destruct Hquery as [Hquery Hqr_le_n].
  destruct Hquery as [Hquery Hql_le_qr].
  destruct Hquery as [Hquery Hql_pos].
  pose proof
    (PreH39 (Znth z ql_data 0 - 1) (Znth z qr_data 0)
      ltac:(rewrite PreH20; lia)) as Hprefix_bounds.
  pose proof
    (Z.rem_bound_pos
      (Znth (Znth z qr_data 0) prefix_values 0 -
       Znth (Znth z ql_data 0 - 1) prefix_values 0)
      9 (proj1 Hprefix_bounds) ltac:(lia)) as Hremainder_bounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_1 : solver_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change
    (QueryBestPrefix text w_pre (Znth z qs __default__Prod__Prod_Z_Z_Z)
      0 1073741824 1073741824).
  apply query_best_prefix_zero__query_setup.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_2 : solver_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply PreH39; eassumption.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_3 : solver_entail_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply PreH33; eassumption.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_4 : solver_entail_wit_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_1 : solver_entail_wit_11_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_abs (k - a * v) 9 ltac:(lia)) as Hremainder_bound.
  cbn in Hremainder_bound.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_1 : solver_entail_wit_11_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_abs (k - a * v) 9 ltac:(lia)) as Hremainder_bound.
  cbn in Hremainder_bound.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_1 : solver_entail_wit_12_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
  {
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    unfold ztriple_1, ztriple_2, ztriple_3 in PreH52, PreH53, PreH54.
    cbn in PreH52, PreH53, PreH54. subst. reflexivity.
  }
  rewrite Hqeq in PreH69 |- *.
  assert (Hquery : DecimalSub text (l - 1) (r - 1) mod 9 = v).
  { eapply (decimal_sub_query_rem9__query_choose_candidate
      text prefix_values_2 n l r v); eauto; lia. }
  assert (Hres : (k - a * v) % 9 = (k - a * v) mod 9).
  { apply rem9_nonnegative_normalize__query_choose_candidate. lia. }
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1) a
    PreH64 ltac:(lia) PreH67) as [HfirstA HsecondA].
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1)
    ((k - a * v) % 9) PreH64 ltac:(lia) PreH67)
    as [HfirstB HsecondB].
  eapply (query_best_prefix_step_select__query_choose_candidate
    text w_pre l r k v a ((k - a * v) % 9)
    best1 best2 (Znth (2 * a) position_values_2 0)
    (Znth (2 * ((k - a * v) % 9)) position_values_2 0));
    eauto; try lia.
  all: rewrite <- PreH31; auto.
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_1 : solver_entail_wit_12_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
  {
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    unfold ztriple_1, ztriple_2, ztriple_3 in PreH52, PreH53, PreH54.
    cbn in PreH52, PreH53, PreH54. subst. reflexivity.
  }
  rewrite Hqeq in PreH69 |- *.
  assert (Hquery : DecimalSub text (l - 1) (r - 1) mod 9 = v).
  { eapply (decimal_sub_query_rem9__query_choose_candidate
      text prefix_values_2 n l r v); eauto; lia. }
  assert (Hres : (k - a * v) % 9 = (k - a * v) mod 9).
  { apply rem9_nonnegative_normalize__query_choose_candidate. lia. }
  remember ((k - a * v) % 9) as b eqn:Hb in *.
  subst a.
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1) b
    PreH64 ltac:(lia) PreH67) as [HfirstA HsecondA].
  eapply (query_best_prefix_step_select__query_choose_candidate
    text w_pre l r k v b b best1 best2
    (Znth (2 * b) position_values_2 0)
    (Znth (2 * b + 1) position_values_2 0));
    eauto; try lia.
  all: rewrite <- PreH31; auto.
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_3_split_goal_1 : solver_entail_wit_12_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
  {
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    unfold ztriple_1, ztriple_2, ztriple_3 in PreH52, PreH53, PreH54.
    cbn in PreH52, PreH53, PreH54. subst. reflexivity.
  }
  rewrite Hqeq in PreH69 |- *.
  assert (Hquery : DecimalSub text (l - 1) (r - 1) mod 9 = v).
  { eapply (decimal_sub_query_rem9__query_choose_candidate
      text prefix_values_2 n l r v); eauto; lia. }
  assert (Hres : (k - a * v) % 9 + 9 = (k - a * v) mod 9).
  { apply rem9_negative_normalize__query_choose_candidate. lia. }
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1) a
    PreH64 ltac:(lia) PreH67) as [HfirstA HsecondA].
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1)
    ((k - a * v) % 9 + 9) PreH64 ltac:(lia) PreH67)
    as [HfirstB HsecondB].
  eapply (query_best_prefix_step_select__query_choose_candidate
    text w_pre l r k v a ((k - a * v) % 9 + 9)
    best1 best2 (Znth (2 * a) position_values_2 0)
    (Znth (2 * ((k - a * v) % 9 + 9)) position_values_2 0));
    eauto; try lia.
  all: rewrite <- PreH31; auto.
Qed.

Lemma proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_4_split_goal_1 : solver_entail_wit_12_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
  {
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    unfold ztriple_1, ztriple_2, ztriple_3 in PreH52, PreH53, PreH54.
    cbn in PreH52, PreH53, PreH54. subst. reflexivity.
  }
  rewrite Hqeq in PreH69 |- *.
  assert (Hquery : DecimalSub text (l - 1) (r - 1) mod 9 = v).
  { eapply (decimal_sub_query_rem9__query_choose_candidate
      text prefix_values_2 n l r v); eauto; lia. }
  assert (Hres : (k - a * v) % 9 + 9 = (k - a * v) mod 9).
  { apply rem9_negative_normalize__query_choose_candidate. lia. }
  remember ((k - a * v) % 9 + 9) as b eqn:Hb in *.
  subst a.
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1) b
    PreH64 ltac:(lia) PreH67) as [HfirstA HsecondA].
  eapply (query_best_prefix_step_select__query_choose_candidate
    text w_pre l r k v b b best1 best2
    (Znth (2 * b) position_values_2 0)
    (Znth (2 * b + 1) position_values_2 0));
    eauto; try lia.
  all: rewrite <- PreH31; auto.
Qed.

Lemma proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_5_split_goal_1 : solver_entail_wit_12_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
  {
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    unfold ztriple_1, ztriple_2, ztriple_3 in PreH54, PreH55, PreH56.
    cbn in PreH54, PreH55, PreH56. subst. reflexivity.
  }
  rewrite Hqeq in PreH71 |- *.
  assert (Hquery : DecimalSub text (l - 1) (r - 1) mod 9 = v).
  { eapply (decimal_sub_query_rem9__query_choose_candidate
      text prefix_values_2 n l r v); eauto; lia. }
  assert (Hres : (k - a * v) % 9 + 9 = (k - a * v) mod 9).
  { apply rem9_negative_normalize__query_choose_candidate. lia. }
  remember ((k - a * v) % 9 + 9) as b eqn:Hb in *.
  subst a.
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1) b
    PreH66 ltac:(lia) PreH69) as [HfirstA HsecondA].
  assert (HfirstBest : FirstWindowStart text w_pre
    (n - w_pre + 1) b best1).
  { rewrite <- PreH2. exact HfirstA. }
  assert (HsecondBest : SecondWindowStart text w_pre
    (n - w_pre + 1) b best1
    (Znth (2 * b + 1) position_values_2 0)).
  { rewrite <- PreH2. exact HsecondA. }
  eapply (query_best_prefix_step_select__query_choose_candidate
    text w_pre l r k v b b best1 best2 best1
    (Znth (2 * b + 1) position_values_2 0));
    eauto; try lia.
  all: rewrite <- PreH33; auto.
Qed.

Lemma proof_of_solver_entail_wit_12_5 : solver_entail_wit_12_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_6_split_goal_1 : solver_entail_wit_12_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
  {
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    unfold ztriple_1, ztriple_2, ztriple_3 in PreH54, PreH55, PreH56.
    cbn in PreH54, PreH55, PreH56. subst. reflexivity.
  }
  rewrite Hqeq in PreH71 |- *.
  assert (Hquery : DecimalSub text (l - 1) (r - 1) mod 9 = v).
  { eapply (decimal_sub_query_rem9__query_choose_candidate
      text prefix_values_2 n l r v); eauto; lia. }
  assert (Hres : (k - a * v) % 9 + 9 = (k - a * v) mod 9).
  { apply rem9_negative_normalize__query_choose_candidate. lia. }
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1) a
    PreH66 ltac:(lia) PreH69) as [HfirstA HsecondA].
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1)
    ((k - a * v) % 9 + 9) PreH66 ltac:(lia) PreH69)
    as [HfirstB HsecondB].
  assert (HfirstBest : FirstWindowStart text w_pre
    (n - w_pre + 1) a best1).
  { rewrite <- PreH2. exact HfirstA. }
  eapply (query_best_prefix_step_select__query_choose_candidate
    text w_pre l r k v a ((k - a * v) % 9 + 9)
    best1 best2 best1
    (Znth (2 * ((k - a * v) % 9 + 9)) position_values_2 0));
    eauto; try lia.
  all: rewrite <- PreH33; auto.
Qed.

Lemma proof_of_solver_entail_wit_12_6 : solver_entail_wit_12_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_6_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_7_split_goal_1 : solver_entail_wit_12_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hqeq :
    Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
  {
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    unfold ztriple_1, ztriple_2, ztriple_3
      in PreH54, PreH55, PreH56.
    cbn in PreH54, PreH55, PreH56.
    subst.
    reflexivity.
  }
  rewrite Hqeq in PreH71 |- *.
  assert (Hquery : DecimalSub text (l - 1) (r - 1) mod 9 = v).
  { eapply (decimal_sub_query_rem9__query_choose_candidate
      text prefix_values_2 n l r v); eauto; lia. }
  assert (Hres : (k - a * v) % 9 = (k - a * v) mod 9).
  { apply rem9_nonnegative_normalize__query_choose_candidate. lia. }
  remember ((k - a * v) % 9) as b eqn:Hb in *.
  subst a.
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1) b
    PreH66 ltac:(lia) PreH69) as [HfirstA HsecondA].
  assert (HfirstBest : FirstWindowStart text w_pre
    (n - w_pre + 1) b best1).
  { rewrite <- PreH2. exact HfirstA. }
  assert (HsecondBest : SecondWindowStart text w_pre
    (n - w_pre + 1) b best1
    (Znth (2 * b + 1) position_values_2 0)).
  { rewrite <- PreH2. exact HsecondA. }
  eapply (query_best_prefix_step_select__query_choose_candidate
    text w_pre l r k v b b best1 best2 best1
    (Znth (2 * b + 1) position_values_2 0));
    eauto; try lia.
  all: rewrite <- PreH33; auto.
Qed.

Lemma proof_of_solver_entail_wit_12_7 : solver_entail_wit_12_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_7_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_8_split_goal_1 : solver_entail_wit_12_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hqeq :
    Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
  {
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    unfold ztriple_1, ztriple_2, ztriple_3
      in PreH54, PreH55, PreH56.
    cbn in PreH54, PreH55, PreH56.
    subst.
    reflexivity.
  }
  rewrite Hqeq in PreH71 |- *.
  assert (Hquery : DecimalSub text (l - 1) (r - 1) mod 9 = v).
  { eapply (decimal_sub_query_rem9__query_choose_candidate
      text prefix_values_2 n l r v); eauto; lia. }
  assert (Hres : (k - a * v) % 9 = (k - a * v) mod 9).
  { apply rem9_nonnegative_normalize__query_choose_candidate. lia. }
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1) a
    PreH66 ltac:(lia) PreH69) as [HfirstA HsecondA].
  pose proof (flat_positions_starts__query_choose_candidate
    text position_values_2 w_pre (n - w_pre + 1)
    ((k - a * v) % 9) PreH66 ltac:(lia) PreH69)
    as [HfirstB HsecondB].
  assert (HfirstBest : FirstWindowStart text w_pre
    (n - w_pre + 1) a best1).
  { rewrite <- PreH2. exact HfirstA. }
  eapply (query_best_prefix_step_select__query_choose_candidate
    text w_pre l r k v a ((k - a * v) % 9)
    best1 best2 best1
    (Znth (2 * ((k - a * v) % 9)) position_values_2 0));
    eauto; try lia.
  all: rewrite <- PreH33; auto.
Qed.

Lemma proof_of_solver_entail_wit_12_8 : solver_entail_wit_12_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_8_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_9_split_goal_1 : solver_entail_wit_12_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_low; eauto.
  - intros [x y] Hcandidate.
    unfold PrefixEligiblePair, QueryPair in Hcandidate.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    cbn in Hcandidate |- *.
    lia.
  - intros [x y] Hcandidate Hnot_old.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z)
      as [[ql qr] qk] eqn:Hquery_value.
    cbn [ztriple_1 ztriple_2 ztriple_3] in *.
    change (l = ql) in PreH54.
    change (r = qr) in PreH55.
    change (k = qk) in PreH56.
    subst ql; subst qr; subst qk.
    unfold PrefixEligiblePair in Hcandidate.
    destruct Hcandidate as [Hpair Hresidue_range].
    assert (Hxresidue : PairFirstResidue text w_pre (x, y) = a).
    {
      destruct Hresidue_range as [Hresidue_nonneg Hresidue_upper].
      destruct (Z.eq_dec (PairFirstResidue text w_pre (x, y)) a)
        as [Heq | Hneq]; [exact Heq |].
      exfalso.
      apply Hnot_old.
      unfold PrefixEligiblePair.
      split; [exact Hpair | lia].
    }
    assert (Hvmod : v =
      (Znth r prefix_values_2 0 - Znth (l - 1) prefix_values_2 0) mod 9).
    {
      rewrite <- Z.rem_mod_nonneg by (try lia;
        pose proof (PreH68 (l - 1) r ltac:(lia)); lia).
      exact PreH62.
    }
    assert (Hwindows :
      WindowStart text w_pre (n - w_pre + 1) a x /\
      WindowStart text w_pre (n - w_pre + 1)
        ((k - a * v) mod 9) y).
    {
      eapply query_pair_window_residues__query_preserve_low;
        eauto; try lia.
      all: try exact Hvmod.
      all: match goal with |- ?G => fail 1 "WINDOWSIDE" G end.
    }
    destruct Hwindows as [Hxwindow Hywindow].
    assert (Hnormalized :
      Z.rem (k - a * v) 9 + 9 = (k - a * v) mod 9).
    { apply negative_rem_plus_eq_mod9__query_preserve_low.
      assumption. }
    rewrite <- Hnormalized in Hywindow.
    rewrite <- PreH5 in Hywindow.
    pose proof (flat_positions_first_le__query_preserve_low
      text w_pre (n - w_pre + 1) position_values_2 a x)
      as Hfirst_le.
    specialize (Hfirst_le ltac:(assumption) ltac:(assumption)
      ltac:(lia) ltac:(lia) Hxwindow).
    unfold PairLexLe.
    cbn.
    destruct (Z_lt_ge_dec best1 x) as [Hstrict | Htied].
    + left; lia.
    + right.
      split; [lia |].
      pose proof (flat_positions_second_le__query_preserve_low
        text w_pre (n - w_pre + 1) position_values_2 a x y)
        as Hsecond_le.
      assert (Hxyneq : x <> y).
      { unfold QueryPair in Hpair; cbn in Hpair; tauto. }
      assert (Hxfirst : x = Znth (2 * a) position_values_2 0) by lia.
      assert (Hsecond_nonnegative :
        0 <= Znth (2 * a + 1) position_values_2 0).
      { rewrite PreH5. lia. }
      specialize (Hsecond_le PreH66 PreH69 ltac:(lia) Hxfirst
        Hsecond_nonnegative Hywindow ltac:(lia)).
      rewrite <- PreH5 in PreH1.
      lia.
Qed.

Lemma proof_of_solver_entail_wit_12_9 : solver_entail_wit_12_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_9_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_10_split_goal_1 : solver_entail_wit_12_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_low; eauto.
  - intros [x y] Hcandidate.
    unfold PrefixEligiblePair, QueryPair in Hcandidate.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    cbn in Hcandidate |- *; lia.
  - intros [x y] Hcandidate Hnot_old.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z)
      as [[ql qr] qk] eqn:Hquery_value.
    change (l = ql) in PreH54; change (r = qr) in PreH55;
      change (k = qk) in PreH56.
    subst ql; subst qr; subst qk.
    unfold PrefixEligiblePair in Hcandidate.
    destruct Hcandidate as [Hpair Hresidue_range].
    assert (Hxresidue : PairFirstResidue text w_pre (x, y) = a).
    { destruct Hresidue_range as [Hlo Hhi].
      destruct (Z.eq_dec (PairFirstResidue text w_pre (x, y)) a);
        [assumption|].
      exfalso; apply Hnot_old; unfold PrefixEligiblePair; split;
        [exact Hpair|lia]. }
    assert (Hvmod : v =
      (Znth r prefix_values_2 0 - Znth (l - 1) prefix_values_2 0) mod 9).
    { rewrite <- Z.rem_mod_nonneg by (try lia;
        pose proof (PreH68 (l - 1) r ltac:(lia)); lia).
      exact PreH62. }
    assert (Hwindows :
      WindowStart text w_pre (n - w_pre + 1) a x /\
      WindowStart text w_pre (n - w_pre + 1) ((k - a * v) mod 9) y).
    { eapply query_pair_window_residues__query_preserve_low; eauto; lia. }
    destruct Hwindows as [Hxwindow Hywindow].
    assert (Hnormalized :
      Z.rem (k - a * v) 9 + 9 = (k - a * v) mod 9).
    { apply negative_rem_plus_eq_mod9__query_preserve_low; assumption. }
    rewrite <- Hnormalized in Hywindow.
    pose proof (flat_positions_first_le__query_preserve_low
      text w_pre (n - w_pre + 1) position_values_2 a x
      PreH66 PreH69 ltac:(lia) ltac:(lia) Hxwindow) as Hfirst_le.
    pose proof (flat_positions_first_le__query_preserve_low
      text w_pre (n - w_pre + 1) position_values_2
      ((k - a * v) % 9 + 9) y
      PreH66 PreH69 ltac:(lia) ltac:(lia) Hywindow) as Htarget_le.
    unfold PairLexLe; cbn.
    destruct (Z_lt_ge_dec best1 x); [left; lia|].
    right; split; [lia|].
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_10 : solver_entail_wit_12_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_10_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_11_split_goal_1 : solver_entail_wit_12_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_low; eauto.
  - intros [x y] Hcandidate.
    unfold PrefixEligiblePair, QueryPair in Hcandidate.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    cbn in Hcandidate |- *; lia.
  - intros [x y] Hcandidate Hnot_old.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z)
      as [[ql qr] qk] eqn:Hquery_value.
    change (l = ql) in PreH54; change (r = qr) in PreH55;
      change (k = qk) in PreH56.
    subst ql; subst qr; subst qk.
    unfold PrefixEligiblePair in Hcandidate.
    destruct Hcandidate as [Hpair Hresidue_range].
    assert (Hxresidue : PairFirstResidue text w_pre (x, y) = a).
    { destruct Hresidue_range as [Hlo Hhi].
      destruct (Z.eq_dec (PairFirstResidue text w_pre (x, y)) a);
        [assumption|].
      exfalso; apply Hnot_old; unfold PrefixEligiblePair; split;
        [exact Hpair|lia]. }
    assert (Hvmod : v =
      (Znth r prefix_values_2 0 - Znth (l - 1) prefix_values_2 0) mod 9).
    { rewrite <- Z.rem_mod_nonneg by (try lia;
        pose proof (PreH68 (l - 1) r ltac:(lia)); lia).
      exact PreH62. }
    assert (Hwindows :
      WindowStart text w_pre (n - w_pre + 1) a x /\
      WindowStart text w_pre (n - w_pre + 1) ((k - a * v) mod 9) y).
    { eapply query_pair_window_residues__query_preserve_low; eauto; lia. }
    destruct Hwindows as [Hxwindow Hywindow].
    assert (Hnormalized : Z.rem (k - a * v) 9 = (k - a * v) mod 9).
    { apply nonnegative_rem_eq_mod9__query_preserve_low; assumption. }
    rewrite <- Hnormalized in Hywindow.
    rewrite <- PreH5 in Hywindow.
    pose proof (flat_positions_first_le__query_preserve_low
      text w_pre (n - w_pre + 1) position_values_2 a x
      PreH66 PreH69 ltac:(lia) ltac:(lia) Hxwindow) as Hfirst_le.
    unfold PairLexLe; cbn.
    destruct (Z_lt_ge_dec best1 x); [left; lia|].
    right; split; [lia|].
    pose proof (flat_positions_second_le__query_preserve_low
      text w_pre (n - w_pre + 1) position_values_2 a x y) as Hsecond_le.
    assert (Hxyneq : x <> y).
    { unfold QueryPair in Hpair; cbn in Hpair; tauto. }
    assert (Hxfirst : x = Znth (2 * a) position_values_2 0) by lia.
    assert (Hsecond_nonnegative :
      0 <= Znth (2 * a + 1) position_values_2 0).
    { rewrite PreH5; lia. }
    specialize (Hsecond_le PreH66 PreH69 ltac:(lia) Hxfirst
      Hsecond_nonnegative Hywindow ltac:(lia)).
    rewrite <- PreH5 in PreH1.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_11 : solver_entail_wit_12_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_11_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_12_split_goal_1 : solver_entail_wit_12_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_low; eauto.
  - intros [x y] Hcandidate.
    unfold PrefixEligiblePair, QueryPair in Hcandidate.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    cbn in Hcandidate |- *; lia.
  - intros [x y] Hcandidate Hnot_old.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z)
      as [[ql qr] qk] eqn:Hquery_value.
    change (l = ql) in PreH54; change (r = qr) in PreH55;
      change (k = qk) in PreH56.
    subst ql; subst qr; subst qk.
    unfold PrefixEligiblePair in Hcandidate.
    destruct Hcandidate as [Hpair Hresidue_range].
    assert (Hxresidue : PairFirstResidue text w_pre (x, y) = a).
    { destruct Hresidue_range as [Hlo Hhi].
      destruct (Z.eq_dec (PairFirstResidue text w_pre (x, y)) a);
        [assumption|].
      exfalso; apply Hnot_old; unfold PrefixEligiblePair; split;
        [exact Hpair|lia]. }
    assert (Hvmod : v =
      (Znth r prefix_values_2 0 - Znth (l - 1) prefix_values_2 0) mod 9).
    { rewrite <- Z.rem_mod_nonneg by (try lia;
        pose proof (PreH68 (l - 1) r ltac:(lia)); lia).
      exact PreH62. }
    assert (Hwindows :
      WindowStart text w_pre (n - w_pre + 1) a x /\
      WindowStart text w_pre (n - w_pre + 1) ((k - a * v) mod 9) y).
    { eapply query_pair_window_residues__query_preserve_low; eauto; lia. }
    destruct Hwindows as [Hxwindow Hywindow].
    assert (Hnormalized : Z.rem (k - a * v) 9 = (k - a * v) mod 9).
    { apply nonnegative_rem_eq_mod9__query_preserve_low; assumption. }
    rewrite <- Hnormalized in Hywindow.
    pose proof (flat_positions_first_le__query_preserve_low
      text w_pre (n - w_pre + 1) position_values_2 a x
      PreH66 PreH69 ltac:(lia) ltac:(lia) Hxwindow) as Hfirst_le.
    pose proof (flat_positions_first_le__query_preserve_low
      text w_pre (n - w_pre + 1) position_values_2
      ((k - a * v) % 9) y
      PreH66 PreH69 ltac:(lia) ltac:(lia) Hywindow) as Htarget_le.
    unfold PairLexLe; cbn.
    destruct (Z_lt_ge_dec best1 x); [left; lia|].
    right; split; [lia|].
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_12 : solver_entail_wit_12_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_12_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_13_split_goal_1 : solver_entail_wit_12_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_low; eauto.
  - intros [x y] Hcandidate.
    unfold PrefixEligiblePair, QueryPair in Hcandidate.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    cbn in Hcandidate |- *; lia.
  - intros [x y] Hcandidate Hnot_old.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z)
      as [[ql qr] qk] eqn:Hquery_value.
    change (l = ql) in PreH53; change (r = qr) in PreH54;
      change (k = qk) in PreH55.
    subst ql; subst qr; subst qk.
    unfold PrefixEligiblePair in Hcandidate.
    destruct Hcandidate as [Hpair Hresidue_range].
    assert (Hxresidue : PairFirstResidue text w_pre (x, y) = a).
    { destruct Hresidue_range as [Hlo Hhi].
      destruct (Z.eq_dec (PairFirstResidue text w_pre (x, y)) a);
        [assumption|].
      exfalso; apply Hnot_old; unfold PrefixEligiblePair; split;
        [exact Hpair|lia]. }
    assert (Hvmod : v =
      (Znth r prefix_values_2 0 - Znth (l - 1) prefix_values_2 0) mod 9).
    { rewrite <- Z.rem_mod_nonneg by (try lia;
        pose proof (PreH67 (l - 1) r ltac:(lia)); lia).
      exact PreH61. }
    assert (Hwindows :
      WindowStart text w_pre (n - w_pre + 1) a x /\
      WindowStart text w_pre (n - w_pre + 1) ((k - a * v) mod 9) y).
    { eapply query_pair_window_residues__query_preserve_low; eauto; lia. }
    destruct Hwindows as [Hxwindow Hywindow].
    pose proof (flat_positions_first_le__query_preserve_low
      text w_pre (n - w_pre + 1) position_values_2 a x
      PreH65 PreH68 ltac:(lia) ltac:(lia) Hxwindow) as Hfirst_le.
    unfold PairLexLe; cbn; left; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_13 : solver_entail_wit_12_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_13_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_14_split_goal_1 : solver_entail_wit_12_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_low; eauto.
  - intros [x y] Hcandidate.
    unfold PrefixEligiblePair, QueryPair in Hcandidate.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    cbn in Hcandidate |- *; lia.
  - intros [x y] Hcandidate Hnot_old.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z)
      as [[ql qr] qk] eqn:Hquery_value.
    change (l = ql) in PreH53; change (r = qr) in PreH54;
      change (k = qk) in PreH55.
    subst ql; subst qr; subst qk.
    unfold PrefixEligiblePair in Hcandidate.
    destruct Hcandidate as [Hpair Hresidue_range].
    assert (Hxresidue : PairFirstResidue text w_pre (x, y) = a).
    { destruct Hresidue_range as [Hlo Hhi].
      destruct (Z.eq_dec (PairFirstResidue text w_pre (x, y)) a);
        [assumption|].
      exfalso; apply Hnot_old; unfold PrefixEligiblePair; split;
        [exact Hpair|lia]. }
    assert (Hvmod : v =
      (Znth r prefix_values_2 0 - Znth (l - 1) prefix_values_2 0) mod 9).
    { rewrite <- Z.rem_mod_nonneg by (try lia;
        pose proof (PreH67 (l - 1) r ltac:(lia)); lia).
      exact PreH61. }
    assert (Hwindows :
      WindowStart text w_pre (n - w_pre + 1) a x /\
      WindowStart text w_pre (n - w_pre + 1) ((k - a * v) mod 9) y).
    { eapply query_pair_window_residues__query_preserve_low; eauto; lia. }
    destruct Hwindows as [Hxwindow Hywindow].
    pose proof (flat_positions_first_le__query_preserve_low
      text w_pre (n - w_pre + 1) position_values_2 a x
      PreH65 PreH68 ltac:(lia) ltac:(lia) Hxwindow) as Hfirst_le.
    unfold PairLexLe; cbn; left; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_14 : solver_entail_wit_12_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_14_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_15_split_goal_1 : solver_entail_wit_12_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_low; eauto.
  - intros [x y] Hcandidate.
    unfold PrefixEligiblePair, QueryPair in Hcandidate.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
    cbn in Hcandidate |- *; lia.
  - intros [x y] Hcandidate Hnot_old.
    destruct (Znth z qs __default__Prod__Prod_Z_Z_Z)
      as [[ql qr] qk] eqn:Hquery_value.
    change (l = ql) in PreH53; change (r = qr) in PreH54;
      change (k = qk) in PreH55.
    subst ql; subst qr; subst qk.
    unfold PrefixEligiblePair in Hcandidate.
    destruct Hcandidate as [Hpair Hresidue_range].
    assert (Hxresidue : PairFirstResidue text w_pre (x, y) = a).
    { destruct Hresidue_range as [Hlo Hhi].
      destruct (Z.eq_dec (PairFirstResidue text w_pre (x, y)) a);
        [assumption|].
      exfalso; apply Hnot_old; unfold PrefixEligiblePair; split;
        [exact Hpair|lia]. }
    assert (Hvmod : v =
      (Znth r prefix_values_2 0 - Znth (l - 1) prefix_values_2 0) mod 9).
    { rewrite <- Z.rem_mod_nonneg by (try lia;
        pose proof (PreH67 (l - 1) r ltac:(lia)); lia).
      exact PreH61. }
    assert (Hwindows :
      WindowStart text w_pre (n - w_pre + 1) a x /\
      WindowStart text w_pre (n - w_pre + 1) ((k - a * v) mod 9) y).
    { eapply query_pair_window_residues__query_preserve_low; eauto; lia. }
    destruct Hwindows as [Hxwindow Hywindow].
    pose proof (flat_positions_first_le__query_preserve_low
      text w_pre (n - w_pre + 1) position_values_2 a x
      PreH65 PreH68 ltac:(lia) ltac:(lia) Hxwindow) as Hfirst_le.
    unfold PairLexLe; cbn; left; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_15 : solver_entail_wit_12_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_15_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_16_split_goal_1 : solver_entail_wit_12_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_high.
  - lia.
  - exact PreH70.
  - intros [x y] Hnew.
    unfold PrefixEligiblePair in Hnew.
    destruct Hnew as [Hpair Hresidue].
    destruct (Z_lt_ge_dec (PairFirstResidue text w_pre (x, y)) a).
    + left. unfold PrefixEligiblePair. split; [exact Hpair | lia].
    + assert (Hresidue_eq : PairFirstResidue text w_pre (x, y) = a) by lia.
      assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
      {
        destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
        unfold ztriple_1, ztriple_2, ztriple_3 in PreH53, PreH54, PreH55.
        cbn in PreH53, PreH54, PreH55. subst. reflexivity.
      }
      rewrite Hqeq in Hpair.
      pose proof (PreH67 (l - 1) r ltac:(lia)) as Hdiff.
      pose proof
        (candidate_windows__query_preserve_high
          text prefix_values_2 n w_pre l r k v a (x, y)
          PreH32 PreH56 PreH57 PreH58 (conj PreH59 PreH60)
          (fun j Hj => proj1 (PreH40 j Hj)) (proj1 Hdiff) PreH66 PreH61
          Hpair Hresidue_eq) as [Hx _].
      unfold FlatPositionsPrefix, PositionsPrefix in PreH68.
      specialize (PreH68 a ltac:(lia)).
      rewrite flat_position_row__query_preserve_high in PreH68 by lia.
      cbn in PreH68.
      destruct PreH68 as [Hfirst _].
      change
        (FirstWindowStart text w_pre (n - w_pre + 1) a
          (Znth (2 * a) position_values_2 (-1)))
        in Hfirst.
      rewrite
        (Znth_indep position_values_2 (2 * a) (-1) 0) in Hfirst by lia.
      pose proof
        (first_window_lower_bound__query_preserve_high
          text w_pre (n - w_pre + 1) a
          (Znth (2 * a) position_values_2 0)
          Hfirst ltac:(lia) x Hx) as Hfirst_le.
      right. split.
      * unfold WindowStart in Hx. cbn in Hx.
        destruct Hx as [[Hxlower Hxupper] [Hxend Hxresidue]]. lia.
      * unfold PairLexLe. cbn. left. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_16 : solver_entail_wit_12_16.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_16_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_17_split_goal_1 : solver_entail_wit_12_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_high.
  - lia.
  - exact PreH66.
  - intros [x y] Hnew.
    unfold PrefixEligiblePair in Hnew.
    destruct Hnew as [Hpair Hresidue].
    destruct (Z_lt_ge_dec (PairFirstResidue text w_pre (x, y)) a).
    + left. unfold PrefixEligiblePair. split; [exact Hpair | lia].
    + assert (Hresidue_eq : PairFirstResidue text w_pre (x, y) = a) by lia.
      exfalso.
      assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
      {
        destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
        unfold ztriple_1, ztriple_2, ztriple_3 in PreH49, PreH50, PreH51.
        cbn in PreH49, PreH50, PreH51. subst. reflexivity.
      }
      rewrite Hqeq in Hpair.
      pose proof (PreH63 (l - 1) r ltac:(lia)) as Hdiff.
      pose proof
        (candidate_windows__query_preserve_high
          text prefix_values_2 n w_pre l r k v a (x, y)
          PreH28 PreH52 PreH53 PreH54 (conj PreH55 PreH56)
          (fun j Hj => proj1 (PreH36 j Hj)) (proj1 Hdiff) PreH62 PreH57
          Hpair Hresidue_eq) as [Hx _].
      unfold FlatPositionsPrefix, PositionsPrefix in PreH64.
      specialize (PreH64 a ltac:(lia)).
      rewrite flat_position_row__query_preserve_high in PreH64 by lia.
      cbn in PreH64.
      destruct PreH64 as [Hfirst _].
      unfold FirstWindowStart in Hfirst.
      destruct Hfirst as [[_ Hnone] | [Hstored _]].
      * exact (Hnone x Hx).
      * change
          (WindowStart text w_pre (n - w_pre + 1) a
            (Znth (2 * a) position_values_2 (-1))) in Hstored.
        rewrite (Znth_indep position_values_2 (2 * a) (-1) 0) in Hstored by lia.
        unfold WindowStart in Hstored. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_17 : solver_entail_wit_12_17.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_17_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_18_split_goal_1 : solver_entail_wit_12_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_high.
  - lia.
  - exact PreH66.
  - intros [x y] Hnew.
    unfold PrefixEligiblePair in Hnew.
    destruct Hnew as [Hpair Hresidue].
    destruct (Z_lt_ge_dec (PairFirstResidue text w_pre (x, y)) a).
    + left. unfold PrefixEligiblePair. split; [exact Hpair | lia].
    + assert (Hresidue_eq : PairFirstResidue text w_pre (x, y) = a) by lia.
      exfalso.
      assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
      {
        destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
        unfold ztriple_1, ztriple_2, ztriple_3 in PreH49, PreH50, PreH51.
        cbn in PreH49, PreH50, PreH51. subst. reflexivity.
      }
      rewrite Hqeq in Hpair.
      pose proof (PreH63 (l - 1) r ltac:(lia)) as Hdiff.
      pose proof
        (candidate_windows__query_preserve_high
          text prefix_values_2 n w_pre l r k v a (x, y)
          PreH28 PreH52 PreH53 PreH54 (conj PreH55 PreH56)
          (fun j Hj => proj1 (PreH36 j Hj)) (proj1 Hdiff) PreH62 PreH57
          Hpair Hresidue_eq) as [Hx _].
      unfold FlatPositionsPrefix, PositionsPrefix in PreH64.
      specialize (PreH64 a ltac:(lia)).
      rewrite flat_position_row__query_preserve_high in PreH64 by lia.
      cbn in PreH64.
      destruct PreH64 as [Hfirst _].
      unfold FirstWindowStart in Hfirst.
      destruct Hfirst as [[_ Hnone] | [Hstored _]].
      * exact (Hnone x Hx).
      * change
          (WindowStart text w_pre (n - w_pre + 1) a
            (Znth (2 * a) position_values_2 (-1))) in Hstored.
        rewrite (Znth_indep position_values_2 (2 * a) (-1) 0) in Hstored by lia.
        unfold WindowStart in Hstored. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_18 : solver_entail_wit_12_18.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_18_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_19_split_goal_1 : solver_entail_wit_12_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_high.
  - lia.
  - exact PreH68.
  - intros [x y] Hnew.
    unfold PrefixEligiblePair in Hnew.
    destruct Hnew as [Hpair Hresidue].
    destruct (Z_lt_ge_dec (PairFirstResidue text w_pre (x, y)) a).
    + left. unfold PrefixEligiblePair. split; [exact Hpair | lia].
    + assert (Hresidue_eq : PairFirstResidue text w_pre (x, y) = a) by lia.
      exfalso.
      assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
      {
        destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
        unfold ztriple_1, ztriple_2, ztriple_3 in PreH51, PreH52, PreH53.
        cbn in PreH51, PreH52, PreH53. subst. reflexivity.
      }
      rewrite Hqeq in Hpair.
      pose proof (PreH65 (l - 1) r ltac:(lia)) as Hdiff.
      pose proof
        (candidate_windows__query_preserve_high
          text prefix_values_2 n w_pre l r k v a (x, y)
          PreH30 PreH54 PreH55 PreH56 (conj PreH57 PreH58)
          (fun j Hj => proj1 (PreH38 j Hj)) (proj1 Hdiff) PreH64 PreH59
          Hpair Hresidue_eq) as [Hx Hy].
      pose proof
          (negative_rem_as_mod__query_preserve_high (k - a * v) PreH28) as Hmod.
      rewrite <- Hmod, <- PreH2 in Hy.
      rewrite <- PreH2 in PreH1.
      unfold FlatPositionsPrefix, PositionsPrefix in PreH66.
      specialize (PreH66 a ltac:(lia)).
      rewrite flat_position_row__query_preserve_high in PreH66 by lia.
      cbn in PreH66.
      destruct PreH66 as [_ Hsecond].
      change
        (SecondWindowStart text w_pre (n - w_pre + 1) a
          (Znth (2 * a) position_values_2 (-1))
          (Znth (2 * a + 1) position_values_2 (-1))) in Hsecond.
      rewrite (Znth_indep position_values_2 (2 * a) (-1) 0) in Hsecond by lia.
      rewrite (Znth_indep position_values_2 (2 * a + 1) (-1) 0) in Hsecond by lia.
      pose proof
        (second_window_negative_unique__query_preserve_high
          text w_pre (n - w_pre + 1) a
          (Znth (2 * a) position_values_2 0)
          (Znth (2 * a + 1) position_values_2 0)
          Hsecond PreH1 x Hx) as Hxeq.
      pose proof
        (second_window_negative_unique__query_preserve_high
          text w_pre (n - w_pre + 1) a
          (Znth (2 * a) position_values_2 0)
          (Znth (2 * a + 1) position_values_2 0)
          Hsecond PreH1 y Hy) as Hyeq.
      unfold QueryPair in Hpair. cbn in Hpair. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_19 : solver_entail_wit_12_19.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_19_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_20_split_goal_1 : solver_entail_wit_12_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_high.
  - lia.
  - exact PreH68.
  - intros [x y] Hnew.
    unfold PrefixEligiblePair in Hnew.
    destruct Hnew as [Hpair Hresidue].
    destruct (Z_lt_ge_dec (PairFirstResidue text w_pre (x, y)) a).
    + left. unfold PrefixEligiblePair. split; [exact Hpair | lia].
    + assert (Hresidue_eq : PairFirstResidue text w_pre (x, y) = a) by lia.
      exfalso.
      assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
      {
        destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
        unfold ztriple_1, ztriple_2, ztriple_3 in PreH51, PreH52, PreH53.
        cbn in PreH51, PreH52, PreH53. subst. reflexivity.
      }
      rewrite Hqeq in Hpair.
      pose proof (PreH65 (l - 1) r ltac:(lia)) as Hdiff.
      pose proof
        (candidate_windows__query_preserve_high
          text prefix_values_2 n w_pre l r k v a (x, y)
          PreH30 PreH54 PreH55 PreH56 (conj PreH57 PreH58)
          (fun j Hj => proj1 (PreH38 j Hj)) (proj1 Hdiff) PreH64 PreH59
          Hpair Hresidue_eq) as [_ Hy].
      pose proof
          (negative_rem_as_mod__query_preserve_high (k - a * v) PreH28) as Hmod.
      rewrite <- Hmod in Hy.
      unfold FlatPositionsPrefix, PositionsPrefix in PreH66.
      specialize (PreH66 (Z.rem (k - a * v) 9 + 9) ltac:(lia)).
      rewrite flat_position_row__query_preserve_high in PreH66 by lia.
      cbn in PreH66.
      destruct PreH66 as [Hfirst _].
      change
        (FirstWindowStart text w_pre (n - w_pre + 1)
          (Z.rem (k - a * v) 9 + 9)
          (Znth (2 * (Z.rem (k - a * v) 9 + 9)) position_values_2 (-1)))
        in Hfirst.
      rewrite
        (Znth_indep position_values_2
          (2 * (Z.rem (k - a * v) 9 + 9)) (-1) 0) in Hfirst by lia.
      exact
        (first_window_negative_none__query_preserve_high
          text w_pre (n - w_pre + 1) (Z.rem (k - a * v) 9 + 9)
          (Znth (2 * (Z.rem (k - a * v) 9 + 9)) position_values_2 0)
          Hfirst PreH1 y Hy).
Qed.

Lemma proof_of_solver_entail_wit_12_20 : solver_entail_wit_12_20.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_20_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_21_split_goal_1 : solver_entail_wit_12_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_high.
  - lia.
  - exact PreH68.
  - intros [x y] Hnew.
    unfold PrefixEligiblePair in Hnew.
    destruct Hnew as [Hpair Hresidue].
    destruct (Z_lt_ge_dec (PairFirstResidue text w_pre (x, y)) a).
    + left. unfold PrefixEligiblePair. split; [exact Hpair | lia].
    + assert (Hresidue_eq : PairFirstResidue text w_pre (x, y) = a) by lia.
      exfalso.
      assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
      {
        destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
        unfold ztriple_1, ztriple_2, ztriple_3 in PreH51, PreH52, PreH53.
        cbn in PreH51, PreH52, PreH53. subst. reflexivity.
      }
      rewrite Hqeq in Hpair.
      pose proof (PreH65 (l - 1) r ltac:(lia)) as Hdiff.
      pose proof
        (candidate_windows__query_preserve_high
          text prefix_values_2 n w_pre l r k v a (x, y)
          PreH30 PreH54 PreH55 PreH56 (conj PreH57 PreH58)
          (fun j Hj => proj1 (PreH38 j Hj)) (proj1 Hdiff) PreH64 PreH59
          Hpair Hresidue_eq) as [Hx Hy].
      pose proof
        (nonnegative_rem_as_mod__query_preserve_high (k - a * v) ltac:(lia)) as Hmod.
      rewrite <- Hmod, <- PreH2 in Hy.
      rewrite <- PreH2 in PreH1.
      unfold FlatPositionsPrefix, PositionsPrefix in PreH66.
      specialize (PreH66 a ltac:(lia)).
      rewrite flat_position_row__query_preserve_high in PreH66 by lia.
      cbn in PreH66.
      destruct PreH66 as [_ Hsecond].
      change
        (SecondWindowStart text w_pre (n - w_pre + 1) a
          (Znth (2 * a) position_values_2 (-1))
          (Znth (2 * a + 1) position_values_2 (-1))) in Hsecond.
      rewrite (Znth_indep position_values_2 (2 * a) (-1) 0) in Hsecond by lia.
      rewrite (Znth_indep position_values_2 (2 * a + 1) (-1) 0) in Hsecond by lia.
      pose proof
        (second_window_negative_unique__query_preserve_high
          text w_pre (n - w_pre + 1) a
          (Znth (2 * a) position_values_2 0)
          (Znth (2 * a + 1) position_values_2 0)
          Hsecond PreH1 x Hx) as Hxeq.
      pose proof
        (second_window_negative_unique__query_preserve_high
          text w_pre (n - w_pre + 1) a
          (Znth (2 * a) position_values_2 0)
          (Znth (2 * a + 1) position_values_2 0)
          Hsecond PreH1 y Hy) as Hyeq.
      unfold QueryPair in Hpair. cbn in Hpair. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_21 : solver_entail_wit_12_21.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_21_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_22_split_goal_1 : solver_entail_wit_12_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply query_best_prefix_step_preserve__query_preserve_high.
  - lia.
  - exact PreH68.
  - intros [x y] Hnew.
    unfold PrefixEligiblePair in Hnew.
    destruct Hnew as [Hpair Hresidue].
    destruct (Z_lt_ge_dec (PairFirstResidue text w_pre (x, y)) a).
    + left. unfold PrefixEligiblePair. split; [exact Hpair | lia].
    + assert (Hresidue_eq : PairFirstResidue text w_pre (x, y) = a) by lia.
      exfalso.
      assert (Hqeq : Znth z qs __default__Prod__Prod_Z_Z_Z = ((l, r), k)).
      {
        destruct (Znth z qs __default__Prod__Prod_Z_Z_Z) as [[ql qr] qk].
        unfold ztriple_1, ztriple_2, ztriple_3 in PreH51, PreH52, PreH53.
        cbn in PreH51, PreH52, PreH53. subst. reflexivity.
      }
      rewrite Hqeq in Hpair.
      pose proof (PreH65 (l - 1) r ltac:(lia)) as Hdiff.
      pose proof
        (candidate_windows__query_preserve_high
          text prefix_values_2 n w_pre l r k v a (x, y)
          PreH30 PreH54 PreH55 PreH56 (conj PreH57 PreH58)
          (fun j Hj => proj1 (PreH38 j Hj)) (proj1 Hdiff) PreH64 PreH59
          Hpair Hresidue_eq) as [_ Hy].
      pose proof
        (nonnegative_rem_as_mod__query_preserve_high (k - a * v) ltac:(lia)) as Hmod.
      rewrite <- Hmod in Hy.
      unfold FlatPositionsPrefix, PositionsPrefix in PreH66.
      specialize (PreH66 (Z.rem (k - a * v) 9) ltac:(lia)).
      rewrite flat_position_row__query_preserve_high in PreH66 by lia.
      cbn in PreH66.
      destruct PreH66 as [Hfirst _].
      change
        (FirstWindowStart text w_pre (n - w_pre + 1)
          (Z.rem (k - a * v) 9)
          (Znth (2 * Z.rem (k - a * v) 9) position_values_2 (-1)))
        in Hfirst.
      rewrite
        (Znth_indep position_values_2
          (2 * Z.rem (k - a * v) 9) (-1) 0) in Hfirst by lia.
      exact
        (first_window_negative_none__query_preserve_high
          text w_pre (n - w_pre + 1) (Z.rem (k - a * v) 9)
          (Znth (2 * Z.rem (k - a * v) 9) position_values_2 0)
          Hfirst PreH1 y Hy).
Qed.

Lemma proof_of_solver_entail_wit_12_22 : solver_entail_wit_12_22.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_22_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_1 : solver_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace a with 9 in * by lia.
  auto.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_2 : solver_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_3 : solver_entail_wit_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_13_split_goal_4 : solver_entail_wit_13_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_13_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_1 : solver_entail_wit_14_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (Z.shiftl 1 30) with 1073741824 in * by reflexivity.
  subst best1.
  eapply query_output_append_none__query_output; try eassumption; try lia.
  eapply query_best_full_no_pair__query_output; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_2 : solver_entail_wit_14_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_3 : solver_entail_wit_14_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_4 : solver_entail_wit_14_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_1 : solver_entail_wit_14_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (Z.shiftl 1 30) with 1073741824 in * by reflexivity.
  eapply query_output_append_found__query_output; try eassumption; try lia.
  eapply query_best_full_minimum__query_output; eauto.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_2 : solver_entail_wit_14_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_3 : solver_entail_wit_14_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_4 : solver_entail_wit_14_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hzm : z = m_pre) by lia.
  rewrite <- Hzm.
  eassumption.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_2 : solver_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_3 : solver_entail_wit_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_4 : solver_entail_wit_15_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_15_split_goal_4.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (query_output_prefix_full__final_result
       w_pre text qs m_pre out1_data_now out2_data_now
       __default__Prod_Z_Z PreH10 PreH20) as Hfull.
  destruct Hfull as
    (out & Hspec & Hout & Hout1 & Hout2 & Hcomponents).
  Exists out2_data_now out1_data_now out.
  split_pure_spatial.
  - rewrite PreH2, PreH3.
    repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hout.
    + dump_pre_spatial. exact Hout1.
    + dump_pre_spatial. exact Hout2.
    + dump_pre_spatial. exact Hcomponents.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_solver_which_implies_wit_1_split_goal_1 : solver_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_which_implies_wit_1_split_goal_2 : solver_which_implies_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_which_implies_wit_1_split_goal_3 : solver_which_implies_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold valid_string, all_ascii, no_inner_nul.
  split; intros i Hi; specialize (PreH3 i Hi) as [Hlo Hhi]; lia.
Qed.

Lemma proof_of_solver_which_implies_wit_1_split_goal_spatial : solver_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_which_implies_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_which_implies_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_which_implies_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_which_implies_wit_1_split_goal_3.
Qed.
