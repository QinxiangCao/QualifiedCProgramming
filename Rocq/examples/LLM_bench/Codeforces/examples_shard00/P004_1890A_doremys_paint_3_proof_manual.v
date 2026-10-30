From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P004_1890A_doremys_paint_3_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P004_1890A_doremys_paint_3_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold PaintScanState in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold PaintScanState in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_1 : solver_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold PaintScanState in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_2 : solver_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold PaintScanState in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold PaintScanState in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold PaintScanState in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold PaintScanState in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold PaintScanState in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold PaintScanState in *; lia).
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold PaintScanState in *; lia).
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
  apply paint_scan_state_init__scan_transitions.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH4.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply paint_scan_state_step_x__scan_transitions; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply paint_scan_state_step_first_y__scan_transitions; eauto; try lia.
  specialize (PreH9 i).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply paint_scan_state_step_y__scan_transitions; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PaintScanState in PreH9.
  destruct PreH9 as
    (Hi_bounds & Hx & Hcx_bounds & Hcy_bounds & Hsum & Hy_zero &
     Hy_distinct & Hcx_occ & Hcy_occ & Hcover).
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Hy : y = -1).
  { apply (proj2 Hy_zero). exact PreH1. }
  assert (Hall : forall j, 0 <= j < Zlength input -> Znth j input 0 = x).
  {
    intros j Hj.
    specialize (Hcover j ltac:(lia)).
    destruct Hcover as [Hjx | [Hyn _]].
    - exact Hjx.
    - exfalso. apply Hyn. exact Hy.
  }
  unfold Spec. split.
  - right. reflexivity.
  - split.
    + intros _. exists input. split.
      * apply Permutation_refl.
      * apply good_adjacent_sums_uniform__accepted_results with (x := x).
        exact Hall.
    + intros _. reflexivity.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  split.
  - left. reflexivity.
  - split.
    + intro H. lia.
    + intros [b [Hperm Hgood]].
      pose proof (paint_scan_state_full_count_balance__rejected_results
        input b n_pre i x y cx cy PreH6 PreH5 PreH4 PreH9 PreH3
        PreH11 Hperm Hgood) as Hbal.
      rewrite Z.abs_le in Hbal.
      lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PaintScanState in PreH11.
  destruct PreH11 as
    (Hi_bounds & Hx & Hcx_bounds & Hcy_bounds & Hsum & Hy_zero &
     Hy_distinct & Hcx_occ & Hcy_occ & Hcover).
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Hy : y <> -1).
  { intro Hy. apply PreH3. apply (proj1 Hy_zero). exact Hy. }
  assert (Hxy : x <> y).
  { intro Hxy. apply (Hy_distinct Hy). symmetry. exact Hxy. }
  assert (Hsub : sublist 0 n_pre input = input).
  {
    rewrite PreH5.
    unfold sublist. simpl.
    rewrite Zlength_correct, Nat2Z.id.
    apply firstn_all.
  }
  assert (Hcover_all : forall j, 0 <= j < Zlength input ->
    Znth j input 0 = x \/ Znth j input 0 = y).
  {
    intros j Hj.
    specialize (Hcover j ltac:(lia)).
    destruct Hcover as [Hjx | [_ Hjy]].
    - left. exact Hjx.
    - right. exact Hjy.
  }
  assert (Hcx : cx = Z.of_nat (count_occ Z.eq_dec input x)).
  { rewrite Hcx_occ. unfold Occurrences. now rewrite Hi, Hsub. }
  assert (Hcy : cy = Z.of_nat (count_occ Z.eq_dec input y)).
  { rewrite (Hcy_occ Hy). unfold Occurrences. now rewrite Hi, Hsub. }
  unfold Spec. split.
  - right. reflexivity.
  - split.
    + intros _.
      apply balanced_two_value_permutation__accepted_results with (x := x) (y := y).
      * exact Hxy.
      * exact Hcover_all.
      * rewrite <- Hcy, <- Hcx. exact PreH1.
      * rewrite <- Hcx, <- Hcy. exact PreH2.
    + intros _. reflexivity.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  split.
  - left. reflexivity.
  - split.
    + intro H. lia.
    + intros [b [Hperm Hgood]].
      pose proof (paint_scan_state_full_count_balance__rejected_results
        input b n_pre i x y cx cy PreH5 PreH4 PreH3 PreH8 PreH2
        PreH10 Hperm Hgood) as Hbal.
      rewrite Z.abs_le in Hbal.
      lia.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_5_split_goal_1 : solver_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  split.
  - left. reflexivity.
  - split.
    + intro H. lia.
    + intros [b [Hperm Hgood]].
      destruct PreH11 as
        [Hbounds [Hx [Hcx [Hcy [Htotal [Hsentinel [Hyx
          [Hcxocc [Hcyocc Hcover]]]]]]]]].
      assert (Hxy : x <> y).
      { intro Hxy. apply (Hyx PreH2). symmetry. exact Hxy. }
      assert (Hinx : In x input).
      { rewrite Hx.
        apply Znth_in_range__rejected_results.
        rewrite <- PreH5. lia. }
      assert (Hcy0 : cy <> 0).
      { intro Hcyzero.
        apply PreH2.
        apply (proj2 Hsentinel). exact Hcyzero. }
      specialize (Hcyocc PreH2).
      assert (Hiny_prefix : In y (sublist 0 i input)).
      { apply (count_occ_In Z.eq_dec).
        unfold Occurrences in Hcyocc.
        lia. }
      assert (Hiny : In y input).
      { eapply In_sublist_from_zero__rejected_results. exact Hiny_prefix. }
      assert (Hinz : In (Znth i input 0) input).
      { apply Znth_in_range__rejected_results.
        rewrite <- PreH5. lia. }
      exfalso.
      eapply good_adjacent_sums_no_three_distinct__rejected_results
        with (a := input) (b := b) (x := x) (y := y)
             (z := Znth i input 0); eauto; congruence.
Qed.

Lemma proof_of_solver_return_wit_5 : solver_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_5_split_goal_1.
Qed.
