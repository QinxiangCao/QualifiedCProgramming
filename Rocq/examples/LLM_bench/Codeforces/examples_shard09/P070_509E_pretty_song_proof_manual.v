From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P070_509E_pretty_song_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P070_509E_pretty_song_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P070_509E_pretty_song_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_24_split_goal_1 : solver_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH13 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_2 : solver_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH13 i ltac:(lia)).
  dump_pre_spatial.
  lia.
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
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH11 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH11 i ltac:(lia)).
  dump_pre_spatial.
  lia.
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
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH9 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_2 : solver_safety_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH9 i ltac:(lia)).
  dump_pre_spatial.
  lia.
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
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH10 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_27_split_goal_2 : solver_safety_wit_27_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH10 i ltac:(lia)).
  dump_pre_spatial.
  lia.
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
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH12 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_28_split_goal_2 : solver_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH12 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_29_split_goal_1 : solver_safety_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH14 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_29_split_goal_2 : solver_safety_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH14 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_29_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_29_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_30_split_goal_1 : solver_safety_wit_30_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH14 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_30_split_goal_2 : solver_safety_wit_30_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i by lia.
  rewrite app_Znth1 by lia.
  specialize (PreH14 i ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_30_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_30_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_42_split_goal_1 : solver_safety_wit_42_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace ((i - 1) - 0) with (i - 1) by lia.
  destruct (PreH9 i ltac:(lia)) as [Hpre_nonneg Hpre_upper].
  destruct (PreH10 (i - 1) ltac:(lia)) as [Hpp_nonneg Hpp_upper].
  rewrite Z.quot_div_nonneg in Hpp_upper by nia.
  assert (((i - 1) * ((i - 1) + 1)) / 2 <= 125000250000)
    by (apply Z.div_le_upper_bound; nia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_42_split_goal_2 : solver_safety_wit_42_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  replace ((i - 1) - 0) with (i - 1) by lia.
  destruct (PreH9 i ltac:(lia)) as [Hpre_nonneg Hpre_upper].
  destruct (PreH10 (i - 1) ltac:(lia)) as [Hpp_nonneg Hpp_upper].
  lia.
Qed.

Lemma proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_42_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_42_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_46_split_goal_1 : solver_safety_wit_46_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (PreH11 n_pre ltac:(lia)) as [Hpp_n_nonneg Hpp_n_upper].
  destruct (PreH11 (L0 - 1) ltac:(lia)) as [Hpp_L_nonneg Hpp_L_upper].
  rewrite Z.quot_div_nonneg in Hpp_n_upper by nia.
  rewrite Z.quot_div_nonneg in Hpp_L_upper by nia.
  assert ((n_pre * (n_pre + 1)) / 2 <= 125000250000)
    by (apply Z.div_le_upper_bound; nia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_46_split_goal_2 : solver_safety_wit_46_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (PreH11 n_pre ltac:(lia)) as [Hpp_n_nonneg Hpp_n_upper].
  destruct (PreH11 (L0 - 1) ltac:(lia)) as [Hpp_L_nonneg Hpp_L_upper].
  rewrite Z.quot_div_nonneg in Hpp_n_upper by nia.
  rewrite Z.quot_div_nonneg in Hpp_L_upper by nia.
  assert (((L0 - 1) * ((L0 - 1) + 1)) / 2 <= 125000250000)
    by (apply Z.div_le_upper_bound; nia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_46 : solver_safety_wit_46.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_46_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_46_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_52_split_goal_1 : solver_safety_wit_52_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (PreH11 n_pre ltac:(lia)) as [Hpp_n_nonneg Hpp_n_upper].
  destruct (PreH11 (L0 - 1) ltac:(lia)) as [Hpp_L_nonneg Hpp_L_upper].
  destruct (PreH11 (n_pre - L0) ltac:(lia)) as [Hpp_lo_nonneg Hpp_lo_upper].
  rewrite Z.quot_div_nonneg in Hpp_n_upper by nia.
  rewrite Z.quot_div_nonneg in Hpp_L_upper by nia.
  rewrite Z.quot_div_nonneg in Hpp_lo_upper by nia.
  assert ((n_pre * (n_pre + 1)) / 2 <= 125000250000)
    by (apply Z.div_le_upper_bound; nia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_52_split_goal_2 : solver_safety_wit_52_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (PreH11 n_pre ltac:(lia)) as [Hpp_n_nonneg Hpp_n_upper].
  destruct (PreH11 (L0 - 1) ltac:(lia)) as [Hpp_L_nonneg Hpp_L_upper].
  destruct (PreH11 (n_pre - L0) ltac:(lia)) as [Hpp_lo_nonneg Hpp_lo_upper].
  rewrite Z.quot_div_nonneg in Hpp_n_upper by nia.
  rewrite Z.quot_div_nonneg in Hpp_L_upper by nia.
  rewrite Z.quot_div_nonneg in Hpp_lo_upper by nia.
  assert (((L0 - 1) * ((L0 - 1) + 1)) / 2 <= 125000250000)
    by (apply Z.div_le_upper_bound; nia).
  assert (((n_pre - L0) * ((n_pre - L0) + 1)) / 2 <= 125000250000)
    by (apply Z.div_le_upper_bound; nia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_52 : solver_safety_wit_52.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_52_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_52_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (0 :: nil).
  split_pure_spatial.
  - replace (0 + 1) with 1 in * by lia.
    sep_apply_l_atomic (Int64Array.seg_single pre_pre 0 0).
    sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
         pre_pre 0 (n_pre + 1)).
    + dump_pre_spatial. lia.
    + replace (0 + 1) with 1 by lia.
      repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + intros k Hk.
      assert (k = 0) by lia. subst k.
      rewrite Znth0_cons. lia.
    + apply vowel_prefix_counts_single_zero__prefix_init_exit.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_spatial : solver_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Int64Array.missing_i_shape_unfold; try lia.
  Left.
  repeat cancel.
  split_pure_spatial.
  - cancel (Int64Array.seg_shape pre_pre (i + 1 + 1) (n_pre + 1)).
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hvowel : Vowel (Znth i text 0)).
  { unfold Vowel. right; right; right; right; left. exact PreH1. }
  replace (i - 0) with i by lia.
  assert (Hread :
    Znth i (pre_values_2 ++ (old_next :: nil)) 0 = Znth i pre_values_2 0).
  { rewrite app_Znth1; lia. }
  rewrite Hread.
  assert (Hreplace :
    replace_Znth (i + 1) (Znth i pre_values_2 0 + 1)
      (pre_values_2 ++ (old_next :: nil)) =
    pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  { rewrite <- PreH12. apply replace_Znth_app_last__prefix_vowel_append. }
  rewrite Hreplace.
  Exists (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
         pre_pre (i + 1) (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (Int64Array.full_to_seg pre_pre ((i + 1) + 1)
           (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil))).
      repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + dump_pre_spatial.
      eapply prefix_count_bounds_extend__prefix_vowel_append; eauto.
    + dump_pre_spatial.
      eapply vowel_prefix_counts_extend_vowel__prefix_vowel_append; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hvowel : Vowel (Znth i text 0)).
  { unfold Vowel. left. exact PreH1. }
  replace (i - 0) with i by lia.
  assert (Hread :
    Znth i (pre_values_2 ++ (old_next :: nil)) 0 = Znth i pre_values_2 0).
  { rewrite app_Znth1; lia. }
  rewrite Hread.
  assert (Hreplace :
    replace_Znth (i + 1) (Znth i pre_values_2 0 + 1)
      (pre_values_2 ++ (old_next :: nil)) =
    pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  { rewrite <- PreH10. apply replace_Znth_app_last__prefix_vowel_append. }
  rewrite Hreplace.
  Exists (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
         pre_pre (i + 1) (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (Int64Array.full_to_seg pre_pre ((i + 1) + 1)
           (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil))).
      repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + dump_pre_spatial.
      eapply prefix_count_bounds_extend__prefix_vowel_append; eauto.
    + dump_pre_spatial.
      eapply vowel_prefix_counts_extend_vowel__prefix_vowel_append; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hvowel : Vowel (Znth i text 0)).
  { unfold Vowel. right; right; left. exact PreH1. }
  replace (i - 0) with i by lia.
  assert (Hread :
    Znth i (pre_values_2 ++ (old_next :: nil)) 0 = Znth i pre_values_2 0).
  { rewrite app_Znth1; lia. }
  rewrite Hread.
  assert (Hreplace :
    replace_Znth (i + 1) (Znth i pre_values_2 0 + 1)
      (pre_values_2 ++ (old_next :: nil)) =
    pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  { rewrite <- PreH8. apply replace_Znth_app_last__prefix_vowel_append. }
  rewrite Hreplace.
  Exists (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
         pre_pre (i + 1) (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (Int64Array.full_to_seg pre_pre ((i + 1) + 1)
           (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil))).
      repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + dump_pre_spatial.
      eapply prefix_count_bounds_extend__prefix_vowel_append; eauto.
    + dump_pre_spatial.
      eapply vowel_prefix_counts_extend_vowel__prefix_vowel_append; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hvowel : Vowel (Znth i text 0)).
  { unfold Vowel. right; left. exact PreH1. }
  replace (i - 0) with i by lia.
  assert (Hread :
    Znth i (pre_values_2 ++ (old_next :: nil)) 0 = Znth i pre_values_2 0).
  { rewrite app_Znth1; lia. }
  rewrite Hread.
  assert (Hreplace :
    replace_Znth (i + 1) (Znth i pre_values_2 0 + 1)
      (pre_values_2 ++ (old_next :: nil)) =
    pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  { rewrite <- PreH9. apply replace_Znth_app_last__prefix_vowel_append. }
  rewrite Hreplace.
  Exists (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
         pre_pre (i + 1) (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (Int64Array.full_to_seg pre_pre ((i + 1) + 1)
           (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil))).
      repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + dump_pre_spatial.
      eapply prefix_count_bounds_extend__prefix_vowel_append; eauto.
    + dump_pre_spatial.
      eapply vowel_prefix_counts_extend_vowel__prefix_vowel_append; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_5 : solver_entail_wit_4_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hvowel : Vowel (Znth i text 0)).
  { unfold Vowel. right; right; right; left. exact PreH1. }
  replace (i - 0) with i by lia.
  assert (Hread :
    Znth i (pre_values_2 ++ (old_next :: nil)) 0 = Znth i pre_values_2 0).
  { rewrite app_Znth1; lia. }
  rewrite Hread.
  assert (Hreplace :
    replace_Znth (i + 1) (Znth i pre_values_2 0 + 1)
      (pre_values_2 ++ (old_next :: nil)) =
    pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  { rewrite <- PreH11. apply replace_Znth_app_last__prefix_vowel_append. }
  rewrite Hreplace.
  Exists (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
         pre_pre (i + 1) (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (Int64Array.full_to_seg pre_pre ((i + 1) + 1)
           (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil))).
      repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + dump_pre_spatial.
      eapply prefix_count_bounds_extend__prefix_vowel_append; eauto.
    + dump_pre_spatial.
      eapply vowel_prefix_counts_extend_vowel__prefix_vowel_append; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_6 : solver_entail_wit_4_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hvowel : Vowel (Znth i text 0)).
  { unfold Vowel. right; right; right; right; right. exact PreH1. }
  replace (i - 0) with i by lia.
  assert (Hread :
    Znth i (pre_values_2 ++ (old_next :: nil)) 0 = Znth i pre_values_2 0).
  { rewrite app_Znth1; lia. }
  rewrite Hread.
  assert (Hreplace :
    replace_Znth (i + 1) (Znth i pre_values_2 0 + 1)
      (pre_values_2 ++ (old_next :: nil)) =
    pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  { rewrite <- PreH13. apply replace_Znth_app_last__prefix_vowel_append. }
  rewrite Hreplace.
  Exists (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil)).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
         pre_pre (i + 1) (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (Int64Array.full_to_seg pre_pre ((i + 1) + 1)
           (pre_values_2 ++ ((Znth i pre_values_2 0 + 1) :: nil))).
      repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + dump_pre_spatial.
      eapply prefix_count_bounds_extend__prefix_vowel_append; eauto.
    + dump_pre_spatial.
      eapply vowel_prefix_counts_extend_vowel__prefix_vowel_append; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_7 : solver_entail_wit_4_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnonvowel : ~ Vowel (Znth i text 0)).
  {
    unfold Vowel.
    intros [H | [H | [H | [H | [H | H]]]]];
      contradiction.
  }
  replace (i - 0) with i by lia.
  assert (Hread :
    Znth i (pre_values_2 ++ (old_next :: nil)) 0 =
    Znth i pre_values_2 0).
  { rewrite app_Znth1; lia. }
  rewrite Hread.
  replace (Znth i pre_values_2 0 + 0) with (Znth i pre_values_2 0) by lia.
  assert (Hreplace :
    replace_Znth (i + 1) (Znth i pre_values_2 0)
      (pre_values_2 ++ (old_next :: nil)) =
    pre_values_2 ++ (Znth i pre_values_2 0 :: nil)).
  {
    rewrite <- PreH13.
    apply replace_Znth_app_last__prefix_nonvowel_append.
  }
  rewrite Hreplace.
  Exists (pre_values_2 ++ (Znth i pre_values_2 0 :: nil)).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
         pre_pre (i + 1) (n_pre + 1)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (Int64Array.full_to_seg pre_pre ((i + 1) + 1)
           (pre_values_2 ++ (Znth i pre_values_2 0 :: nil))).
      repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + dump_pre_spatial.
      eapply prefix_count_bounds_extend_nonvowel__prefix_nonvowel_append;
        eauto.
    + dump_pre_spatial.
      eapply vowel_prefix_counts_extend_nonvowel__prefix_nonvowel_append;
        eauto.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  sep_apply_l_atomic
    (Int64Array.full_shape_split_to_missing_i_shape pp_pre 0 (n_pre + 1)).
  - dump_pre_spatial. lia.
  - Intros old_pp0.
    Exists old_pp0 pre_values_2.
    split_pure_spatial.
    + sep_apply_l_atomic
        (Int64Array.seg_split_to_missing_i pre_pre 0 0 (n_pre + 1)
           pre_values_2 0).
      * dump_pre_spatial. lia.
      * rewrite Int64Array.seg_shape_empty.
        cancel (CharArray.full s_pre n_pre text).
        cancel (Int64Array.full_shape term_pre n_pre).
        cancel (((pre_pre + (0 * sizeof(INT64)))) # Int64 |->
          (Znth 0 pre_values_2 0)).
        cancel (Int64Array.missing_i pre_pre 0 0 (n_pre + 1)
          pre_values_2).
        cancel (((pp_pre + (0 * sizeof(INT64)))) # Int64 |-> old_pp0).
        cancel (Int64Array.missing_i_shape pp_pre 0 0 (n_pre + 1)).
        cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (Znth 0 pre_values_2 0 :: nil) pre_values_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.missing_i_merge_to_full pre_pre 0 (n_pre + 1)
         (Znth 0 pre_values_2 0) pre_values_2).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth by lia.
      sep_apply_l_atomic
        (Int64Array.seg_single pp_pre 0 (Znth 0 pre_values_2 0)).
      sep_apply_l_atomic
        (Int64Array.missing_i_shape_to_seg_shape_head pp_pre 0 (n_pre + 1)).
      * dump_pre_spatial. lia.
      * replace (0 + 1) with 1 by lia.
        repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + reflexivity.
    + apply prefix_count_totals_init__prefix_totals.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (k_3 = 0) by lia.
  subst k_3.
  specialize (PreH6 0 ltac:(lia)).
  specialize (PreH10 0 ltac:(lia)).
  unfold SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.sum_range in PreH10.
  rewrite SumLib.ZRange.sum_Z_range_single in PreH10.
  rewrite PreH10.
  simpl.
  exact PreH6.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
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

Lemma proof_of_solver_entail_wit_8_split_goal_spatial : solver_entail_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Int64Array.missing_i_shape_unfold; try lia.
  Left.
  repeat cancel.
  split_pure_spatial.
  - cancel (Int64Array.seg_shape pp_pre (i + 1) (n_pre + 1)).
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hreplace :
    replace_Znth i
      (Znth (i - 1) pp_values_2 0 + Znth i pre_values_2 0)
      (pp_values_2 ++ old_next :: nil) =
    pp_values_2 ++
      (Znth (i - 1) pp_values_2 0 + Znth i pre_values_2 0) :: nil).
  { rewrite <- PreH8.
    apply replace_Znth_app_last__prefix_totals. }
  replace (i - 1 - 0) with (i - 1) by lia.
  rewrite Hreplace.
  set (pp_values := pp_values_2 ++
    (Znth (i - 1) pp_values_2 0 + Znth i pre_values_2 0) :: nil).
  pose proof
    (prefix_count_totals_extend__prefix_totals
      pre_values_2 pp_values_2 i PreH5 ltac:(lia) PreH8
      ltac:(intros k Hk; apply PreH9; lia) PreH10 PreH12)
    as [Htotals Hbounds].
  Exists pp_values pre_values_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.full_to_seg pp_pre (i + 1) pp_values).
    sep_apply_l_atomic
      (Int64Array.missing_i_shape_to_seg_shape_head
        pp_pre i (n_pre + 1)).
    + dump_pre_spatial. lia.
    + repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    + subst pp_values.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre + 1) by lia.
  subst i.
  Exists pp_values_2 pre_values_2.
  split_pure_spatial.
  - rewrite H.
    rewrite Int64Array.seg_shape_empty.
    sep_apply_l_atomic
      (Int64Array.seg_to_full pp_pre 0 (n_pre + 1) pp_values_2).
    replace (pp_pre + 0 * sizeof(INT64)) with pp_pre by lia.
    replace (n_pre + 1 - 0) with (n_pre + 1) by lia.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    intros k Hk.
    apply PreH11.
    rewrite H.
    exact Hk.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists pp_values_2 pre_values_2 (@nil Z).
  split_pure_spatial.
  - rewrite (Int64Array.seg_empty term_pre 0 0).
    rewrite (Int64Array.seg_shape_empty term_pre 0).
    sep_apply_l_atomic (Int64Array.full_shape_split_to_seg_shape term_pre 0 n_pre).
    + dump_pre_spatial. lia.
    + replace (1 - 1) with 0 by lia.
      rewrite (Int64Array.seg_shape_empty term_pre 0).
      cancel.
      normalize. cancel.
  - split_pures; dump_pre_spatial; try reflexivity; try lia; try assumption.
    + unfold PrettyTermPrefix. intros len Hlen.
      rewrite Zlength_nil in Hlen. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_3 : solver_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_4 : solver_entail_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_spatial : solver_entail_wit_12_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (Int64Array.missing_i_shape_unfold term_pre (L0 - 1) (L0 - 1) n_pre); try lia.
  Left.
  split_pure_spatial.
  - cancel (Int64Array.seg_shape term_pre (L0 - 1 + 1) n_pre).
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (new_term :=
    (Znth n_pre pp_values_2 0 - Znth (L0 - 1) pp_values_2 0 -
      Znth (n_pre - L0) pp_values_2 0)%Z).
  assert (Hnew : new_term = PrettyTerm text L0).
  {
    unfold new_term.
    apply (pretty_term_from_prefix_totals__pretty_terms
      text pre_values_2 pp_values_2 n_pre L0);
      try assumption; try lia.
  }
  pose proof (pretty_term_bounds__pretty_terms text n_pre L0 ltac:(lia) ltac:(lia))
    as Hpretty_bounds.
  assert (Hnew_bounds : (0 <= new_term <= n_pre * n_pre)%Z) by
    (rewrite Hnew; exact Hpretty_bounds).
  assert (Hterm_prefix : PrettyTermPrefix text (terms_2 ++ new_term :: nil)).
  {
    apply pretty_term_prefix_extend__pretty_terms with (len := L0);
      assumption.
  }
  assert (Hterm_bounds : forall k,
    (0 <= k < L0)%Z ->
    (0 <= Znth k (terms_2 ++ new_term :: nil) 0 <= n_pre * n_pre)%Z).
  {
    intros k Hk.
    destruct (Z_lt_ge_dec k (L0 - 1)) as [Hlt | Hge].
    - rewrite app_Znth1 by lia. apply PreH12. lia.
    - assert (k = L0 - 1) by lia. subst k.
      rewrite app_Znth2 by lia.
      replace (L0 - 1 - Zlength terms_2)%Z with 0%Z by lia.
      rewrite Znth0_cons. exact Hnew_bounds.
  }
  assert (Hreplace :
    replace_Znth (L0 - 1) new_term (terms_2 ++ old_next :: nil) =
    terms_2 ++ new_term :: nil).
  {
    rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (L0 - 1 - Zlength terms_2)%Z with 0%Z by lia.
    simpl. reflexivity.
  }
  Exists pp_values_2 pre_values_2 (terms_2 ++ new_term :: nil).
  split_pure_spatial.
  - unfold new_term in Hreplace |- *.
    rewrite Hreplace.
    fold new_term.
    replace (L0 - 1 + 1)%Z with L0 by lia.
    sep_apply_l_atomic (Int64Array.full_to_seg term_pre L0
      (terms_2 ++ new_term :: nil)).
    sep_apply_l_atomic (Int64Array.missing_i_shape_to_seg_shape_head
      term_pre (L0 - 1) n_pre).
    + dump_pre_spatial. lia.
    + replace (L0 - 1 + 1)%Z with L0 by lia.
      replace (L0 + 1 - 1)%Z with L0 by lia.
      cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia;
      try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    + intros k Hk. apply Hterm_bounds. lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HL : L0 = n_pre + 1) by lia.
  assert (Hterms_len : Zlength terms_2 = Zlength text) by lia.
  assert (Htable : PrettyTermTable text terms_2).
  {
    split.
    - exact Hterms_len.
    - intros len Hlen.
      apply PreH16.
      rewrite Hterms_len.
      exact Hlen.
  }
  destruct (spec_pretty_terms_exists__final_result text terms_2 Htable)
    as [real_out [Hspec Hpretty]].
  subst L0.
  Exists terms_2 real_out.
  split_pure_spatial.
  - replace (n_pre + 1 - 1) with n_pre by lia.
    rewrite Int64Array.seg_shape_empty.
    sep_apply_l_atomic (Int64Array.seg_to_full term_pre 0 n_pre terms_2).
    replace (term_pre + 0 * sizeof(INT64)) with term_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    sep_apply_l_atomic
      (Int64Array.full_to_full_shape pre_pre (n_pre + 1) pre_values).
    sep_apply_l_atomic
      (Int64Array.full_to_full_shape pp_pre (n_pre + 1) pp_values).
    cancel.
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hpretty.
Qed.
