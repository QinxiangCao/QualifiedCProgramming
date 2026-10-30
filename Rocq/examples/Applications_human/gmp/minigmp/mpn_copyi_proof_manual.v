From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_copyi_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_copyi_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_copyi_entail_wit_1_off_zero_split_goal_spatial : mpn_copyi_entail_wit_1_off_zero_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst off_shifted.
  sep_apply UIntArray.full_to_seg.
  replace (n_pre + 0) with n_pre by lia.
  sep_apply (UIntArray.seg_split_to_seg d_pre 0 0 n_pre l_shifted); try lia.
  try rewrite Zsublist_nil by lia.
  try rewrite sublist_self by lia.
  try rewrite UIntArray.seg_empty.
  replace (sublist 0 (0 - 0) l_shifted) with (@nil Z)
    by (rewrite (Zsublist_nil l_shifted 0 (0 - 0)); [reflexivity | lia]).
  try rewrite UIntArray.seg_empty.
  replace (sublist (0 - 0) (n_pre - 0) l_shifted) with (sublist 0 n_pre l_shifted) by (f_equal; lia).
  replace (sublist 0 n_pre l_shifted) with l_shifted.
  - normalize.
    Intros.
    repeat cancel.
  - replace n_pre with (n_pre + 0) by lia.
    rewrite <- PreH5.
    rewrite sublist_self; reflexivity.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_1_off_zero : mpn_copyi_entail_wit_1_off_zero.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_1_off_zero_split_goal_spatial.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_2_off_pos_split_goal_spatial : mpn_copyi_entail_wit_2_off_pos_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply UIntArray.full_to_seg.
  sep_apply (UIntArray.seg_split_to_seg d_pre 0 0 (n_pre + off_shifted) l_shifted); try lia.
  try rewrite Zsublist_nil by lia.
  try rewrite UIntArray.seg_empty.
  replace (sublist (0 - 0) (n_pre + off_shifted - 0) l_shifted)
    with (sublist 0 (n_pre + off_shifted) l_shifted) by (f_equal; lia).
  normalize.
  Intros.
  repeat cancel.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_2_off_pos : mpn_copyi_entail_wit_2_off_pos.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_2_off_pos_split_goal_spatial.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_3_off_zero_split_goal_1 : mpn_copyi_entail_wit_3_off_zero_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_copyi_entail_wit_3_off_zero : mpn_copyi_entail_wit_3_off_zero.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_3_off_zero_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_4_off_pos_split_goal_1 : mpn_copyi_entail_wit_4_off_pos_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (off_shifted + 0) with off_shifted by lia.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_4_off_pos : mpn_copyi_entail_wit_4_off_pos.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_4_off_pos_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_5_non_alias_split_goal_1 : mpn_copyi_entail_wit_5_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (Zlength_nonneg l). lia.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_5_non_alias_split_goal_2 : mpn_copyi_entail_wit_5_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_copyi_entail_wit_5_non_alias : mpn_copyi_entail_wit_5_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_copyi_entail_wit_5_non_alias_split_goal_1.
  - Goal_apply proof_of_mpn_copyi_entail_wit_5_non_alias_split_goal_2.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_6_off_zero_split_goal_1 : mpn_copyi_entail_wit_6_off_zero_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (sublist_split 0 (i + 1) i); try lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_6_off_zero : mpn_copyi_entail_wit_6_off_zero.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_6_off_zero_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_7_off_pos_split_goal_1 : mpn_copyi_entail_wit_7_off_pos_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (off_shifted + (i + 1)) with (off_shifted + i + 1) by lia.
  rewrite (sublist_split off_shifted (off_shifted + i + 1)
    (off_shifted + i) l_shifted) by lia.
  f_equal.
  replace (i - i) with 0 by lia.
  rewrite (sublist_single 0 (off_shifted + i) l_shifted) by lia.
  rewrite (sublist_single 0 i l_shifted) by lia.
  unfold replace_Znth.
  simpl.
  rewrite Znth0_cons.
  dump_pre_spatial.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_7_off_pos_split_goal_spatial : mpn_copyi_entail_wit_7_off_pos_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst s_pre.
  rewrite <- (UIntArray.seg_shift d_pre off_shifted i (i + 1)
    (sublist (off_shifted + i) (off_shifted + i + 1) l_shifted)).
  replace (off_shifted + (i + 1)) with (off_shifted + i + 1) by lia.
  sep_apply (UIntArray.seg_merge_to_seg d_pre (off_shifted + i) (off_shifted + i + 1)
    (n_pre + off_shifted)
    (sublist (off_shifted + i) (off_shifted + i + 1) l_shifted)
    (sublist (off_shifted + i + 1) (n_pre + off_shifted) l_shifted)); try lia.
  rewrite <- (sublist_split (off_shifted + i) (n_pre + off_shifted)
    (off_shifted + i + 1) l_shifted) by lia.
  sep_apply (UIntArray.seg_merge_to_seg d_pre (i + 1) (off_shifted + i)
    (n_pre + off_shifted)
    (sublist (i + 1) (off_shifted + i) l_shifted)
    (sublist (off_shifted + i) (n_pre + off_shifted) l_shifted)); try lia.
  rewrite <- (sublist_split (i + 1) (n_pre + off_shifted)
    (off_shifted + i) l_shifted) by lia.
  cancel.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_7_off_pos : mpn_copyi_entail_wit_7_off_pos.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_copyi_entail_wit_7_off_pos_split_goal_spatial.
  - Goal_apply proof_of_mpn_copyi_entail_wit_7_off_pos_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_8_non_alias_split_goal_1 : mpn_copyi_entail_wit_8_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (sublist_split 0 (i + 1) i); try lia.
  rewrite <- sublist_single; try lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_8_non_alias : mpn_copyi_entail_wit_8_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_8_non_alias_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_return_wit_1_off_zero_split_goal_1 : mpn_copyi_return_wit_1_off_zero_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (i = n_pre) by lia.
  subst i; subst off_shifted.
  replace (0 + n_pre) with n_pre by lia.
  rewrite (Zsublist_nil l_shifted n_pre n_pre) by lia.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_return_wit_1_off_zero_split_goal_spatial : mpn_copyi_return_wit_1_off_zero_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (i = n_pre) by lia.
  subst i.
  subst off_shifted.
  replace (0 + n_pre) with n_pre by lia.
  replace (n_pre + 0) with n_pre by lia.
  rewrite (Zsublist_nil l_shifted n_pre n_pre) by lia.
  rewrite UIntArray.seg_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma proof_of_mpn_copyi_return_wit_1_off_zero : mpn_copyi_return_wit_1_off_zero.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_copyi_return_wit_1_off_zero_split_goal_spatial.
  - Goal_apply proof_of_mpn_copyi_return_wit_1_off_zero_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_return_wit_2_off_pos_split_goal_spatial : mpn_copyi_return_wit_2_off_pos_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (i = n_pre) by lia.
  subst i.
  cancel.
Qed.

Lemma proof_of_mpn_copyi_return_wit_2_off_pos : mpn_copyi_return_wit_2_off_pos.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_return_wit_2_off_pos_split_goal_spatial.
Qed.

Lemma proof_of_mpn_copyi_return_wit_3_non_alias_split_goal_spatial : mpn_copyi_return_wit_3_non_alias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Exists l l.
  assert (i = n_pre) by lia.
  subst i.
  rewrite sublist_self; try lia.
  subst n_pre.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try (split; assumption); reflexivity.
Qed.

Lemma proof_of_mpn_copyi_return_wit_3_non_alias : mpn_copyi_return_wit_3_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_return_wit_3_non_alias_split_goal_spatial.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z, mpd_store_list.
  Intros l.
  Exists l. subst n.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try reflexivity;
      destruct H; assumption.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_2_split_goal_1 : mpn_copyi_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (sublist_split i n_pre (i + 1)); try lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_2_split_goal_2 : mpn_copyi_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_sublist by lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_2 : mpn_copyi_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_which_implies_wit_2_split_goal_1.
  Goal_apply proof_of_mpn_copyi_which_implies_wit_2_split_goal_2.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_3_split_goal_spatial : mpn_copyi_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst s_pre.
  sep_apply (UIntArray.seg_split_to_seg d_pre i (i + 1) (n_pre + off_shifted)
    (sublist i (n_pre + off_shifted) l_shifted)); try lia.
  rewrite Zsublist_Zsublist by lia.
  replace (0 + i) with i by lia.
  replace (i + 1 - i + i) with (i + 1) by lia.
  sep_apply (UIntArray.seg_split_to_seg d_pre (i + 1) (off_shifted + i)
    (n_pre + off_shifted)
    (sublist (i + 1 - i) (n_pre + off_shifted - i)
      (sublist i (n_pre + off_shifted) l_shifted))); try lia.
  repeat rewrite Zsublist_Zsublist by lia.
  replace (0 + (i + 1 - i) + i) with (i + 1) by lia.
  replace (off_shifted + i - (i + 1) + (i + 1 - i) + i)
    with (off_shifted + i) by lia.
  replace (n_pre + off_shifted - (i + 1) + (i + 1 - i) + i)
    with (n_pre + off_shifted) by lia.
  sep_apply (UIntArray.seg_split_to_seg d_pre (off_shifted + i)
    (off_shifted + i + 1) (n_pre + off_shifted)
    (sublist (off_shifted + i) (n_pre + off_shifted) l_shifted)); try lia.
  repeat rewrite Zsublist_Zsublist by lia.
  replace (0 + (off_shifted + i)) with (off_shifted + i) by lia.
  replace (off_shifted + i + 1 - (off_shifted + i) + (off_shifted + i))
    with (off_shifted + i + 1) by lia.
  replace (n_pre + off_shifted - (off_shifted + i) + (off_shifted + i))
    with (n_pre + off_shifted) by lia.
  replace (off_shifted + i + 1) with (off_shifted + (i + 1)) by lia.
  rewrite (UIntArray.seg_shift d_pre off_shifted i (i + 1)
    (sublist (off_shifted + i) (off_shifted + (i + 1)) l_shifted)).
  cancel.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_3 : mpn_copyi_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_which_implies_wit_3_split_goal_spatial.
Qed.

