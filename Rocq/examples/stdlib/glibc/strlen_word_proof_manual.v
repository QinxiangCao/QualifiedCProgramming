From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.stdlib.glibc Require Import strlen_word_goal.
From SimpleC.EE.stdlib.glibc Require Import strlen_word_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.stdlib.glibc.strlen_word_lib.
Import StrlenLittleEndian strlen_word_lib.
Local Open Scope sac.

Lemma proof_of_sl_load_word_entail_wit_1 : sl_load_word_entail_wit_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold sl_addr in *.
prop_apply_p (UCharArray.full_Zlength s capacity bytes). Intros_p Hlen.
sep_apply (UCharArray.full_split_to_seg s (p_pre-s+8) capacity bytes ltac:(lia)).
sep_apply (UCharArray.seg_split_to_seg s 0 (p_pre-s) (p_pre-s+8) (sublist 0 (p_pre-s+8) bytes) ltac:(lia)).
rewrite !Z.sub_0_r.
rewrite Zsublist_Zsublist00 by lia.
rewrite Zsublist_Zsublist0 by lia.
assert (Ha : (s+(p_pre-s)) mod 8 = 0) by
 (replace (s+(p_pre-s)) with p_pre by lia; rewrite <- Z.rem_mod_nonneg by lia; exact PreH5).
sep_apply (extract_eight__object_load s (p_pre-s) (sublist (p_pre-s) (p_pre-s+8) bytes) Ha).
Intros word. Exists word.
replace (s+(p_pre-s)) with p_pre by lia.
split_pure_spatial; [cancel |].
cancel (p_pre # UInt64 |-> word). cancel.
split_pures; dump_pre_spatial; try lia.
unfold sl_word_matches. intros j Hj.
replace (p_pre-s+j) with (j+(p_pre-s)) by lia.
rewrite <- (Znth_sublist 0 (p_pre-s) j (p_pre-s+8) bytes) by lia.
apply H0; exact Hj.
Qed.

Lemma proof_of_sl_load_word_return_wit_1_split_goal_spatial : sl_load_word_return_wit_1_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold sl_addr in *.
assert (Hlen : Zlength (sublist (p_pre-s) (p_pre-s+8) bytes) = 8) by (rewrite Zlength_sublist by lia; lia).
assert (Hm : forall j, 0 <= j < 8 -> (word/256^j) mod 256 = Znth j (sublist (p_pre-s) (p_pre-s+8) bytes) 0).
{ intros j Hj.
rewrite Znth_sublist by lia.
replace (j+(p_pre-s)) with (p_pre-s+j) by lia.
apply PreH11; exact Hj.
} pose proof (restore_eight__object_load s (p_pre-s) word (sublist (p_pre-s) (p_pre-s+8) bytes) Hlen Hm) as Hr.
replace (s+(p_pre-s)) with p_pre in Hr by lia.
sep_apply Hr.
sep_apply (UCharArray.seg_merge_to_seg s 0 (p_pre-s) (p_pre-s+8) (sublist 0 (p_pre-s) bytes) (sublist (p_pre-s) (p_pre-s+8) bytes) ltac:(lia)).
rewrite <- sublist_split by lia.
sep_apply (UCharArray.seg_merge_to_full s 0 (p_pre-s+8) capacity (sublist 0 (p_pre-s+8) bytes) (sublist (p_pre-s+8) capacity bytes) ltac:(lia)).
rewrite Z.mul_0_l, Z.add_0_r, Z.sub_0_r.
rewrite <- sublist_split by lia.
rewrite <- PreH3, sublist_self.
cancel.
reflexivity.
Qed.
Lemma proof_of_sl_load_word_return_wit_1 : sl_load_word_return_wit_1.
Proof.
aggressive_pre_process.
Goal_apply proof_of_sl_load_word_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_sl_first_zero_entail_wit_1_split_goal_1 : sl_first_zero_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite sl_suffix_zero. reflexivity.
Qed.

Lemma proof_of_sl_first_zero_entail_wit_1 : sl_first_zero_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sl_first_zero_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_sl_first_zero_entail_wit_2_split_goal_1 : sl_first_zero_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Z.quot_div_nonneg by lia. subst v. apply sl_suffix_step. lia.
Qed.

Lemma proof_of_sl_first_zero_entail_wit_2_split_goal_2 : sl_first_zero_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.le_trans with v; [apply Z.div_le_upper_bound; nia | assumption].
Qed.

Lemma proof_of_sl_first_zero_entail_wit_2_split_goal_3 : sl_first_zero_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Z.quot_div_nonneg by lia. apply Z.div_pos; lia.
Qed.

Lemma proof_of_sl_first_zero_entail_wit_2 : sl_first_zero_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sl_first_zero_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_sl_first_zero_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_sl_first_zero_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_sl_first_zero_entail_wit_3_split_goal_1 : sl_first_zero_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_sl_first_zero_entail_wit_3 : sl_first_zero_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sl_first_zero_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_sl_first_zero_entail_wit_4_split_goal_1 : sl_first_zero_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Z.quot_div_nonneg by lia. subst v. apply sl_suffix_step. lia.
Qed.

Lemma proof_of_sl_first_zero_entail_wit_4_split_goal_2 : sl_first_zero_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.le_trans with v; [apply Z.div_le_upper_bound; nia | assumption].
Qed.

Lemma proof_of_sl_first_zero_entail_wit_4_split_goal_3 : sl_first_zero_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite Z.quot_div_nonneg by lia. apply Z.div_pos; lia.
Qed.

Lemma proof_of_sl_first_zero_entail_wit_4 : sl_first_zero_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sl_first_zero_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_sl_first_zero_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_sl_first_zero_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_sl_first_zero_return_wit_1_split_goal_1 : sl_first_zero_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold sl_found. repeat split; try lia. intros j Hj. apply PreH11. lia.
Qed.

Lemma proof_of_sl_first_zero_return_wit_1 : sl_first_zero_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sl_first_zero_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_sl_first_zero_return_wit_2_split_goal_1 : sl_first_zero_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold sl_found. repeat split; try lia.
  - exact PreH12.
  - intros. unfold sl_byte. rewrite <- PreH11. rewrite Z.rem_mod_nonneg in PreH1 by lia. exact PreH1.
Qed.

Lemma proof_of_sl_first_zero_return_wit_2 : sl_first_zero_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sl_first_zero_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_strlen_word_entail_wit_1 : strlen_word_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite ?sizeof_uchar in *.
  pose proof (Zlength_nonneg m_capacity_spec) as Hn.
  pose proof (rounded_capacity__outer_loop _ _ Hn PreH4) as Hcap.
  assert (Hu : unsigned_last_nbits s_pre 64 = s_pre).
  { apply unsigned_last_nbits_eq. change (0 <= s_pre < 18446744073709551616). lia. }
  rewrite Hu, PreH2, Z.sub_0_r, Hu.
  unfold ObjectString.store_string. Intros tail.
  Exists tail. split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_strlen_word_entail_wit_2 : strlen_word_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite ?sizeof_uchar in *.
  pose proof (Zlength_nonneg m_capacity_spec) as Hn.
  pose proof (rounded_capacity__outer_loop _ _ Hn PreH11) as Hcap.
  assert (Hstep : p + 8 <= s_pre + Zlength m_capacity_spec).
  { pose proof (no_zero_word_step__outer_loop m_capacity_spec tail_2 retval
      (p-s_pre) retval_2 ltac:(rewrite ?sizeof_uchar in *; lia) PreH3
      ltac:(rewrite <- PreH7; exact PreH2) PreH1). lia. }
  rewrite unsigned_last_nbits_eq by (change (0 <= p+8 < 18446744073709551616); lia).
  Exists tail_2. split_pure_spatial; [cancel |].
  split_pures; dump_pre_spatial; auto; try (rewrite ?sizeof_uchar in *; lia).
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Z.rem_mod_nonneg in PreH14 by lia.
  rewrite Z.add_mod by lia. rewrite PreH14. reflexivity.
Qed.

Lemma proof_of_strlen_word_return_wit_1_split_goal_1 : strlen_word_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst start. unfold sl_addr in *.
  assert (Heq : p - s_pre + retval = Zlength m_capacity_spec).
  { apply (first_zero_is_string_end__result_specs m_capacity_spec tail (p-s_pre) retval_2 retval).
    - exact PreH15.
    - change (p <= s_pre + Zlength m_capacity_spec * 1) in PreH13. lia.
    - exact PreH3.
    - exact PreH2.
    - exact PreH1. }
  prop_apply_p (UCharArray.full_Zlength s_pre capacity_capacity_spec (m_capacity_spec ++ 0 :: tail)).
  Intros_p Hlen.
  dump_pre_spatial.
  rewrite Zlength_app, Zlength_cons in Hlen.
  pose proof (Zlength_nonneg tail). pose proof (Zlength_nonneg m_capacity_spec).
  change (s_pre + capacity_capacity_spec * 1 <= 18446744073709551615) in PreH10.
  rewrite (unsigned_last_nbits_eq (p + retval) 64) by (change (0 <= p + retval < 18446744073709551616); lia).
  rewrite unsigned_last_nbits_eq by (change (0 <= p + retval - s_pre < 18446744073709551616); lia).
  lia.
Qed.

Lemma proof_of_strlen_word_return_wit_1_split_goal_spatial : strlen_word_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ObjectString.store_string. Exists tail.
  split_pure_spatial; [cancel | dump_pre_spatial; assumption].
Qed.

Lemma proof_of_strlen_word_return_wit_1 : strlen_word_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strlen_word_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_strlen_word_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_strlen_word_partial_solve_wit_1_pure_split_goal_1 : strlen_word_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_strlen_word_partial_solve_wit_1_pure_split_goal_2 : strlen_word_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial. unfold sl_addr.
  rewrite Z.rem_mod_nonneg in PreH10, PreH15 by lia.
  apply (aligned_last_word_bound__outer_loop s_pre p (Zlength m_capacity_spec) capacity_capacity_spec); auto using Zlength_nonneg.
  rewrite ?sizeof_uchar in *; lia.
Qed.

Lemma proof_of_strlen_word_partial_solve_wit_1_pure_split_goal_3 : strlen_word_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_strlen_word_partial_solve_wit_1_pure : strlen_word_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strlen_word_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_strlen_word_partial_solve_wit_1_pure_split_goal_2.
  - Goal_apply proof_of_strlen_word_partial_solve_wit_1_pure_split_goal_3.
Qed.

Lemma proof_of_strlen_word_capacity_spec_entail_exact_spec : strlen_word_capacity_spec_entail_exact_spec.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ObjectString.store_string_exact.
  Exists (Zlength m_exact_spec + 1) m_exact_spec.
  split_pure_spatial.
  - cancel. Intros_r retval. apply derivable1_wand_sepcon_adjoint.
    Intros_p Hr. split_pure_spatial; [cancel | dump_pre_spatial; assumption].
  - split_pures; dump_pre_spatial; assumption.
Qed.

