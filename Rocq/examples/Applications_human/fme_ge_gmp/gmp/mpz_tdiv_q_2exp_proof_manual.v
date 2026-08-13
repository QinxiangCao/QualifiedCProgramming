Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_q_2exp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_q_2exp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_copyi_entail_wit_1_off_zero_split_goal_spatial :
  mpn_copyi_entail_wit_1_off_zero_split_goal_spatial.
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

Lemma proof_of_mpn_copyi_entail_wit_1_off_zero :
  mpn_copyi_entail_wit_1_off_zero.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_1_off_zero_split_goal_spatial.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_2_off_pos_split_goal_spatial :
  mpn_copyi_entail_wit_2_off_pos_split_goal_spatial.
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

Lemma proof_of_mpn_copyi_entail_wit_2_off_pos :
  mpn_copyi_entail_wit_2_off_pos.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_2_off_pos_split_goal_spatial.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_3_off_zero_split_goal_1 :
  mpn_copyi_entail_wit_3_off_zero_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

(* This split goal no longer exists in the generated goal interface.
Lemma proof_of_mpn_copyi_entail_wit_3_off_zero_split_goal_2 :
  mpn_copyi_entail_wit_3_off_zero_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

Lemma proof_of_mpn_copyi_entail_wit_3_off_zero : mpn_copyi_entail_wit_3_off_zero.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_3_off_zero_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_4_off_pos_split_goal_1 :
  mpn_copyi_entail_wit_4_off_pos_split_goal_1.
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

Lemma proof_of_mpn_copyi_entail_wit_5_off_zero_split_goal_1 :
  mpn_copyi_entail_wit_5_off_zero_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (sublist_split 0 (i + 1) i); try lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_5_off_zero : mpn_copyi_entail_wit_5_off_zero.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_5_off_zero_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_6_off_pos_split_goal_spatial :
  mpn_copyi_entail_wit_6_off_pos_split_goal_spatial.
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

Lemma proof_of_mpn_copyi_entail_wit_6_off_pos_split_goal_1 :
  mpn_copyi_entail_wit_6_off_pos_split_goal_1.
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

Lemma proof_of_mpn_copyi_entail_wit_6_off_pos :
  mpn_copyi_entail_wit_6_off_pos.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_copyi_entail_wit_6_off_pos_split_goal_spatial.
  - Goal_apply proof_of_mpn_copyi_entail_wit_6_off_pos_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_return_wit_1_off_zero_split_goal_spatial :
  mpn_copyi_return_wit_1_off_zero_split_goal_spatial.
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

Lemma proof_of_mpn_copyi_return_wit_1_off_zero_split_goal_1 :
  mpn_copyi_return_wit_1_off_zero_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (i = n_pre) by lia.
  subst i; subst off_shifted.
  replace (0 + n_pre) with n_pre by lia.
  rewrite (Zsublist_nil l_shifted n_pre n_pre) by lia.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_return_wit_1_off_zero :
  mpn_copyi_return_wit_1_off_zero.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_copyi_return_wit_1_off_zero_split_goal_spatial.
  - Goal_apply proof_of_mpn_copyi_return_wit_1_off_zero_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_return_wit_2_off_pos_split_goal_spatial :
  mpn_copyi_return_wit_2_off_pos_split_goal_spatial.
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

Lemma proof_of_mpn_copyi_which_implies_wit_1_split_goal_1 :
  mpn_copyi_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (sublist_split i n_pre (i + 1)); try lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_1_split_goal_2 :
  mpn_copyi_which_implies_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_sublist by lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_which_implies_wit_1_split_goal_1.
  Goal_apply proof_of_mpn_copyi_which_implies_wit_1_split_goal_2.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_2_split_goal_spatial :
  mpn_copyi_which_implies_wit_2_split_goal_spatial.
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

Lemma proof_of_mpn_copyi_which_implies_wit_2 :
  mpn_copyi_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_which_implies_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_1 :
  mpn_rshift_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (off_shifted + 0 + 1) with (off_shifted + 1) by lia.
  replace (0 - 0) with 0 by lia.
  rewrite Znth_sublist by lia.
  replace (0 + off_shifted) with off_shifted by lia.
  rewrite (mpn_lshift_list_to_Z_single_sublist UINT_MOD l_up_shifted off_shifted).
  2: { rewrite PreH8; lia. }
  rewrite list_to_Z_nil.
  rewrite Z.pow_0_r.
  dump_pre_spatial.
  ring_simplify.
  apply mpn_rshift_limb_decompose.
  + apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted off_shifted);
      try exact PreH9; lia.
  + lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_2 :
  mpn_rshift_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Znth_sublist by lia.
  replace (0 - 0 + off_shifted) with off_shifted by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  dump_pre_spatial.
  reflexivity.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_3 :
  mpn_rshift_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Znth_sublist by lia.
  replace (0 - 0 + off_shifted) with off_shifted by lia.
  replace (off_shifted + 0) with off_shifted by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  dump_pre_spatial.
  symmetry.
  apply Z.quot_div_nonneg.
  + apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted off_shifted);
      try exact PreH9; lia.
  + apply Z.pow_pos_nonneg; lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_4 :
  mpn_rshift_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Znth_sublist by lia.
  replace (0 - 0 + off_shifted) with off_shifted by lia.
  replace (off_shifted + 0) with off_shifted by lia.
  dump_pre_spatial.
  reflexivity.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_5 :
  mpn_rshift_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_6 :
  mpn_rshift_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1_split_goal_spatial :
  mpn_rshift_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst up_pre.
  rewrite <- (UIntArray.seg_shift rp_pre off_shifted 0 1
    (sublist off_shifted (off_shifted + 1) l_up_shifted)).
  replace (off_shifted + 0) with off_shifted by lia.
  replace (off_shifted + (0 + 1)) with (off_shifted + 1) by lia.
  sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre off_shifted (off_shifted + 1)
    (n_pre + off_shifted)
    (sublist off_shifted (off_shifted + 1) l_up_shifted)
    (sublist (off_shifted + 1) (n_pre + off_shifted) l_up_shifted)).
  - dump_pre_spatial; lia.
  - rewrite <- (sublist_split off_shifted (n_pre + off_shifted)
      (off_shifted + 1) l_up_shifted) by lia.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 off_shifted
      (n_pre + off_shifted)
      (sublist 0 off_shifted l_up_shifted)
      (sublist off_shifted (n_pre + off_shifted) l_up_shifted)).
    + dump_pre_spatial; lia.
    + rewrite <- (sublist_split 0 (n_pre + off_shifted) off_shifted l_up_shifted) by lia.
      cancel.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_1 : mpn_rshift_entail_wit_1.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_spatial.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_1.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_2.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_3.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_4.
  + Goal_apply proof_of_mpn_rshift_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_2 : mpn_rshift_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_done_2 i_2.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_3 : mpn_rshift_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_done_2 i_2.
  subst rp up up_pre.
  sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i_2 (i_2 + 1)
    (n_pre + off_shifted)
    (sublist i_2 (n_pre + off_shifted) l_up_shifted)).
  - dump_pre_spatial; lia.
  - repeat rewrite Zsublist_Zsublist by lia.
    replace (0 + i_2) with i_2 by lia.
    replace (i_2 + 1 - i_2 + i_2) with (i_2 + 1) by lia.
    replace (n_pre + off_shifted - i_2 + i_2) with (n_pre + off_shifted) by lia.
    sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre (i_2 + 1)
      (off_shifted + i_2 + 1) (n_pre + off_shifted)
      (sublist (i_2 + 1) (n_pre + off_shifted) l_up_shifted)).
    + dump_pre_spatial; lia.
    + repeat rewrite Zsublist_Zsublist by lia.
      replace (0 + (i_2 + 1)) with (i_2 + 1) by lia.
      replace (off_shifted + i_2 + 1 - (i_2 + 1) + (i_2 + 1))
        with (off_shifted + i_2 + 1) by lia.
      replace (n_pre + off_shifted - (i_2 + 1) + (i_2 + 1))
        with (n_pre + off_shifted) by lia.
      sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre
        (off_shifted + i_2 + 1) (off_shifted + i_2 + 2)
        (n_pre + off_shifted)
        (sublist (off_shifted + i_2 + 1)
          (n_pre + off_shifted) l_up_shifted)).
      * dump_pre_spatial; lia.
      * repeat rewrite Zsublist_Zsublist by lia.
        replace (0 + (off_shifted + i_2 + 1))
          with (off_shifted + i_2 + 1) by lia.
        replace (off_shifted + i_2 + 2 - (off_shifted + i_2 + 1)
          + (off_shifted + i_2 + 1)) with (off_shifted + i_2 + 2) by lia.
        replace (n_pre + off_shifted - (off_shifted + i_2 + 1)
          + (off_shifted + i_2 + 1)) with (n_pre + off_shifted) by lia.
        rewrite <- (UIntArray.seg_shift rp_pre i_2 0 1
          (sublist i_2 (i_2 + 1) l_up_shifted)).
        replace (rp_pre + off_shifted * sizeof(UINT) +
          (i_2 + 1) * sizeof(UINT))
          with (rp_pre + (off_shifted + i_2 + 1) * sizeof(UINT)) by lia.
        rewrite <- (UIntArray.seg_shift rp_pre (off_shifted + i_2 + 1) 0 1
          (sublist (off_shifted + i_2 + 1)
            (off_shifted + i_2 + 2) l_up_shifted)).
        repeat (replace (i_2 + 0) with i_2 by lia).
        repeat (replace (off_shifted + i_2 + 1 + 0)
          with (off_shifted + i_2 + 1) by lia).
        replace (off_shifted + i_2 + 1 + 1)
          with (off_shifted + i_2 + 2) by lia.
        split_pure_spatial.
        -- cancel.
        -- repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_4 : mpn_rshift_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (high_next := Znth (0 - 0)
    (sublist (off_shifted + i + 1) (off_shifted + i + 2) l_up_shifted) 0).
  set (joined := Z.lor low_limb
    (unsigned_last_nbits (Z.shiftl high_next tnc) 32)).
  set (cur := replace_Znth 0 joined (sublist i (i + 1) l_up_shifted)).
  Exists (l_done_2 ++ cur) (i + 1).
  subst rp up up_pre.
  sep_apply_l_atomic (UIntArray.full_to_seg (rp_pre + i * sizeof(UINT)) 1 cur).
  rewrite <- (UIntArray.seg_shift rp_pre i 0 1 cur).
    replace (i + 0) with i by lia.
    replace (rp_pre + off_shifted * sizeof(UINT) + (i + 1) * sizeof(UINT))
      with (rp_pre + (off_shifted + i + 1) * sizeof(UINT)) by lia.
    rewrite <- (UIntArray.seg_shift rp_pre (off_shifted + i + 1) 0 1
      (sublist (off_shifted + i + 1) (off_shifted + i + 2) l_up_shifted)).
    replace (off_shifted + i + 1 + 0) with (off_shifted + i + 1) by lia.
    replace (off_shifted + i + 1 + 1) with (off_shifted + i + 2) by lia.
  sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1)
    l_done_2 cur).
  - dump_pre_spatial; lia.
  - sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre
        (off_shifted + i + 1) (off_shifted + i + 2)
        (n_pre + off_shifted)
        (sublist (off_shifted + i + 1) (off_shifted + i + 2) l_up_shifted)
        (sublist (off_shifted + i + 2) (n_pre + off_shifted) l_up_shifted)).
    + dump_pre_spatial; lia.
    + rewrite <- (sublist_split (off_shifted + i + 1)
          (n_pre + off_shifted) (off_shifted + i + 2) l_up_shifted) by lia.
      sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre
          (i + 1) (off_shifted + i + 1) (n_pre + off_shifted)
          (sublist (i + 1) (off_shifted + i + 1) l_up_shifted)
          (sublist (off_shifted + i + 1) (n_pre + off_shifted) l_up_shifted)).
      * dump_pre_spatial; lia.
      * rewrite <- (sublist_split (i + 1) (n_pre + off_shifted)
             (off_shifted + i + 1) l_up_shifted) by lia.
        split_pure_spatial.
        -- cancel.
        -- repeat split_pures; dump_pre_spatial; try assumption; try lia.
           ++ subst cur.
           rewrite Zlength_app.
           rewrite Zlength_replace_Znth.
           rewrite Zlength_sublist by lia.
           rewrite PreH15.
           lia.
           ++ subst cur high_next joined.
           assert (Hcur_single:
             replace_Znth 0
               (Z.lor low_limb
                 (unsigned_last_nbits
                   (Z.shiftl
                     (Znth (0 - 0)
                       (sublist (off_shifted + i + 1)
                         (off_shifted + i + 2) l_up_shifted) 0) tnc) 32))
               (sublist i (i + 1) l_up_shifted) =
             (Z.lor low_limb
                 (unsigned_last_nbits
                   (Z.shiftl
                     (Znth (off_shifted + i + 1) l_up_shifted 0) tnc) 32)) :: nil).
           {
             replace (0 - 0) with 0 by lia.
             rewrite Znth_sublist by lia.
             replace (0 + (off_shifted + i + 1)) with (off_shifted + i + 1) by lia.
             assert (Hcond: 0 <= i /\ i < i + 1 /\ i + 1 <= Zlength l_up_shifted).
             { rewrite PreH14; lia. }
             rewrite (replace_Znth_sublist_head l_up_shifted i (i + 1)
               (Z.lor low_limb
                 (unsigned_last_nbits
                   (Z.shiftl (Znth (off_shifted + i + 1) l_up_shifted 0) tnc) 32))
               Hcond).
             rewrite Zsublist_nil by lia.
             reflexivity.
           }
           rewrite Hcur_single.
           apply list_within_bound_app_single.
           ** exact PreH17.
           ** rewrite PreH19.
              replace (Znth (off_shifted + i) l_up_shifted 0 ÷ 2 ^ cnt_pre)
                with (Z.shiftr (Znth (off_shifted + i) l_up_shifted 0) cnt_pre).
              rewrite PreH11.
              apply mpn_rshift_join_limb_bound.
              --- apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted
                   (off_shifted + i)); try exact PreH16; lia.
              --- lia.
              --- rewrite Z.shiftr_div_pow2 by lia.
                  symmetry.
                  apply Z.quot_div_nonneg.
                  +++ assert (Hbd:
                       0 <= Znth (off_shifted + i) l_up_shifted 0 < UINT_MOD).
                     { apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted
                         (off_shifted + i)); try exact PreH16; lia. }
                     lia.
                  +++ apply Z.pow_pos_nonneg; lia.
           ++ subst cur high_next joined.
           replace (0 - 0) with 0 by lia.
           rewrite Znth_sublist by lia.
           replace (0 + (off_shifted + i + 1)) with (off_shifted + (i + 1)) by lia.
           reflexivity.
           ++ subst high_next.
           replace (0 - 0) with 0 by lia.
           rewrite Znth_sublist by lia.
           replace (0 + (off_shifted + i + 1)) with (off_shifted + (i + 1)) by lia.
           rewrite Z.shiftr_div_pow2 by lia.
           symmetry.
           apply Z.quot_div_nonneg.
           ** assert (Hbd:
                0 <= Znth (off_shifted + (i + 1)) l_up_shifted 0 < UINT_MOD).
              { apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted
                  (off_shifted + (i + 1))); try exact PreH16; lia. }
              lia.
           ** apply Z.pow_pos_nonneg; lia.
           ++ subst cur high_next joined.
              set (lsrc := sublist off_shifted (off_shifted + n_pre) l_up_shifted).
              assert (Hls_len: Zlength lsrc = n_pre).
              { subst lsrc. rewrite Zlength_sublist by lia. lia. }
              assert (Hls_bound: list_within_bound UINT_MOD lsrc).
              { subst lsrc. apply list_within_bound_sublist.
                - lia.
                - rewrite PreH14; lia.
                - exact PreH16. }
              assert (Hlow_src: low_limb = Znth i lsrc 0 ÷ 2 ^ cnt_pre).
              { subst lsrc.
                rewrite Znth_sublist by lia.
                replace (i + off_shifted) with (off_shifted + i) by lia.
                exact PreH19. }
              assert (Hhigh_src:
                Znth (0 - 0)
                  (sublist (off_shifted + i + 1)
                    (off_shifted + i + 2) l_up_shifted) 0 =
                Znth (i + 1) lsrc 0).
              { subst lsrc.
                replace (0 - 0) with 0 by lia.
                rewrite Znth_sublist by lia.
                rewrite Znth_sublist by lia.
                replace (0 + (off_shifted + i + 1)) with (i + 1 + off_shifted) by lia.
                reflexivity. }
              assert (Hstep_src:
                list_to_Z UINT_MOD (sublist 0 (i + 1) lsrc) =
                (list_to_Z UINT_MOD l_done_2 + low_limb * UINT_MOD ^ i) *
                  2 ^ cnt_pre + retval ÷ 2 ^ tnc).
              { subst lsrc.
                rewrite Zsublist_Zsublist by lia.
                replace (0 + off_shifted) with off_shifted by lia.
                replace (i + 1 + off_shifted) with (off_shifted + i + 1) by lia.
                exact PreH21. }
              pose proof (mpn_rshift_step_equation lsrc l_done_2 n_pre (i + 1)
                cnt_pre retval (Znth (i + 1) lsrc 0) low_limb tnc
                ltac:(lia) ltac:(lia) ltac:(rewrite Hls_len; lia)
                ltac:(rewrite PreH15; lia) ltac:(lia) Hls_bound
                ltac:(replace (i + 1 - 1) with i by lia; exact Hlow_src)
                eq_refl PreH11
                ltac:(replace (i + 1 - 1) with i by lia; exact Hstep_src)) as Hstep.
              subst lsrc.
              rewrite Zsublist_Zsublist in Hstep by lia.
              replace (0 + off_shifted) with off_shifted in Hstep by lia.
              replace (i + 1 + 1 + off_shifted) with (off_shifted + (i + 1) + 1) in Hstep by lia.
              rewrite <- Hhigh_src in Hstep.
              match goal with
              | |- context[replace_Znth ?idx ?v (sublist i (i + 1) l_up_shifted)] =>
                  set (cur_replace := replace_Znth idx v (sublist i (i + 1) l_up_shifted))
              end.
              match type of Hstep with
              | context[replace_Znth ?idx ?v ?lst] =>
                  set (src_replace := replace_Znth idx v lst) in Hstep
              end.
              assert (Hreplace_eq: cur_replace = src_replace).
              {
                subst cur_replace src_replace.
                replace (i + 1 - 1) with i by lia.
                replace (i - i) with 0 by lia.
                replace (i + 1 - (i + 1)) with 0 by lia.
                set (joined := Z.lor low_limb
                  (unsigned_last_nbits
                    (Z.shiftl
                      (Znth (0 - 0)
                        (sublist (off_shifted + i + 1)
                          (off_shifted + i + 2) l_up_shifted) 0) tnc) 32)).
                assert (Hcur_cond: 0 <= i /\ i < i + 1 /\ i + 1 <= Zlength l_up_shifted).
                { rewrite PreH14; lia. }
                pose proof (replace_Znth_sublist_head l_up_shifted i (i + 1)
                  joined Hcur_cond) as Hcur.
                assert (Hsrc_cond:
                  0 <= i /\ i < i + 1 /\
                  i + 1 <= Zlength (sublist off_shifted (off_shifted + n_pre) l_up_shifted)).
                { rewrite Zlength_sublist by lia; lia. }
                pose proof (replace_Znth_sublist_head
                  (sublist off_shifted (off_shifted + n_pre) l_up_shifted)
                  i (i + 1) joined Hsrc_cond) as Hsrc.
                rewrite Hcur, Hsrc.
                repeat rewrite Zsublist_nil by lia.
                reflexivity.
              }
              rewrite Hreplace_eq.
              exact Hstep.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_5 : mpn_rshift_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_done_2 i_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_6 : mpn_rshift_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_done_2 i_2.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre i_2 (i_2 + 1)
      (n_pre + off_shifted)
      (sublist i_2 (n_pre + off_shifted) l_up_shifted)).
    + dump_pre_spatial; lia.
    + repeat rewrite Zsublist_Zsublist by lia.
      replace (0 + i_2) with i_2 by lia.
      replace (i_2 + 1 - i_2 + i_2) with (i_2 + 1) by lia.
      replace (n_pre + off_shifted - i_2 + i_2)
        with (n_pre + off_shifted) by lia.
      replace (UIntArray.seg rp_pre i_2 (i_2 + 1)
        (sublist i_2 (i_2 + 1) l_up_shifted))
        with (UIntArray.seg rp_pre (i_2 + 0) (i_2 + 1)
          (sublist i_2 (i_2 + 1) l_up_shifted)) by (f_equal; lia).
      rewrite (UIntArray.seg_shift rp_pre i_2 0 1
        (sublist i_2 (i_2 + 1) l_up_shifted)).
      rewrite PreH2.
      cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_7 : mpn_rshift_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_last: i = n_pre - 1) by lia.
  set (lsrc := sublist off_shifted (off_shifted + n_pre) l_up_shifted).
  set (cur := replace_Znth 0 low_limb (sublist i (i + 1) l_up_shifted)).
  Exists (l_done ++ cur).
  assert (Hls_len: Zlength lsrc = n_pre).
  { subst lsrc. rewrite Zlength_sublist by lia. lia. }
  assert (Hls_bound: list_within_bound UINT_MOD lsrc).
  { subst lsrc. apply list_within_bound_sublist.
    - lia.
    - rewrite PreH14; lia.
    - exact PreH16. }
  assert (Hlow_src: low_limb = Znth i lsrc 0 ÷ 2 ^ cnt_pre).
  { subst lsrc.
    rewrite Znth_sublist by lia.
    replace (i + off_shifted) with (off_shifted + i) by lia.
    exact PreH19. }
  assert (Hcur_single: cur = low_limb :: nil).
  {
    subst cur.
    assert (Hcond: 0 <= i /\ i < i + 1 /\ i + 1 <= Zlength l_up_shifted).
    { rewrite PreH14; lia. }
    rewrite (replace_Znth_sublist_head l_up_shifted i (i + 1) low_limb Hcond).
    rewrite Zsublist_nil by lia.
    reflexivity.
  }
  assert (Hlast_single:
    replace_Znth (i - i) low_limb (sublist i (i + 1) lsrc) =
    low_limb :: nil).
  {
    replace (i - i) with 0 by lia.
    assert (Hcond: 0 <= i /\ i < i + 1 /\ i + 1 <= Zlength lsrc).
    { rewrite Hls_len; lia. }
    rewrite (replace_Znth_sublist_head lsrc i (i + 1) low_limb Hcond).
    rewrite Zsublist_nil by lia.
    reflexivity.
  }
  sep_apply_l_atomic (UIntArray.full_to_seg rp 1 cur).
  subst rp.
  rewrite <- (UIntArray.seg_shift rp_pre i 0 1 cur).
  replace (i + 0) with i by lia.
  sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre 0 i (i + 1)
    l_done cur).
  - dump_pre_spatial; lia.
  - replace (i + 1) with n_pre by lia.
    split_pure_spatial.
    + sep_apply (store_uint_undef_store_uint &( "high_limb") high_limb).
      sep_apply (store_uint_undef_store_uint &( "low_limb") low_limb).
      cancel.
    + repeat split_pures; dump_pre_spatial; try assumption; try lia.
      * rewrite Hcur_single.
        rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil, ?PreH15.
        lia.
      * rewrite Hcur_single.
        apply list_within_bound_app_single.
        -- exact PreH17.
        -- rewrite Hlow_src.
           apply mpn_rshift_quot_limb_bound.
           ++ apply (list_within_bound_Znth_bound UINT_MOD lsrc i);
                try exact Hls_bound; rewrite Hls_len; lia.
           ++ lia.
      * assert (Hinv_src:
          list_to_Z UINT_MOD (sublist 0 n_pre lsrc) =
          (list_to_Z UINT_MOD l_done + low_limb * UINT_MOD ^ i) *
            2 ^ cnt_pre + retval ÷ 2 ^ tnc).
        {
          subst lsrc.
          rewrite Zsublist_Zsublist by lia.
          replace (0 + off_shifted) with off_shifted by lia.
          replace (n_pre + off_shifted) with (off_shifted + (i + 1)) by lia.
          replace (off_shifted + (i + 1)) with (off_shifted + i + 1) by lia.
          exact PreH21.
        }
        pose proof (mpn_rshift_return_equation lsrc l_done n_pre i cnt_pre
          retval low_limb tnc Hi_last Hls_len ltac:(rewrite PreH15; lia)
          PreH10 Hls_bound ltac:(lia) Hlow_src Hinv_src) as Hret.
        rewrite Hcur_single.
        rewrite PreH10.
        rewrite Hlast_single in Hret.
        exact Hret.
Qed.

(* This split goal no longer exists in the generated goal interface.
Lemma proof_of_mpn_rshift_return_wit_1_split_goal_1 :
  mpn_rshift_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH9.
  exact PreH16.
Qed.
*)

(* This split goal no longer exists in the generated goal interface.
Lemma proof_of_mpn_rshift_return_wit_1_split_goal_2 :
  mpn_rshift_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH9.
  exact PreH15.
Qed.
*)

(* Already discharged by mpz_tdiv_q_2exp_proof_auto after solver regeneration.
Lemma proof_of_mpn_rshift_return_wit_1 : mpn_rshift_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_out_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption;
      try (rewrite <- PreH9; assumption).
Qed.
*)

Lemma proof_of_mpn_rshift_which_implies_wit_1_split_goal_spatial :
  mpn_rshift_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst up_pre.
  sep_apply_l_atomic (UIntArray.full_split_to_seg rp_pre off_shifted
    (n_pre + off_shifted) l_up_shifted).
  - dump_pre_spatial; lia.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg rp_pre off_shifted
      (off_shifted + 1) (n_pre + off_shifted)
      (sublist off_shifted (n_pre + off_shifted) l_up_shifted)).
    + dump_pre_spatial; lia.
    + rewrite Zsublist_Zsublist by lia.
      rewrite Zsublist_Zsublist by lia.
      replace (0 + off_shifted) with off_shifted by lia.
      replace (1 + off_shifted) with (off_shifted + 1) by lia.
      replace (off_shifted + 1 - off_shifted + off_shifted)
        with (off_shifted + 1) by lia.
      replace (n_pre + off_shifted - off_shifted + off_shifted)
        with (n_pre + off_shifted) by lia.
      rewrite <- (UIntArray.seg_shift rp_pre off_shifted 0 1
        (sublist off_shifted (off_shifted + 1) l_up_shifted)).
      replace (off_shifted + 0) with off_shifted by lia.
      cancel.
Qed.

Lemma proof_of_mpn_rshift_which_implies_wit_1 : mpn_rshift_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_rshift_which_implies_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_div_q_2exp_safety_wit_5_split_goal_1 :
  mpz_div_q_2exp_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  rewrite Hlimb_signed.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_safety_wit_5_split_goal_2 :
  mpz_div_q_2exp_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  rewrite Hlimb_signed.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_safety_wit_5 : mpz_div_q_2exp_safety_wit_5.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpz_div_q_2exp_safety_wit_5_split_goal_1.
  + Goal_apply proof_of_mpz_div_q_2exp_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_1 : mpz_div_q_2exp_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre.
  unfold store_Z.
  Intros ptr size cap.
  prop_apply (store_int_range (&(u_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap).
  Intros.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  Exists ptr cap size.
  split_pure_spatial.
  - normalize.
    Intros.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_2_1 : mpz_div_q_2exp_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  rewrite Hlimb_signed in *.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  destruct H as [Hdata_val [Hdata_last Hdata_bound]].
  Exists retval_2.
  Exists z_callee__mp_alloc.
  Exists size.
  Exists data.
  Exists cap_2.
  subst u_pre z_callee__mp_alloc.
  pose proof (Z.rem_bound_pos bit_index_pre 32 ltac:(lia) ltac:(lia)) as [Hrem_low Hrem_high].
  replace (retval - bit_index_pre ÷ 32 + bit_index_pre ÷ 32)
    with (Zlength data) by lia.
  rewrite H0.
  assert (Hretval_len : retval = Zlength data) by lia.
  assert (Hcap_len : Zlength data <= cap_2) by lia.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_2_2 : mpz_div_q_2exp_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  rewrite Hlimb_signed in *.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  destruct H as [Hdata_val [Hdata_last Hdata_bound]].
  Exists retval_2.
  Exists z_callee__mp_alloc.
  Exists size.
  Exists data.
  Exists cap_2.
  subst u_pre z_callee__mp_alloc.
  pose proof (Z.rem_bound_pos bit_index_pre 32 ltac:(lia) ltac:(lia)) as [Hrem_low Hrem_high].
  replace (retval - bit_index_pre ÷ 32 + bit_index_pre ÷ 32)
    with (Zlength data) by lia.
  rewrite H0.
  assert (Hretval_len : retval = Zlength data) by lia.
  assert (Hcap_len : Zlength data <= cap_2) by lia.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_3_4 : mpz_div_q_2exp_entail_wit_3_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre u__mp_alloc u__mp_d bit_index adjust mode_pre.
  assert (Hn_pos : 0 < qn) by lia.
  assert (Hbit_quot_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hshift :
    list_to_Z UINT_MOD
      (sublist limb_cnt (limb_cnt + qn) l) =
      Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD
      (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre)
      qn).
  {
    replace limb_cnt with (bit_index_pre ÷ 32) by lia.
    replace qn with (Zabs un - bit_index_pre ÷ 32) by lia.
    apply (mpz_tdiv_q_2exp_suffix_shift0
      l (Zabs z_eq_trunc) bit_index_pre (bit_index_pre ÷ 32)
      (Zabs un - bit_index_pre ÷ 32));
    try assumption; try lia.
  }
  destruct Hshift as [Hsuffix_val Hsuffix_compact].
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  unfold store_Z.
  Exists qp qn (Z.max qn cap).
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs qn) with qn by lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  sep_apply (UIntArray.seg_to_full qp 0
    qn
    (sublist limb_cnt (limb_cnt + qn) l)).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact qp
    qn
    (sublist limb_cnt (limb_cnt + qn) l)
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption;
    try (rewrite Zlength_sublist by lia; lia);
    try (apply list_within_bound_sublist; [lia | lia | assumption]).
  split_pure_spatial.
  - sep_apply (store_uint64_undef_store_uint64 &( "bit_index") 0).
    sep_apply (store_int_undef_store_int &( "qn") qn).
    sep_apply (store_int_undef_store_int &( "limb_cnt") limb_cnt).
    sep_apply (store_ptr_undef_store_ptr &( "qp") qp).
    sep_apply (store_int_undef_store_int &( "adjust") 0).
    cancel (mpd_store_Z_compact UINT_MOD qp
      (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) qn).
    cancel (UIntArray.undef_seg qp qn (Z.max qn cap)).
    cancel ((&((u_pre) # "__mpz_struct" ->ₛ "_mp_size")) # Int |-> qn).
    cancel ((&((u_pre) # "__mpz_struct" ->ₛ "_mp_alloc")) # Int
      |-> Z.max qn cap).
    cancel ((&((u_pre) # "__mpz_struct" ->ₛ "_mp_d")) # Ptr |-> qp).
    cancel ((( &( "bit_index" ) )) # UInt64 |->_).
    cancel ((( &( "qn" ) )) # Int |->_).
    cancel ((( &( "limb_cnt" ) )) # Int |->_).
    cancel ((( &( "qp" ) )) # Ptr |->_).
    cancel ((( &( "adjust" ) )) # Int |->_).
  - split_pures; dump_pre_spatial;
      try assumption;
      try (apply list_within_bound_sublist; [lia | lia | assumption]);
      try (unfold same_sign; lia);
      try lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_3_3 : mpz_div_q_2exp_entail_wit_3_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre mode_pre adjust u__mp_size u__mp_alloc u__mp_d.
  assert (Hbit_pos : 1 <= bit_index < 32) by lia.
  assert (Hshift :
    list_to_Z UINT_MOD l_out = Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) (qn - 1)).
  {
    replace limb_cnt with (bit_index_pre ÷ 32) by lia.
    replace qn with (Zabs un - bit_index_pre ÷ 32) by lia.
    apply (mpz_tdiv_q_2exp_rshift_high_zero
      l l_out (Zabs z_eq_trunc) bit_index_pre (bit_index_pre ÷ 32)
      bit_index (Zabs un - bit_index_pre ÷ 32) retval);
    try assumption; try lia.
    - replace (Zabs un - bit_index_pre ÷ 32 - 1)
        with (qn - 1 - 0) by lia.
      exact PreH2.
    - rewrite <- PreH21.
      exact PreH5.
    - rewrite <- PreH21.
      replace (Zabs un - limb_cnt) with qn by lia.
      exact PreH6.
  }
  destruct Hshift as [Hout_val Hout_compact].
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hhigh0 : Znth (qn - 1) l_out 0 = 0).
  {
    replace (qn - 1) with (qn - 1 - 0) by lia.
    exact PreH2.
  }
  unfold store_Z.
  Exists qp (qn - 1) (Z.max qn cap).
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs (qn - 1)) with (qn - 1) by lia.
  sep_apply (UIntArray.seg_to_full qp 0 qn l_out).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact qp
    qn l_out
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption; try lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    (qn - 1)
    qn
    (qn + limb_cnt)); try lia.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    (qn - 1)
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  split_pure_spatial.
  - sep_apply (store_uint64_undef_store_uint64 &( "bit_index") bit_index).
    sep_apply (store_int_undef_store_int &( "qn") (qn - 1)).
    sep_apply (store_int_undef_store_int &( "limb_cnt") limb_cnt).
    sep_apply (store_ptr_undef_store_ptr &( "qp") qp).
    sep_apply (store_int_undef_store_int &( "adjust") 0).
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_3_2 : mpz_div_q_2exp_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre mode_pre adjust u__mp_size u__mp_alloc u__mp_d.
  assert (Hbit_pos : 1 <= bit_index < 32) by lia.
  assert (Hshift :
    list_to_Z UINT_MOD l_out = Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) qn).
  {
    replace (Zlength l_out) with qn by lia.
    apply (mpz_tdiv_q_2exp_rshift_nonzero
      l l_out (Zabs z_eq_trunc) bit_index_pre limb_cnt
      bit_index qn retval);
    try assumption; try lia.
    - replace (qn - 1)
        with (qn - 1 - 0) by lia.
      exact PreH2.
  }
  destruct Hshift as [Hout_val Hout_compact].
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  unfold store_Z.
  Exists qp qn (Z.max qn cap).
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs qn) with qn by lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  sep_apply (UIntArray.seg_to_full qp 0 qn l_out).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact qp
    qn l_out
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption; try lia.
  split_pure_spatial.
  - sep_apply (store_uint64_undef_store_uint64 &( "bit_index") bit_index).
    sep_apply (store_int_undef_store_int &( "qn") qn).
    sep_apply (store_int_undef_store_int &( "limb_cnt") limb_cnt).
    sep_apply (store_ptr_undef_store_ptr &( "qp") qp).
    sep_apply (store_int_undef_store_int &( "adjust") 0).
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_3_1 : mpz_div_q_2exp_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre.
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  assert (Hsize_le_limb : Zabs size <= bit_index_pre ÷ 32).
  { rewrite Hlimb_signed in PreH2; lia. }
  prop_apply (mpd_store_Z_compact_bound ptr (Zabs z_eq_trunc) (Zabs size)).
  Intros.
  assert (Hquot_zero :
    Z.quot (Zabs z_eq_trunc) (2 ^ bit_index_pre) = 0).
  {
    apply (mpz_tdiv_q_2exp_zero_by_limb_bound
      (Zabs z_eq_trunc) size bit_index_pre);
    [lia | exact Hsize_le_limb | assumption].
  }
  rewrite Hquot_zero.
  sep_apply_l_atomic (store_Z_zero_from_fields u_pre ptr size cap z_eq_trunc).
  - dump_pre_spatial; lia.
  - dump_pre_spatial; assumption.
  - sep_apply (store_uint64_undef_store_uint64 &( "bit_index") (bit_index_pre % 32)).
    sep_apply (store_int_undef_store_int &( "qn") 0).
    sep_apply (store_int_undef_store_int &( "limb_cnt") (signed_last_nbits (bit_index_pre ÷ 32) 32)).
    sep_apply (store_int_undef_store_int &( "adjust") 0).
    split_pure_spatial.
    + cancel.
    + repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_1 : mpz_div_q_2exp_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre size.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs z_eq_trunc)).
  Intros.
  assert (Hzero : z_eq_trunc = 0) by lia.
  subst z_eq_trunc.
  change (0 ÷ 2 ^ bit_index_pre) with 0.
  unfold store_Z.
  Exists ptr 0 cap.
  replace (Zabs 0) with 0 by lia.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_2_split_goal_spatial :
  mpz_div_q_2exp_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hz_neg : z_eq_trunc < 0).
  { unfold same_sign in PreH4; lia. }
  assert (Hden_pos : 0 < 2 ^ bit_index_pre).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hz_abs : z_eq_trunc = - Zabs z_eq_trunc).
  {
    rewrite Z.abs_neq by lia.
    lia.
  }
  rewrite Hz_abs.
  replace (Zabs (- Zabs z_eq_trunc)) with (Zabs z_eq_trunc) by
    (rewrite Z.abs_neq; lia).
  rewrite Z.quot_opp_l by lia.
  cancel.
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_2 : mpz_div_q_2exp_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_div_q_2exp_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_3 : mpz_div_q_2exp_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre.
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  assert (Hsize_le_limb : Zabs size <= bit_index_pre ÷ 32).
  { rewrite Hlimb_signed in PreH2; lia. }
  prop_apply (mpd_store_Z_compact_bound ptr (Zabs z_eq_trunc) (Zabs size)).
  Intros.
  assert (Hquot_zero :
    Z.quot (Zabs z_eq_trunc) (2 ^ bit_index_pre) = 0).
  {
    apply (mpz_tdiv_q_2exp_zero_by_limb_bound
      (Zabs z_eq_trunc) size bit_index_pre);
    [lia | exact Hsize_le_limb | assumption].
  }
  assert (Hz_nonneg : 0 <= z_eq_trunc).
  { unfold same_sign in PreH14; lia. }
  replace (Z.quot z_eq_trunc (2 ^ bit_index_pre)) with 0.
  2: {
    rewrite <- (Z.abs_eq z_eq_trunc) by lia.
    symmetry; exact Hquot_zero.
  }
  sep_apply_l_atomic (store_Z_zero_from_fields u_pre ptr size cap z_eq_trunc).
  - dump_pre_spatial; lia.
  - dump_pre_spatial; assumption.
  - split_pure_spatial.
    + cancel.
    + repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_4 : mpz_div_q_2exp_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre mode_pre adjust u__mp_size u__mp_alloc u__mp_d.
  assert (Hbit_pos : 1 <= bit_index < 32) by lia.
  assert (Hshift :
    list_to_Z UINT_MOD l_out = Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) qn).
  {
    replace (Zlength l_out) with qn by lia.
    apply (mpz_tdiv_q_2exp_rshift_nonzero
      l l_out (Zabs z_eq_trunc) bit_index_pre limb_cnt
      bit_index qn retval);
    try assumption; try lia.
    - replace (qn - 1)
        with (qn - 1 - 0) by lia.
      exact PreH2.
  }
  destruct Hshift as [Hout_val Hout_compact].
  assert (Hz_nonneg : 0 <= z_eq_trunc).
  { unfold same_sign in PreH19; lia. }
  assert (Hquot_eq :
    Z.quot z_eq_trunc (2 ^ bit_index_pre) =
    Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    rewrite (Z.abs_eq z_eq_trunc) by lia.
    reflexivity.
  }
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  unfold store_Z.
  Exists qp qn (Z.max qn cap).
  rewrite Hquot_eq.
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs qn) with qn by lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  sep_apply (UIntArray.seg_to_full qp 0 qn l_out).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact qp
    qn l_out
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption; try lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_5 : mpz_div_q_2exp_return_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre mode_pre adjust u__mp_size u__mp_alloc u__mp_d.
  assert (Hbit_pos : 1 <= bit_index < 32) by lia.
  assert (Hshift :
    list_to_Z UINT_MOD l_out = Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) (qn - 1)).
  {
    replace limb_cnt with (bit_index_pre ÷ 32) by lia.
    replace qn with (Zabs un - bit_index_pre ÷ 32) by lia.
    apply (mpz_tdiv_q_2exp_rshift_high_zero
      l l_out (Zabs z_eq_trunc) bit_index_pre (bit_index_pre ÷ 32)
      bit_index (Zabs un - bit_index_pre ÷ 32) retval);
    try assumption; try lia.
    - replace (Zabs un - bit_index_pre ÷ 32 - 1)
        with (qn - 1 - 0) by lia.
      exact PreH2.
    - rewrite <- PreH21.
      exact PreH5.
    - rewrite <- PreH21.
      replace (Zabs un - limb_cnt) with qn by lia.
      exact PreH6.
  }
  destruct Hshift as [Hout_val Hout_compact].
  assert (Hz_nonneg : 0 <= z_eq_trunc).
  { unfold same_sign in PreH19; lia. }
  assert (Hquot_eq :
    Z.quot z_eq_trunc (2 ^ bit_index_pre) =
    Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    rewrite (Z.abs_eq z_eq_trunc) by lia.
    reflexivity.
  }
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hhigh0 : Znth (qn - 1) l_out 0 = 0).
  {
    replace (qn - 1) with (qn - 1 - 0) by lia.
    exact PreH2.
  }
  unfold store_Z.
  Exists qp (qn - 1) (Z.max qn cap).
  rewrite Hquot_eq.
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs (qn - 1)) with (qn - 1) by lia.
  sep_apply (UIntArray.seg_to_full qp 0 qn l_out).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact qp
    qn l_out
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption; try lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    (qn - 1)
    qn
    (qn + limb_cnt)); try lia.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    (qn - 1)
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_6 : mpz_div_q_2exp_return_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre mode_pre bit_index adjust u__mp_size u__mp_alloc u__mp_d.
  assert (Hn_pos : 0 < qn) by lia.
  assert (Hbit_quot_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hshift :
    list_to_Z UINT_MOD
      (sublist limb_cnt (limb_cnt + qn) l) =
      Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD
      (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre)
      qn).
  {
    replace limb_cnt with (bit_index_pre ÷ 32) by lia.
    replace qn with (Zabs un - bit_index_pre ÷ 32) by lia.
    apply (mpz_tdiv_q_2exp_suffix_shift0
      l (Zabs z_eq_trunc) bit_index_pre (bit_index_pre ÷ 32)
      (Zabs un - bit_index_pre ÷ 32));
    try assumption; try lia.
  }
  destruct Hshift as [Hsuffix_val Hsuffix_compact].
  assert (Hz_nonneg : 0 <= z_eq_trunc).
  { unfold same_sign in PreH14; lia. }
  assert (Hquot_eq :
    Z.quot z_eq_trunc (2 ^ bit_index_pre) =
    Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    rewrite (Z.abs_eq z_eq_trunc) by lia.
    reflexivity.
  }
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  unfold store_Z.
  Exists qp qn (Z.max qn cap).
  rewrite Hquot_eq.
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs qn) with qn by lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  sep_apply (UIntArray.seg_to_full qp 0
    qn
    (sublist limb_cnt (limb_cnt + qn) l)).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact qp
    qn
    (sublist limb_cnt (limb_cnt + qn) l)
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption;
    try (rewrite Zlength_sublist by lia; lia);
    try (apply list_within_bound_sublist; [lia | lia | assumption]).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; left; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_2_pure : mpz_div_q_2exp_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_1 :
  mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_2 :
  mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_3 :
  mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_4 :
  mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure :
  mpz_div_q_2exp_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_1.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_2.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_3.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_4.
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_1 :
  mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_2 :
  mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure :
  mpz_div_q_2exp_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_1.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_2.
Qed.
