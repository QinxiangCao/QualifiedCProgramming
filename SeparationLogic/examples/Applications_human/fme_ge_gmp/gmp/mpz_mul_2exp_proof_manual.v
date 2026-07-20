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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_mul_2exp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_mul_2exp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_copyd_entail_wit_2_off_pos : mpn_copyd_entail_wit_2_off_pos.
Proof.
  pre_process.
  Exists n_pre.
  split_pure_spatial.
  - entailer!.
    rewrite Z.add_comm.
    rewrite Zsublist_nil by lia.
    rewrite UIntArray.seg_empty.
    entailer!.
  - split_pures; dump_pre_spatial; try lia; auto.
Qed. 

Lemma proof_of_mpn_copyd_entail_wit_5_off_pos : mpn_copyd_entail_wit_5_off_pos.
Proof.
  pre_process.
  replace k_2 with (n + 1) by lia.
  replace (off_shifted + n + 1) with (off_shifted + (n + 1)) by lia.
  entailer!.
Qed. 

Lemma proof_of_mpn_copyd_entail_wit_6_off_zero : mpn_copyd_entail_wit_6_off_zero.
Proof.
  pre_process.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_merge_to_seg s_pre 0 n_2 (n_2 + 1)
      (sublist 0 n_2 l_shifted) (sublist n_2 (n_2 + 1) l_shifted)).
    + dump_pre_spatial; lia.
    +
    replace (sublist 0 n_2 l_shifted ++ sublist n_2 (n_2 + 1) l_shifted)
      with (sublist 0 (n_2 + 1) l_shifted).
    2: { rewrite <- (sublist_split 0 (n_2 + 1) n_2 l_shifted) by lia; reflexivity. }
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg s_pre 0 (n_2 + 1) n_pre
      (sublist 0 (n_2 + 1) l_shifted) (sublist (n_2 + 1) n_pre l_shifted)).
    * dump_pre_spatial; lia.
    *
    replace (sublist 0 (n_2 + 1) l_shifted ++ sublist (n_2 + 1) n_pre l_shifted)
      with (sublist 0 n_pre l_shifted).
    2: { rewrite <- (sublist_split 0 n_pre (n_2 + 1) l_shifted) by lia; reflexivity. }
    rewrite PreH1.
    entailer!.
  - split_pures; dump_pre_spatial; try lia; auto.
Qed. 

Lemma proof_of_mpn_copyd_entail_wit_7_off_pos : mpn_copyd_entail_wit_7_off_pos.
Proof.
  aggressive_pre_process.
  Exists n_2.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_to_undef_seg s_pre n_2 (n_2 + 1)
      (sublist n_2 (n_2 + 1) l_shifted)).
    sep_apply_l_atomic (UIntArray.undef_seg_merge_to_undef_seg s_pre n_2 (n_2 + 1) (off_shifted + n_2)).
    + dump_pre_spatial; lia.
    + sep_apply_l_atomic (UIntArray.seg_single d_pre n_2
        (Znth (n_2 - n_2) (sublist n_2 (n_2 + 1) l_shifted) 0)).
      replace (Znth (n_2 - n_2) (sublist n_2 (n_2 + 1) l_shifted) 0 :: nil)
        with (sublist n_2 (n_2 + 1) l_shifted).
      2: {
        rewrite Z.sub_diag.
        rewrite Znth_sublist by lia.
        replace (0 + n_2) with n_2 by lia.
        apply sublist_single; lia.
      }
      sep_apply_l_atomic (UIntArray.seg_merge_to_seg d_pre n_2 (n_2 + 1) n_pre
        (sublist n_2 (n_2 + 1) l_shifted) (sublist (n_2 + 1) n_pre l_shifted)).
      * dump_pre_spatial; lia.
      * replace (sublist n_2 (n_2 + 1) l_shifted ++ sublist (n_2 + 1) n_pre l_shifted)
          with (sublist n_2 n_pre l_shifted).
        2: { rewrite <- (sublist_split n_2 n_pre (n_2 + 1) l_shifted) by lia; reflexivity. }
        entailer!.
  - split_pures; dump_pre_spatial; try lia; auto.
Qed. 

Lemma proof_of_mpn_copyd_return_wit_1_off_zero : mpn_copyd_return_wit_1_off_zero.
Proof.
  pre_process.
  rewrite PreH12.
  rewrite UIntArray.undef_seg_empty.
  entailer!.
  rewrite PreH2.
  entailer!.
Qed. 

Lemma proof_of_mpn_copyd_return_wit_2_off_pos : mpn_copyd_return_wit_2_off_pos.
Proof.
  pre_process.
  replace k_2 with 0 by lia.
  replace (off_shifted + 0) with off_shifted by lia.
  entailer!.
  rewrite Zsublist_nil by lia.
  rewrite UIntArray.seg_empty.
  entailer!.
Qed. 

Lemma proof_of_mpn_copyd_which_implies_wit_1 : mpn_copyd_which_implies_wit_1.
Proof.
  pre_process.
  prop_apply (UIntArray.full_Zlength s n l_shifted).
  Intros.
  sep_apply_l_atomic (UIntArray.full_to_seg s n l_shifted).
  replace (sublist 0 n l_shifted) with l_shifted.
  2: { symmetry; apply sublist_self; lia. }
  entailer!.
Qed. 

Lemma proof_of_mpn_copyd_which_implies_wit_2 : mpn_copyd_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  sep_apply_l_atomic (UIntArray.seg_split_to_seg s_pre 0 n n_pre
    (sublist 0 n_pre l_shifted)).
  - dump_pre_spatial; lia.
  - rewrite Zsublist_Zsublist by lia.
    rewrite Zsublist_Zsublist by lia.
    replace (0 + 0) with 0 by lia.
    replace (n - 0 + 0) with n by lia.
    replace (n_pre - 0 + 0) with n_pre by lia.
    sep_apply_l_atomic (UIntArray.seg_split_to_seg s_pre n (n + 1) n_pre
      (sublist n n_pre l_shifted)).
    + dump_pre_spatial; lia.
    + rewrite Zsublist_Zsublist by lia.
      rewrite Zsublist_Zsublist by lia.
      replace (0 + n) with n by lia.
      replace (n + 1 - n + n) with (n + 1) by lia.
      replace (n_pre - n + n) with n_pre by lia.
      entailer!.
Qed. 

Lemma proof_of_mpn_copyd_which_implies_wit_3 : mpn_copyd_which_implies_wit_3.
Proof.
  unfold mpn_copyd_which_implies_wit_3.
  right.
  intros.
  subst d_pre.
  split_pure_spatial.
  sep_apply_l_atomic (UIntArray.undef_seg_split_to_undef_seg s_pre (n + 1)
    (off_shifted + n) ((off_shifted + n) + 1)).
  - dump_pre_spatial; lia.
  - replace (off_shifted + n + 1) with (off_shifted + (n + 1)) by lia.
    rewrite (UIntArray.undef_seg_shift s_pre off_shifted n (n + 1)).
    entailer!.
  - split_pures; dump_pre_spatial; try lia; auto.
    + rewrite <- (sublist_split 0 (n + 1) n l_shifted) by lia.
      reflexivity.
    + rewrite Zlength_sublist by lia.
      lia.
Qed. 

Lemma proof_of_mpn_zero_entail_wit_1 : mpn_zero_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  replace (n_pre - 1 + 1) with n_pre by lia.
  rewrite UIntArray.seg_empty.
  entailer!.
  rewrite Zlength_nil.
  lia.
Qed. 

Lemma proof_of_mpn_zero_entail_wit_2 : mpn_zero_entail_wit_2.
Proof.
  pre_process.
  Exists (0 :: l_done_2).
  replace (n - 1 + 1) with n by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_single rp_pre n 0).
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg rp_pre n (n + 1) n_pre
      (0 :: nil) l_done_2).
    + dump_pre_spatial; lia.
    + simpl.
      entailer!.
  - split_pures; dump_pre_spatial; simpl; try lia; auto.
    + rewrite Zlength_cons.
      lia.
    + split.
      * unfold UINT_MOD; lia.
      * assumption.
    + rewrite list_to_Z_cons.
      lia.
Qed. 

Lemma proof_of_mpn_zero_return_wit_1 : mpn_zero_return_wit_1.
Proof.
  pre_process.
  Exists l_done.
  replace (n + 1) with 0 by lia.
  rewrite UIntArray.undef_seg_empty.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_to_full rp_pre 0 n_pre l_done).
    replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    entailer!.
  - split_pures; dump_pre_spatial; try lia; auto.
Qed. 

Lemma proof_of_mpn_lshift_entail_wit_1_off_zero : mpn_lshift_entail_wit_1_off_zero.
Proof.
  pre_process.
  Exists (@nil Z).
  split_pure_spatial.
  - subst rp_pre.
    replace ((n_pre - 1) + 1) with n_pre by lia.
    rewrite UIntArray.seg_empty.
    entailer!.
  - split_pures; dump_pre_spatial.
    + assumption.
    + lia.
    + lia.
    + assumption.
    + assumption.
    + reflexivity.
    + lia.
    + lia.
    + assumption.
    + reflexivity.
    + rewrite Zlength_nil; lia.
    + assumption.
    + rewrite Znth_sublist by lia.
      replace (n_pre - 1 - 0 + 0) with (n_pre - 1) by lia.
      reflexivity.
    + rewrite Znth_sublist by lia.
      replace (n_pre - 1 - 0 + 0) with (n_pre - 1) by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite <- Z.quot_div_nonneg.
      2: {
        pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted (n_pre - 1)
          ltac:(rewrite PreH7; lia) PreH8) as Hlast_bound.
        lia.
      }
      2: { apply Z.pow_pos_nonneg; lia. }
      reflexivity.
    + rewrite Znth_sublist by lia.
      replace (n_pre - 1 - 0 + 0) with (n_pre - 1) by lia.
      rewrite Z.shiftl_mul_pow2 by lia.
      reflexivity.
    + rewrite Znth_sublist by lia.
      replace (n_pre - 1 - 0 + 0) with (n_pre - 1) by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite <- Z.quot_div_nonneg.
      2: {
        pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted (n_pre - 1)
          ltac:(rewrite PreH7; lia) PreH8) as Hlast_bound.
        lia.
      }
      2: { apply Z.pow_pos_nonneg; lia. }
      rewrite Z.shiftl_mul_pow2 by lia.
      apply mpn_lshift_initial_equation; try lia; auto.
Qed. 

Lemma proof_of_mpn_lshift_entail_wit_2_off_pos : mpn_lshift_entail_wit_2_off_pos.
Proof.
  pre_process.
  Exists (@nil Z).
  split_pure_spatial.
  - replace ((n_pre - 1) + 1) with n_pre by lia.
    replace ((off_shifted + (n_pre - 1)) + 1) with (n_pre + off_shifted) by lia.
    rewrite UIntArray.seg_empty.
    entailer!.
  - split_pures; dump_pre_spatial.
    + assumption.
    + assumption.
    + assumption.
    + reflexivity.
    + lia.
    + lia.
    + reflexivity.
    + lia.
    + lia.
    + assumption.
    + reflexivity.
    + rewrite Zlength_nil; lia.
    + assumption.
    + rewrite Znth_sublist by lia.
      replace (n_pre - 1 - 0 + 0) with (n_pre - 1) by lia.
      reflexivity.
    + rewrite Znth_sublist by lia.
      replace (n_pre - 1 - 0 + 0) with (n_pre - 1) by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite <- Z.quot_div_nonneg.
      2: {
        pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted (n_pre - 1)
          ltac:(rewrite PreH7; lia) PreH8) as Hlast_bound.
        lia.
      }
      2: { apply Z.pow_pos_nonneg; lia. }
      reflexivity.
    + rewrite Znth_sublist by lia.
      replace (n_pre - 1 - 0 + 0) with (n_pre - 1) by lia.
      rewrite Z.shiftl_mul_pow2 by lia.
      reflexivity.
    + rewrite Znth_sublist by lia.
      replace (n_pre - 1 - 0 + 0) with (n_pre - 1) by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite <- Z.quot_div_nonneg.
      2: {
        pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted (n_pre - 1)
          ltac:(rewrite PreH7; lia) PreH8) as Hlast_bound.
        lia.
      }
      2: { apply Z.pow_pos_nonneg; lia. }
      rewrite Z.shiftl_mul_pow2 by lia.
      apply mpn_lshift_initial_equation; try lia; auto.
Qed. 

Lemma proof_of_mpn_lshift_entail_wit_5_off_zero_inv : mpn_lshift_entail_wit_5_off_zero_inv.
Proof.
  pre_process.
  Exists l_done_3.
  split_pure_spatial.
  - replace ((i - 1) + 2) with (i + 1) by lia.
    entailer!.
  - split_pures; dump_pre_spatial; try solve [lia | assumption | reflexivity].
    + rewrite Znth_sublist by lia.
      replace (i - 1 - 0 + 0) with (i - 1) by lia.
      pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted (i - 1)
        ltac:(rewrite PreH9; lia) PreH11) as Hlimb.
      lia.
    + rewrite Znth_sublist by lia.
      replace (i - 1 - 0 + 0) with (i - 1) by lia.
      pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted (i - 1)
        ltac:(rewrite PreH9; lia) PreH11) as Hlimb.
      unfold UINT_MOD in *.
      lia.
    + rewrite Znth_sublist by lia.
      replace (i - 1 - 0 + 0) with (i - 1) by lia.
      reflexivity.
    + replace (i - 1 + 1) with i by lia.
      assumption.
    + replace (i - 1 + 1) with i by lia.
      assumption.
Qed. 

Lemma proof_of_mpn_lshift_entail_wit_6_off_pos_inv : mpn_lshift_entail_wit_6_off_pos_inv.
Proof.
  pre_process.
  Exists l_done_3.
  split_pure_spatial.
  - replace ((i - 1) + 2) with (i + 1) by lia.
    replace ((off_shifted + (i - 1)) + 2) with ((off_shifted + i) + 1) by lia.
    entailer!.
  - split_pures; dump_pre_spatial; try solve [lia | assumption | reflexivity].
    + rewrite Znth_sublist by lia.
      replace (i - 1 - 0 + 0) with (i - 1) by lia.
      pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted (i - 1)
        ltac:(rewrite PreH10; lia) PreH12) as Hlimb.
      lia.
    + rewrite Znth_sublist by lia.
      replace (i - 1 - 0 + 0) with (i - 1) by lia.
      pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted (i - 1)
        ltac:(rewrite PreH10; lia) PreH12) as Hlimb.
      unfold UINT_MOD in *.
      lia.
    + rewrite Znth_sublist by lia.
      replace (i - 1 - 0 + 0) with (i - 1) by lia.
      reflexivity.
    + replace (i - 1 + 1) with i by lia.
      assumption.
    + replace (i - 1 + 1) with i by lia.
      assumption.
Qed. 

Lemma proof_of_mpn_lshift_entail_wit_7_off_zero_inv : mpn_lshift_entail_wit_7_off_zero_inv.
Proof.
  aggressive_pre_process.
  Exists (replace_Znth ((i_2 + 1) - (i_2 + 1))
            (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))
            (sublist (i_2 + 1) (i_2 + 2) l_up_shifted) ++ l_done_3).
  split_pure_spatial.
  - rewrite PreH2.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg up_pre (i_2 + 1) (i_2 + 2) n_pre
      (replace_Znth ((i_2 + 1) - (i_2 + 1))
         (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))
         (sublist (i_2 + 1) (i_2 + 2) l_up_shifted)) l_done_3).
    + entailer!.
    + cancel (UIntArray.seg up_pre (i_2 + 1) n_pre
        (replace_Znth (i_2 + 1 - (i_2 + 1))
           (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))
           (sublist (i_2 + 1) (i_2 + 2) l_up_shifted) ++ l_done_3)).
  - entailer!.
    + apply mpn_lshift_initial_equation; try assumption.
      * nia.
      * split; assumption.
    + rewrite Zlength_nil. nia.
    + apply (mpn_lshift_step_equation l_up_shifted l_done_3 n_pre i_2
               cnt_pre retval_2 high_limb_2 low_limb_2 tnc_2);
        try assumption.
      * rewrite PreH11. nia.
      * split; assumption.
    + rewrite PreH8.
      rewrite Z.shiftl_mul_pow2 by nia.
      reflexivity.
    + apply (mpn_lshift_done_bound l_up_shifted l_done_3 n_pre i_2 cnt_pre
               high_limb_2 low_limb_2 tnc_2);
        try assumption.
      * rewrite PreH11. nia.
      * split; assumption.
      * split; assumption.
    + apply (mpn_lshift_done_length l_up_shifted l_done_3 n_pre i_2
               (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)));
        try assumption.
      rewrite PreH11. nia.
Qed. 

Lemma proof_of_mpn_lshift_entail_wit_8_off_pos_inv : mpn_lshift_entail_wit_8_off_pos_inv.
Proof.
  aggressive_pre_process.
  Exists ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) :: l_done_3).
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg up_pre 0 (i_2 + 1) (i_2 + 2)
      (sublist 0 (i_2 + 2) l_up_shifted)).
    + dump_pre_spatial; lia.
    + sep_apply_l_atomic (UIntArray.seg_to_undef_seg up_pre (i_2 + 1) (i_2 + 2)
        (sublist (i_2 + 1 - 0) (i_2 + 2 - 0) (sublist 0 (i_2 + 2) l_up_shifted))).
      sep_apply_l_atomic (UIntArray.undef_seg_merge_to_undef_seg up_pre
        (i_2 + 1) (i_2 + 2) (off_shifted + i_2 + 1)).
      * dump_pre_spatial; lia.
      * sep_apply_l_atomic (UIntArray.seg_single rp_pre (i_2 + 1)
          (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))).
        replace (i_2 + 1 + 1) with (i_2 + 2) by lia.
        sep_apply (UIntArray.seg_merge_to_seg rp_pre (i_2 + 1)
          (i_2 + 2) n_pre
          ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) :: nil)
          l_done_3).
        -- simpl.
           rewrite Zsublist_Zsublist by lia.
           replace (0 + 0) with 0 by lia.
           replace (i_2 + 1 - 0 + 0) with (i_2 + 1) by lia.
           entailer!.
        -- lia.
  - entailer!.
    + apply mpn_lshift_initial_equation; try assumption.
      * nia.
      * split; assumption.
    + rewrite Zlength_nil. nia.
    + apply (mpn_lshift_step_equation_cons l_up_shifted l_done_3 n_pre i_2
               cnt_pre retval_2 high_limb_2 low_limb_2 tnc_2);
        try assumption.
      * rewrite PreH15. nia.
      * split; assumption.
    + rewrite PreH12.
      rewrite Z.shiftl_mul_pow2 by nia.
      reflexivity.
    + simpl.
      split.
      * unfold UINT_MOD in *. nia.
      * exact PreH18.
    + rewrite Zlength_cons.
      rewrite PreH16.
      unfold Z.succ.
      ring.
Qed. 

Lemma proof_of_mpn_lshift_entail_wit_9_off_zero_inv : mpn_lshift_entail_wit_9_off_zero_inv.
Proof.
  unfold mpn_lshift_entail_wit_9_off_zero_inv.
  right.
  intros.
  Exists l_done_3.
  assert (Hi0: i = 0) by nia.
  subst i.
  replace (0 + 1) with 1 by lia.
  rewrite (sublist_self l_up_shifted n_pre) in PreH16 by (symmetry; exact PreH9).
  replace (n_pre - 0) with n_pre in PreH16 by ring.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted 0
    ltac:(rewrite PreH9; lia) PreH11) as Hlimb.
  entailer!.
  - rewrite PreH13.
    unfold UINT_MOD in Hlimb.
    lia.
Qed. 

Lemma proof_of_mpn_lshift_entail_wit_10_off_pos_inv : mpn_lshift_entail_wit_10_off_pos_inv.
Proof.
  unfold mpn_lshift_entail_wit_10_off_pos_inv.
  right.
  intros.
  Exists l_done_3.
  assert (Hi0: i = 0) by nia.
  subst i.
  replace (0 + 1) with 1 by lia.
  replace (off_shifted + 0 + 1) with (off_shifted + 1) by lia.
  rewrite (sublist_self l_up_shifted n_pre) in PreH17 by (symmetry; exact PreH10).
  replace (n_pre - 0) with n_pre in PreH17 by ring.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted 0
    ltac:(rewrite PreH10; lia) PreH12) as Hlimb.
  entailer!.
  - rewrite PreH14.
    unfold UINT_MOD in Hlimb.
    lia.
Qed. 

Lemma proof_of_mpn_lshift_return_wit_1_off_zero_inv : mpn_lshift_return_wit_1_off_zero_inv.
Proof.
  pre_process.
  subst rp_pre.
  subst off_shifted.
  set (prefix := replace_Znth 0 high_limb (sublist 0 1 l_up_shifted)).
  Exists (prefix ++ l_done).
  rewrite UIntArray.undef_seg_empty.
  sep_apply UIntArray.full_to_seg.
  sep_apply (UIntArray.seg_merge_to_full up_pre 0 1 n_pre prefix l_done).
  sep_apply (UIntArray_full_list_within_bound_preserve
               (up_pre + 0 * sizeof(UINT)) (n_pre - 0) (prefix ++ l_done)).
  Intros.
  sep_apply UIntArray.full_to_seg.
  simpl.
  entailer!.
  - replace (up_pre + 0) with up_pre by nia.
    replace (n_pre - 0) with n_pre by nia.
    entailer!.
  - subst prefix.
    assert (Hrep:
      replace_Znth 0 high_limb (sublist 0 1 l_up_shifted) =
      high_limb :: nil).
    {
      rewrite (replace_Znth_sublist_head l_up_shifted 0 1 high_limb).
      - rewrite Zsublist_nil by nia.
        reflexivity.
      - pose proof (Zlength_nonneg l_done).
        rewrite PreH9.
        nia.
    }
    rewrite Hrep.
    simpl.
    rewrite list_to_Z_cons.
    replace (UINT_MOD * list_to_Z UINT_MOD l_done)
      with (list_to_Z UINT_MOD l_done * UINT_MOD) by ring.
    exact PreH14.
  - subst prefix.
    rewrite Zlength_app.
    rewrite Zlength_replace_Znth.
    rewrite Zlength_sublist by (pose proof (Zlength_nonneg l_done); rewrite PreH9; nia).
    nia.
  - pose proof (Zlength_nonneg l_done).
    nia.
Qed. 

Lemma proof_of_mpn_lshift_return_wit_2_off_pos_inv : mpn_lshift_return_wit_2_off_pos_inv.
Proof.
  pre_process.
  sep_apply (store_uint_range_preserve (rp_pre + 0 * sizeof(UINT)) high_limb).
  Intros.
  Exists (high_limb :: l_done).
  sep_apply (UIntArray.seg_to_undef_seg up_pre 0 1 (sublist 0 1 l_up_shifted)).
  sep_apply_l_atomic (UIntArray.undef_seg_merge_to_undef_seg up_pre 0 1 off_shifted).
  - dump_pre_spatial; lia.
  - sep_apply UIntArray.seg_single.
    replace (0 + 1) with 1 by nia.
    sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 1 n_pre
                 (high_limb :: nil) l_done).
    simpl.
    entailer!.
    + rewrite list_to_Z_cons.
      replace (UINT_MOD * list_to_Z UINT_MOD l_done)
        with (list_to_Z UINT_MOD l_done * UINT_MOD) by ring.
      exact PreH16.
    + unfold UINT_MOD.
      replace Int.max_unsigned with 4294967295 in H by reflexivity.
      unfold UINT_MOD in *.
      nia.
    + rewrite Zlength_cons.
      nia.
    + pose proof (Zlength_nonneg l_done).
      nia.
Qed. 

Lemma proof_of_mpn_lshift_which_implies_wit_1 : mpn_lshift_which_implies_wit_1.
Proof.
  unfold mpn_lshift_which_implies_wit_1.
  left.
  intros.
  sep_apply UIntArray.full_to_seg.
  prop_apply (UIntArray.seg_Zlength up 0 n l_up_shifted).
  Intros.
  replace (n - 0) with n in H by lia.
  rewrite (sublist_self l_up_shifted n) by (symmetry; exact H).
  entailer!.
Qed. 

Lemma proof_of_mpn_lshift_which_implies_wit_2 : mpn_lshift_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply_l_atomic (UIntArray.seg_split_to_seg up_pre 0 (i + 1) (i + 2)
    (sublist 0 (i + 2) l_up_shifted)).
  - dump_pre_spatial; lia.
  - rewrite Zsublist_Zsublist by lia.
    rewrite Zsublist_Zsublist by lia.
    replace (0 + 0) with 0 by lia.
    replace (i + 1 - 0 + 0) with (i + 1) by lia.
    replace (i + 2 - 0 + 0) with (i + 2) by lia.
    entailer!.
Qed. 

Lemma proof_of_mpn_lshift_which_implies_wit_3 : mpn_lshift_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  subst rp_pre.
  sep_apply_l_atomic (UIntArray.undef_seg_split_to_undef_seg up_pre (i + 2)
    (off_shifted + i + 1) ((off_shifted + i) + 2)).
  - dump_pre_spatial; lia.
  - replace (off_shifted + i + 1) with (off_shifted + (i + 1)) by lia.
    replace (off_shifted + i + 2) with (off_shifted + (i + 2)) by lia.
    rewrite (UIntArray.undef_seg_shift up_pre off_shifted (i + 1) (i + 2)).
    entailer!.
Qed. 

Lemma proof_of_mpn_lshift_which_implies_wit_5 : mpn_lshift_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  subst rp_pre.
  sep_apply_l_atomic (UIntArray.undef_seg_split_to_undef_seg up_pre 1 off_shifted (off_shifted + 1)).
  - dump_pre_spatial; lia.
  - replace off_shifted with (off_shifted + 0) at 2 by lia.
    rewrite (UIntArray.undef_seg_shift up_pre off_shifted 0 1).
    entailer!.
Qed. 

Lemma proof_of_mpz_mul_2exp_safety_wit_7 : mpz_mul_2exp_safety_wit_7.
Proof.
  pre_process.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z_eq) (Zabs size)).
  Intros Hcompact.
  assert (Hz_nonzero : z_eq <> 0).
  {
    intro Hz.
    subst z_eq.
    rewrite Z.abs_0 in H.
    pose proof (is_compact_Z_size_pos_value_pos 0 (Zabs size) H ltac:(lia)).
    lia.
  }
  unfold mpz_mul_2exp_fits in PreH6.
  pose proof (PreH6 (Zabs size) Hz_nonzero H) as Hfits.
  assert (Hquot : bits_pre ÷ 32 = bits_pre / 32).
  { apply Z.quot_div_nonneg; lia. }
  assert (Hbits_div_nonneg : 0 <= bits_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  destruct (Z.eq_dec (bits_pre % 32) 0) as [Hrem0 | Hremnz].
  {
    rewrite Hrem0 in PreH1.
    change (unsigned_last_nbits 0 32) with 0 in PreH1.
    lia.
  }
  assert (Hbits_div_range : - 2 ^ (32 - 1) <= bits_pre ÷ 32 < 2 ^ (32 - 1)).
  {
    change (2 ^ (32 - 1)) with 2147483648.
    pose proof (Z.abs_nonneg size).
    destruct (Z.eq_dec (bits_pre % 32) 0); [congruence | lia].
  }
  rewrite (signed_last_nbits_eq (bits_pre ÷ 32) 32 ltac:(lia) Hbits_div_range).
  entailer!.
Qed. 

Lemma proof_of_mpz_mul_2exp_safety_wit_8 : mpz_mul_2exp_safety_wit_8.
Proof.
  pre_process.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z_eq) (Zabs size)).
  Intros Hcompact.
  assert (Hz_nonzero : z_eq <> 0).
  {
    intro Hz.
    subst z_eq.
    rewrite Z.abs_0 in H.
    pose proof (is_compact_Z_size_pos_value_pos 0 (Zabs size) H ltac:(lia)).
    lia.
  }
  unfold mpz_mul_2exp_fits in PreH6.
  pose proof (PreH6 (Zabs size) Hz_nonzero H) as Hfits.
  assert (Hquot : bits_pre ÷ 32 = bits_pre / 32).
  { apply Z.quot_div_nonneg; lia. }
  assert (Hbits_div_nonneg : 0 <= bits_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hrem_range : 0 <= bits_pre % 32 < 32).
  { apply Z.rem_bound_pos; lia. }
  assert (Hunsigned : unsigned_last_nbits (bits_pre % 32) 32 = bits_pre % 32).
  { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296. lia. }
  destruct (Z.eq_dec (bits_pre % 32) 0) as [Hrem0 | Hremnz].
  2: { rewrite Hunsigned in PreH1; lia. }
  assert (Hbits_div_range : - 2 ^ (32 - 1) <= bits_pre ÷ 32 < 2 ^ (32 - 1)).
  {
    change (2 ^ (32 - 1)) with 2147483648.
    pose proof (Z.abs_nonneg size).
    destruct (Z.eq_dec (bits_pre % 32) 0); [lia | congruence].
  }
  rewrite (signed_last_nbits_eq (bits_pre ÷ 32) 32 ltac:(lia) Hbits_div_range).
  entailer!.
Qed. 

Lemma proof_of_mpz_mul_2exp_safety_wit_9 : mpz_mul_2exp_safety_wit_9.
Proof.
  pre_process.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z_eq) (Zabs size)).
  Intros Hcompact.
  assert (Hz_nonzero : z_eq <> 0).
  {
    intro Hz.
    subst z_eq.
    rewrite Z.abs_0 in H.
    pose proof (is_compact_Z_size_pos_value_pos 0 (Zabs size) H ltac:(lia)).
    lia.
  }
  unfold mpz_mul_2exp_fits in PreH5.
  pose proof (PreH5 (Zabs size) Hz_nonzero H) as Hfits.
  assert (Hquot : bits_pre ÷ 32 = bits_pre / 32).
  { apply Z.quot_div_nonneg; lia. }
  assert (Hbits_div_nonneg : 0 <= bits_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hbits_div_range : - 2 ^ (32 - 1) <= bits_pre ÷ 32 < 2 ^ (32 - 1)).
  {
    change (2 ^ (32 - 1)) with 2147483648.
    pose proof (Z.abs_nonneg size).
    destruct (Z.eq_dec (bits_pre % 32) 0); lia.
  }
  destruct (Z.eq_dec (bits_pre % 32) 0) as [Hrem0 | Hremnz];
    rewrite (signed_last_nbits_eq (bits_pre ÷ 32) 32 ltac:(lia) Hbits_div_range);
    entailer!.
Qed. 

Lemma proof_of_mpz_mul_2exp_entail_wit_1 : mpz_mul_2exp_entail_wit_1.
Proof.
  pre_process.
  unfold store_Z.
  Intros ptr size cap.
  subst r_pre.
  Exists ptr cap size.
  entailer!.
Qed. 

Lemma proof_of_mpz_mul_2exp_entail_wit_2 : mpz_mul_2exp_entail_wit_2.
Proof.
  pre_process.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros l.
  destruct H as [Hlval [Hlast Hwithin]].
  assert (Hcompact : is_compact_Z UINT_MOD (Zabs z_eq) (Zabs size_2)).
  { exists l; repeat split; auto. }
  assert (Hz_nonzero : z_eq <> 0).
  {
    intro Hz.
    subst z_eq.
    rewrite Z.abs_0 in Hcompact.
    pose proof (is_compact_Z_size_pos_value_pos 0 (Zabs size_2) Hcompact ltac:(lia)).
    lia.
  }
  unfold mpz_mul_2exp_fits in PreH9.
  pose proof (PreH9 (Zabs size_2) Hz_nonzero Hcompact) as Hfits.
  assert (Hquot : bits_pre ÷ 32 = bits_pre / 32).
  { apply Z.quot_div_nonneg; lia. }
  assert (Hbits_div_nonneg : 0 <= bits_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hrem_range : 0 <= bits_pre % 32 < 32).
  { apply Z.rem_bound_pos; lia. }
  assert (Hunsigned : unsigned_last_nbits (bits_pre % 32) 32 = bits_pre % 32).
  { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296. lia. }
  destruct (Z.eq_dec (bits_pre % 32) 0) as [Hrem0 | Hremnz].
  {
    rewrite Hrem0 in PreH1.
    change (unsigned_last_nbits 0 32) with 0 in PreH1.
    lia.
  }
  assert (Hbits_div_range : - 2 ^ (32 - 1) <= bits_pre ÷ 32 < 2 ^ (32 - 1)).
  {
    change (2 ^ (32 - 1)) with 2147483648.
    pose proof (Z.abs_nonneg size_2).
    destruct (Z.eq_dec (bits_pre % 32) 0); [congruence | lia].
  }
  assert (Hsigned : signed_last_nbits (bits_pre ÷ 32) 32 = bits_pre ÷ 32).
  { apply signed_last_nbits_eq; [lia | exact Hbits_div_range]. }
  assert (Hretval_abs : retval = Zabs size_2) by lia.
  assert (Hlen_ret : Zlength l = retval) by lia.
  assert (Hretval_pos : retval > 0) by lia.
  assert (Hcap : Zabs size_2 <= cap_2) by lia.
  rewrite Hsigned in *.
  rewrite Hunsigned in *.
  replace (Zabs size_2) with retval by lia.
  replace (Zlength l) with retval by lia.
  sep_apply_l_atomic (UIntArray.undef_seg_split_to_undef_seg retval_2 retval
    (retval + (bits_pre ÷ 32))
    (Z.max (retval + (bits_pre ÷ 32) + 1) cap_2)).
  - dump_pre_spatial; lia.
  -
  assert (Hfits_pred : mpz_mul_2exp_fits z_eq bits_pre).
  {
    unfold mpz_mul_2exp_fits.
    intros size Hnz Hcomp.
    destruct (Z.eq_dec (bits_pre % 32) 0); [congruence | auto].
  }
  subst r_pre.
  subst z_callee__mp_alloc.
  Exists retval_2 (Z.max (retval + (bits_pre ÷ 32) + 1) cap_2) l cap_2 size_2.
  entailer!; try lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_entail_wit_3 : mpz_mul_2exp_entail_wit_3.
Proof.
  pre_process.
  subst u__mp_d_2.
  subst u__mp_alloc_2.
  sep_apply_l_atomic (UIntArray.undef_seg_split_to_undef_seg rp (un + limbs) rn
    (Z.max rn cap_2)).
  - dump_pre_spatial; lia.
  -
  Exists rp (Z.max rn cap_2) l_out_2 l cap_2 size_2.
  entailer!; try lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_entail_wit_4 : mpz_mul_2exp_entail_wit_4.
Proof.
  pre_process.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros l.
  destruct H as [Hlval [Hlast Hwithin]].
  assert (Hcompact : is_compact_Z UINT_MOD (Zabs z_eq) (Zabs size_2)).
  { exists l; repeat split; auto. }
  assert (Hz_nonzero : z_eq <> 0).
  {
    intro Hz.
    subst z_eq.
    rewrite Z.abs_0 in Hcompact.
    pose proof (is_compact_Z_size_pos_value_pos 0 (Zabs size_2) Hcompact ltac:(lia)).
    lia.
  }
  unfold mpz_mul_2exp_fits in PreH9.
  pose proof (PreH9 (Zabs size_2) Hz_nonzero Hcompact) as Hfits.
  assert (Hquot : bits_pre ÷ 32 = bits_pre / 32).
  { apply Z.quot_div_nonneg; lia. }
  assert (Hbits_div_nonneg : 0 <= bits_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hrem_range : 0 <= bits_pre % 32 < 32).
  { apply Z.rem_bound_pos; lia. }
  assert (Hunsigned : unsigned_last_nbits (bits_pre % 32) 32 = bits_pre % 32).
  { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296. lia. }
  assert (Hshift_zero : unsigned_last_nbits (bits_pre % 32) 32 = 0) by lia.
  assert (Hrem0 : bits_pre % 32 = 0) by (rewrite Hunsigned in Hshift_zero; lia).
  assert (Hbits_div_range : - 2 ^ (32 - 1) <= bits_pre ÷ 32 < 2 ^ (32 - 1)).
  {
    change (2 ^ (32 - 1)) with 2147483648.
    pose proof (Z.abs_nonneg size_2).
    destruct (Z.eq_dec (bits_pre % 32) 0); [lia | congruence].
  }
  assert (Hsigned : signed_last_nbits (bits_pre ÷ 32) 32 = bits_pre ÷ 32).
  { apply signed_last_nbits_eq; [lia | exact Hbits_div_range]. }
  assert (Hretval_abs : retval = Zabs size_2) by lia.
  assert (Hlen_ret : Zlength l = retval) by lia.
  assert (Hretval_pos : retval > 0) by lia.
  assert (Hcap : Zabs size_2 <= cap_2) by lia.
  rewrite Hsigned in *.
  rewrite Hunsigned in *.
  replace (Zabs size_2) with retval by lia.
  replace (Zlength l) with retval by lia.
  sep_apply_l_atomic (UIntArray.undef_seg_split_to_undef_seg retval_2 retval
    (retval + (bits_pre ÷ 32))
    (Z.max (retval + (bits_pre ÷ 32) + 0) cap_2)).
  - dump_pre_spatial; lia.
  -
  assert (Hfits_pred : mpz_mul_2exp_fits z_eq bits_pre).
  {
    unfold mpz_mul_2exp_fits.
    intros size Hnz Hcomp.
    destruct (Z.eq_dec (bits_pre % 32) 0); [auto | congruence].
  }
  assert (Hrn_bound : retval + bits_pre ÷ 32 <= INT_MAX).
  {
    change INT_MAX with 2147483647.
    destruct (Z.eq_dec (bits_pre % 32) 0); [lia | congruence].
  }
  subst r_pre.
  subst z_callee__mp_alloc.
  Exists retval_2 (Z.max (retval + (bits_pre ÷ 32) + 0) cap_2) l cap_2 size_2.
  entailer!; try lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_entail_wit_5 : mpz_mul_2exp_entail_wit_5.
Proof.
  pre_process.
  subst u__mp_d_2.
  subst u__mp_alloc_2.
  Exists rp (Z.max rn cap_2) l_2 cap_2 size_2.
  rewrite (sublist_self l_2 un) by lia.
  entailer!; try lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_return_wit_1 : mpz_mul_2exp_return_wit_1.
Proof.
  pre_process.
  subst retval.
  assert (Hsize0: size = 0) by lia.
  subst size.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs z_eq)).
  Intros.
  assert (Hz0: z_eq = 0) by lia.
  subst z_eq.
  rewrite Z.mul_0_l.
  subst r_pre.
  change (Zabs 0) with 0.
  sep_apply (store_Z_from_zero_fields u_pre ptr cap); [ | entailer!].
  entailer!.
Qed. 

Lemma proof_of_mpz_mul_2exp_return_wit_2 : mpz_mul_2exp_return_wit_2.
Proof.
  pre_process.
  subst r_pre.
  subst u__mp_alloc.
  subst u__mp_d.
  assert (Hz_neg : z_eq < 0) by (unfold same_sign in PreH9; lia).
  assert (Hbits_eq : bits_pre = 32 * limbs + shift).
  { rewrite (Z.quot_rem' bits_pre 32) at 1. lia. }
  assert (Hpow_eq : 2 ^ bits_pre = UINT_MOD ^ limbs * 2 ^ shift).
  {
    unfold UINT_MOD.
    rewrite Hbits_eq.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_mul_r by lia.
    reflexivity.
  }
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_in PreH23) as Hin_bound.
  rewrite PreH22 in Hin_bound.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH27) as Hout_bound.
  rewrite PreH26 in Hout_bound.
  assert (Hshift_bound : 0 <= 2 ^ shift < UINT_MOD).
  {
    split.
    - apply Z.pow_nonneg; lia.
    - unfold UINT_MOD.
      change 4294967296 with (2 ^ 32).
      apply Z.pow_lt_mono_r; lia.
  }
  assert (HA_bound :
    0 <= Zabs z_eq * 2 ^ shift < UINT_MOD ^ (un + 1)).
  {
    replace (UINT_MOD ^ (un + 1)) with (UINT_MOD ^ un * UINT_MOD).
    - nia.
    - rewrite Z.pow_add_r by (unfold UINT_MOD; lia).
      ring.
  }
  assert (Hpow_un_pos : 0 < UINT_MOD ^ un).
  { apply Z.pow_pos_nonneg; unfold UINT_MOD; lia. }
  assert (Hcy_bound : 0 <= cy_val < UINT_MOD).
  { nia. }
  assert (Hlen_join : Zlength (l ++ l_out ++ cy_val :: nil) = rn).
  {
    repeat rewrite Zlength_app.
    rewrite PreH2, PreH26.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  }
  assert (Hbound_join : list_within_bound UINT_MOD (l ++ l_out ++ cy_val :: nil)).
  {
    rewrite app_assoc.
    apply list_within_bound_app_single.
    apply list_within_bound_concat; assumption.
    exact Hcy_bound.
  }
  assert (Hval_join :
    list_to_Z UINT_MOD (l ++ l_out ++ cy_val :: nil) =
    Zabs (z_eq * 2 ^ bits_pre)).
  {
    rewrite !list_to_Z_app by exact UINT_MOD_pos.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite PreH2, PreH4, PreH26.
    replace (cy_val + UINT_MOD * 0) with cy_val by ring.
    replace (0 + (list_to_Z UINT_MOD l_out + cy_val * UINT_MOD ^ un) *
             UINT_MOD ^ limbs)
      with ((list_to_Z UINT_MOD l_out + cy_val * UINT_MOD ^ un) *
             UINT_MOD ^ limbs) by ring.
    rewrite PreH28.
    rewrite Hpow_eq.
    rewrite Z.abs_mul.
    replace (Zabs (2 ^ bits_pre)) with (2 ^ bits_pre)
      by (rewrite Z.abs_eq; [reflexivity | apply Z.pow_nonneg; lia]).
    rewrite Z.abs_neq by lia.
    nia.
  }
  assert (Hlast_join : last (l ++ l_out ++ cy_val :: nil) 1 >= 1).
  {
    rewrite app_assoc.
    rewrite last_last.
    nia.
  }
  assert (Hcompact_join :
    is_compact_Z UINT_MOD (Zabs (z_eq * 2 ^ bits_pre)) rn).
  {
    eapply is_compact_Z_from_full_last with
      (data := l ++ l_out ++ cy_val :: nil);
      try exact Hlen_join; try exact Hbound_join; try exact Hval_join;
      try exact Hlast_join; lia.
  }
  unfold store_Z.
  Exists rp (- rn) (Z.max rn cap).
  replace (Zabs (- rn)) with rn by lia.
  sep_apply UIntArray.full_to_seg.
  rewrite <- (UIntArray.seg_shift rp limbs 0 un l_out).
  replace (limbs + 0) with limbs by lia.
  replace (limbs + un) with (rn - 1) by lia.
  sep_apply (UIntArray.seg_merge_to_seg rp 0 limbs (rn - 1) l l_out); try lia.
  sep_apply_l_atomic (UIntArray.seg_single rp (rn - 1) cy_val).
  replace (rn - 1 + 1) with rn by lia.
  sep_apply_l_atomic (UIntArray.seg_to_full rp (rn - 1) rn (cy_val :: nil)).
  replace (UIntArray.full (rp + (rn - 1) * sizeof(UINT)) 1 (cy_val :: nil))
    with (UIntArray.full (rp + (rn - 1) * sizeof(UINT)) (rn - (rn - 1)) (cy_val :: nil))
    by (f_equal; lia).
  sep_apply_l_atomic (UIntArray.seg_to_full rp 0 (rn - 1) (l ++ l_out)).
  replace (rp + 0 * sizeof(UINT)) with rp by lia.
  replace (rn - 1 - 0) with (rn - 1) by lia.
  sep_apply (UIntArray.full_merge_to_full rp (rn - 1) rn
    (l ++ l_out) (cy_val :: nil)); try lia.
  replace ((l ++ l_out) ++ cy_val :: nil)
    with (l ++ l_out ++ cy_val :: nil) by (rewrite app_assoc; reflexivity).
  sep_apply (UIntArray_full_to_mpd_store_Z_compact rp rn
    (l ++ l_out ++ cy_val :: nil)
    (Zabs (z_eq * 2 ^ bits_pre))); try assumption.
  replace (-(rn - 0)) with (- rn) by lia.
  entailer!; try lia.
  assert (Hpow_bits_pos : 0 < 2 ^ bits_pre).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hprod_neg : z_eq * 2 ^ bits_pre < 0).
  { apply Z.mul_neg_pos; lia. }
  unfold same_sign; lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_return_wit_3 : mpz_mul_2exp_return_wit_3.
Proof.
  pre_process.
  subst r_pre.
  subst u__mp_alloc.
  subst u__mp_d.
  assert (Hz_nonneg : 0 <= z_eq) by (unfold same_sign in PreH9; lia).
  assert (Hbits_eq : bits_pre = 32 * limbs + shift).
  { rewrite (Z.quot_rem' bits_pre 32) at 1. lia. }
  assert (Hpow_eq : 2 ^ bits_pre = UINT_MOD ^ limbs * 2 ^ shift).
  {
    unfold UINT_MOD.
    rewrite Hbits_eq.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_mul_r by lia.
    reflexivity.
  }
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_in PreH23) as Hin_bound.
  rewrite PreH22 in Hin_bound.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH27) as Hout_bound.
  rewrite PreH26 in Hout_bound.
  assert (Hshift_bound : 0 <= 2 ^ shift < UINT_MOD).
  {
    split.
    - apply Z.pow_nonneg; lia.
    - unfold UINT_MOD.
      change 4294967296 with (2 ^ 32).
      apply Z.pow_lt_mono_r; lia.
  }
  assert (HA_bound :
    0 <= Zabs z_eq * 2 ^ shift < UINT_MOD ^ (un + 1)).
  {
    replace (UINT_MOD ^ (un + 1)) with (UINT_MOD ^ un * UINT_MOD).
    - nia.
    - rewrite Z.pow_add_r by (unfold UINT_MOD; lia).
      ring.
  }
  assert (Hpow_un_pos : 0 < UINT_MOD ^ un).
  { apply Z.pow_pos_nonneg; unfold UINT_MOD; lia. }
  assert (Hcy_bound : 0 <= cy_val < UINT_MOD).
  { nia. }
  assert (Hlen_join : Zlength (l ++ l_out ++ cy_val :: nil) = rn).
  {
    repeat rewrite Zlength_app.
    rewrite PreH2, PreH26.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  }
  assert (Hbound_join : list_within_bound UINT_MOD (l ++ l_out ++ cy_val :: nil)).
  {
    rewrite app_assoc.
    apply list_within_bound_app_single.
    apply list_within_bound_concat; assumption.
    exact Hcy_bound.
  }
  assert (Hval_join :
    list_to_Z UINT_MOD (l ++ l_out ++ cy_val :: nil) =
    Zabs (z_eq * 2 ^ bits_pre)).
  {
    rewrite !list_to_Z_app by exact UINT_MOD_pos.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite PreH2, PreH4, PreH26.
    replace (cy_val + UINT_MOD * 0) with cy_val by ring.
    replace (0 + (list_to_Z UINT_MOD l_out + cy_val * UINT_MOD ^ un) *
             UINT_MOD ^ limbs)
      with ((list_to_Z UINT_MOD l_out + cy_val * UINT_MOD ^ un) *
             UINT_MOD ^ limbs) by ring.
    rewrite PreH28.
    rewrite Hpow_eq.
    rewrite Z.abs_mul.
    replace (Zabs (2 ^ bits_pre)) with (2 ^ bits_pre)
      by (rewrite Z.abs_eq; [reflexivity | apply Z.pow_nonneg; lia]).
    nia.
  }
  assert (Hlast_join : last (l ++ l_out ++ cy_val :: nil) 1 >= 1).
  {
    rewrite app_assoc.
    rewrite last_last.
    nia.
  }
  assert (Hcompact_join :
    is_compact_Z UINT_MOD (Zabs (z_eq * 2 ^ bits_pre)) rn).
  {
    eapply is_compact_Z_from_full_last with
      (data := l ++ l_out ++ cy_val :: nil);
      try exact Hlen_join; try exact Hbound_join; try exact Hval_join;
      try exact Hlast_join; lia.
  }
  unfold store_Z.
  Exists rp rn (Z.max rn cap).
  replace (Zabs rn) with rn by lia.
  sep_apply UIntArray.full_to_seg.
  rewrite <- (UIntArray.seg_shift rp limbs 0 un l_out).
  replace (limbs + 0) with limbs by lia.
  replace (limbs + un) with (rn - 1) by lia.
  sep_apply (UIntArray.seg_merge_to_seg rp 0 limbs (rn - 1) l l_out); try lia.
  sep_apply_l_atomic (UIntArray.seg_single rp (rn - 1) cy_val).
  replace (rn - 1 + 1) with rn by lia.
  sep_apply_l_atomic (UIntArray.seg_to_full rp (rn - 1) rn (cy_val :: nil)).
  replace (UIntArray.full (rp + (rn - 1) * sizeof(UINT)) 1 (cy_val :: nil))
    with (UIntArray.full (rp + (rn - 1) * sizeof(UINT)) (rn - (rn - 1)) (cy_val :: nil))
    by (f_equal; lia).
  sep_apply_l_atomic (UIntArray.seg_to_full rp 0 (rn - 1) (l ++ l_out)).
  replace (rp + 0 * sizeof(UINT)) with rp by lia.
  replace (rn - 1 - 0) with (rn - 1) by lia.
  sep_apply (UIntArray.full_merge_to_full rp (rn - 1) rn
    (l ++ l_out) (cy_val :: nil)); try lia.
  replace ((l ++ l_out) ++ cy_val :: nil)
    with (l ++ l_out ++ cy_val :: nil) by (rewrite app_assoc; reflexivity).
  sep_apply (UIntArray_full_to_mpd_store_Z_compact rp rn
    (l ++ l_out ++ cy_val :: nil)
    (Zabs (z_eq * 2 ^ bits_pre))); try assumption.
  replace (rn - 0) with rn by lia.
  entailer!; try lia.
  assert (Hprod_nonneg : 0 <= z_eq * 2 ^ bits_pre).
  { apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]. }
  unfold same_sign; lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_return_wit_4 : mpz_mul_2exp_return_wit_4.
Proof.
  pre_process.
  subst r_pre.
  subst u__mp_alloc.
  subst u__mp_d.
  assert (Hz_neg : z_eq < 0) by (unfold same_sign in PreH9; lia).
  assert (Hbits_eq : bits_pre = 32 * limbs + shift).
  { rewrite (Z.quot_rem' bits_pre 32) at 1. lia. }
  assert (Hpow_eq : 2 ^ bits_pre = UINT_MOD ^ limbs * 2 ^ shift).
  {
    unfold UINT_MOD.
    rewrite Hbits_eq.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_mul_r by lia.
    reflexivity.
  }
  pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l_in PreH23 PreH25)
    as [Hin_lo Hin_hi].
  rewrite PreH22 in Hin_lo, Hin_hi.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH27) as Hout_bound.
  rewrite PreH26 in Hout_bound.
  assert (Hshift_bound : 1 <= 2 ^ shift < UINT_MOD).
  {
    split.
    - change 1 with (2 ^ 0).
      apply Z.pow_le_mono_r; lia.
    - unfold UINT_MOD.
      change 4294967296 with (2 ^ 32).
      apply Z.pow_lt_mono_r; lia.
  }
  assert (Hval_shift :
    Zabs z_eq * 2 ^ shift = list_to_Z UINT_MOD l_out).
  { rewrite <- PreH28. rewrite PreH5. ring. }
  assert (Hlen_join : Zlength (l ++ l_out ++ cy_val :: nil) = rn).
  {
    repeat rewrite Zlength_app.
    rewrite PreH2, PreH26.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  }
  assert (Hbound_join : list_within_bound UINT_MOD (l ++ l_out ++ cy_val :: nil)).
  {
    rewrite app_assoc.
    apply list_within_bound_app_single.
    apply list_within_bound_concat; assumption.
    rewrite PreH5.
    unfold UINT_MOD; lia.
  }
  assert (Hval_join :
    list_to_Z UINT_MOD (l ++ l_out ++ cy_val :: nil) =
    Zabs (z_eq * 2 ^ bits_pre)).
  {
    rewrite !list_to_Z_app by exact UINT_MOD_pos.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite PreH2, PreH4, PreH26.
    rewrite PreH5.
    replace (0 + UINT_MOD * 0) with 0 by ring.
    replace (0 + (list_to_Z UINT_MOD l_out + 0 * UINT_MOD ^ un) *
             UINT_MOD ^ limbs)
      with ((list_to_Z UINT_MOD l_out) * UINT_MOD ^ limbs) by ring.
    rewrite <- Hval_shift.
    rewrite Hpow_eq.
    rewrite Z.abs_mul.
    replace (Zabs (2 ^ bits_pre)) with (2 ^ bits_pre)
      by (rewrite Z.abs_eq; [reflexivity | apply Z.pow_nonneg; lia]).
    rewrite Z.abs_neq by lia.
    nia.
  }
  assert (Hhigh_zero :
    Znth (rn - 1) (l ++ l_out ++ cy_val :: nil) 0 = 0).
  {
    rewrite app_assoc.
    rewrite app_Znth2.
    - replace (rn - 1 - Zlength (l ++ l_out)) with 0 by
        (rewrite Zlength_app, PreH2, PreH26; lia).
      simpl.
      exact PreH5.
    - rewrite Zlength_app, PreH2, PreH26.
      lia.
  }
  assert (Hcompact_join :
    is_compact_Z UINT_MOD (Zabs (z_eq * 2 ^ bits_pre)) (rn - 1)).
  {
    apply is_compact_Z_from_bounds; [unfold UINT_MOD; lia | lia |].
    right.
    split; [lia |].
    split.
    - rewrite Hpow_eq.
      rewrite Z.abs_mul.
      replace (Zabs (2 ^ bits_pre)) with (2 ^ bits_pre)
        by (rewrite Z.abs_eq; [reflexivity | apply Z.pow_nonneg; lia]).
      rewrite Z.abs_neq by lia.
      replace (UINT_MOD ^ (rn - 1 - 1))
        with (UINT_MOD ^ (un - 1) * UINT_MOD ^ limbs).
      + nia.
      + replace (rn - 1 - 1) with ((un - 1) + limbs) by lia.
        rewrite Z.pow_add_r by (unfold UINT_MOD; lia).
        f_equal; lia.
    - rewrite Hpow_eq.
      rewrite Z.abs_mul.
      replace (Zabs (2 ^ bits_pre)) with (2 ^ bits_pre)
        by (rewrite Z.abs_eq; [reflexivity | apply Z.pow_nonneg; lia]).
      rewrite Z.abs_neq by lia.
      replace (UINT_MOD ^ (rn - 1))
        with (UINT_MOD ^ un * UINT_MOD ^ limbs).
      + rewrite <- Hval_shift in Hout_bound.
        nia.
      + replace (rn - 1) with (un + limbs) by lia.
        rewrite Z.pow_add_r by (unfold UINT_MOD; lia).
        f_equal; lia.
  }
  unfold store_Z.
  Exists rp (-(rn - 1)) (Z.max rn cap).
  replace (Zabs (-(rn - 1))) with (rn - 1) by lia.
  sep_apply UIntArray.full_to_seg.
  rewrite <- (UIntArray.seg_shift rp limbs 0 un l_out).
  replace (limbs + 0) with limbs by lia.
  replace (limbs + un) with (rn - 1) by lia.
  sep_apply (UIntArray.seg_merge_to_seg rp 0 limbs (rn - 1) l l_out); try lia.
  sep_apply_l_atomic (UIntArray.seg_single rp (rn - 1) cy_val).
  replace (rn - 1 + 1) with rn by lia.
  sep_apply_l_atomic (UIntArray.seg_to_full rp (rn - 1) rn (cy_val :: nil)).
  replace (UIntArray.full (rp + (rn - 1) * sizeof(UINT)) 1 (cy_val :: nil))
    with (UIntArray.full (rp + (rn - 1) * sizeof(UINT)) (rn - (rn - 1)) (cy_val :: nil))
    by (f_equal; lia).
  sep_apply_l_atomic (UIntArray.seg_to_full rp 0 (rn - 1) (l ++ l_out)).
  replace (rp + 0 * sizeof(UINT)) with rp by lia.
  replace (rn - 1 - 0) with (rn - 1) by lia.
  sep_apply (UIntArray.full_merge_to_full rp (rn - 1) rn
    (l ++ l_out) (cy_val :: nil)); try lia.
  replace ((l ++ l_out) ++ cy_val :: nil)
    with (l ++ l_out ++ cy_val :: nil) by (rewrite app_assoc; reflexivity).
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact rp rn
    (l ++ l_out ++ cy_val :: nil)
    (Zabs (z_eq * 2 ^ bits_pre)) (Z.max rn cap)); try assumption; try lia.
  entailer!; try lia.
  assert (Hpow_bits_pos : 0 < 2 ^ bits_pre).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hprod_neg : z_eq * 2 ^ bits_pre < 0).
  { apply Z.mul_neg_pos; lia. }
  unfold same_sign; lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_return_wit_5 : mpz_mul_2exp_return_wit_5.
Proof.
  pre_process.
  subst r_pre.
  subst u__mp_alloc.
  subst u__mp_d.
  assert (Hz_nonneg : 0 <= z_eq) by (unfold same_sign in PreH9; lia).
  assert (Hbits_eq : bits_pre = 32 * limbs + shift).
  { rewrite (Z.quot_rem' bits_pre 32) at 1. lia. }
  assert (Hpow_eq : 2 ^ bits_pre = UINT_MOD ^ limbs * 2 ^ shift).
  {
    unfold UINT_MOD.
    rewrite Hbits_eq.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_mul_r by lia.
    reflexivity.
  }
  pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l_in PreH23 PreH25)
    as [Hin_lo Hin_hi].
  rewrite PreH22 in Hin_lo, Hin_hi.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH27) as Hout_bound.
  rewrite PreH26 in Hout_bound.
  assert (Hshift_bound : 1 <= 2 ^ shift < UINT_MOD).
  {
    split.
    - change 1 with (2 ^ 0).
      apply Z.pow_le_mono_r; lia.
    - unfold UINT_MOD.
      change 4294967296 with (2 ^ 32).
      apply Z.pow_lt_mono_r; lia.
  }
  assert (Hval_shift :
    Zabs z_eq * 2 ^ shift = list_to_Z UINT_MOD l_out).
  { rewrite <- PreH28. rewrite PreH5. ring. }
  assert (Hlen_join : Zlength (l ++ l_out ++ cy_val :: nil) = rn).
  {
    repeat rewrite Zlength_app.
    rewrite PreH2, PreH26.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  }
  assert (Hbound_join : list_within_bound UINT_MOD (l ++ l_out ++ cy_val :: nil)).
  {
    rewrite app_assoc.
    apply list_within_bound_app_single.
    apply list_within_bound_concat; assumption.
    rewrite PreH5.
    unfold UINT_MOD; lia.
  }
  assert (Hval_join :
    list_to_Z UINT_MOD (l ++ l_out ++ cy_val :: nil) =
    Zabs (z_eq * 2 ^ bits_pre)).
  {
    rewrite !list_to_Z_app by exact UINT_MOD_pos.
    rewrite list_to_Z_cons, list_to_Z_nil.
    rewrite PreH2, PreH4, PreH26.
    rewrite PreH5.
    replace (0 + UINT_MOD * 0) with 0 by ring.
    replace (0 + (list_to_Z UINT_MOD l_out + 0 * UINT_MOD ^ un) *
             UINT_MOD ^ limbs)
      with ((list_to_Z UINT_MOD l_out) * UINT_MOD ^ limbs) by ring.
    rewrite <- Hval_shift.
    rewrite Hpow_eq.
    rewrite Z.abs_mul.
    replace (Zabs (2 ^ bits_pre)) with (2 ^ bits_pre)
      by (rewrite Z.abs_eq; [reflexivity | apply Z.pow_nonneg; lia]).
    nia.
  }
  assert (Hhigh_zero :
    Znth (rn - 1) (l ++ l_out ++ cy_val :: nil) 0 = 0).
  {
    rewrite app_assoc.
    rewrite app_Znth2.
    - replace (rn - 1 - Zlength (l ++ l_out)) with 0 by
        (rewrite Zlength_app, PreH2, PreH26; lia).
      simpl.
      exact PreH5.
    - rewrite Zlength_app, PreH2, PreH26.
      lia.
  }
  assert (Hcompact_join :
    is_compact_Z UINT_MOD (Zabs (z_eq * 2 ^ bits_pre)) (rn - 1)).
  {
    apply is_compact_Z_from_bounds; [unfold UINT_MOD; lia | lia |].
    right.
    split; [lia |].
    split.
    - rewrite Hpow_eq.
      rewrite Z.abs_mul.
      replace (Zabs (2 ^ bits_pre)) with (2 ^ bits_pre)
        by (rewrite Z.abs_eq; [reflexivity | apply Z.pow_nonneg; lia]).
      replace (UINT_MOD ^ (rn - 1 - 1))
        with (UINT_MOD ^ (un - 1) * UINT_MOD ^ limbs).
      + nia.
      + replace (rn - 1 - 1) with ((un - 1) + limbs) by lia.
        rewrite Z.pow_add_r by (unfold UINT_MOD; lia).
        f_equal; lia.
    - rewrite Hpow_eq.
      rewrite Z.abs_mul.
      replace (Zabs (2 ^ bits_pre)) with (2 ^ bits_pre)
        by (rewrite Z.abs_eq; [reflexivity | apply Z.pow_nonneg; lia]).
      replace (UINT_MOD ^ (rn - 1))
        with (UINT_MOD ^ un * UINT_MOD ^ limbs).
      + rewrite <- Hval_shift in Hout_bound.
        nia.
      + replace (rn - 1) with (un + limbs) by lia.
        rewrite Z.pow_add_r by (unfold UINT_MOD; lia).
        f_equal; lia.
  }
  unfold store_Z.
  Exists rp (rn - 1) (Z.max rn cap).
  replace (Zabs (rn - 1)) with (rn - 1) by lia.
  sep_apply UIntArray.full_to_seg.
  rewrite <- (UIntArray.seg_shift rp limbs 0 un l_out).
  replace (limbs + 0) with limbs by lia.
  replace (limbs + un) with (rn - 1) by lia.
  sep_apply (UIntArray.seg_merge_to_seg rp 0 limbs (rn - 1) l l_out); try lia.
  sep_apply_l_atomic (UIntArray.seg_single rp (rn - 1) cy_val).
  replace (rn - 1 + 1) with rn by lia.
  sep_apply_l_atomic (UIntArray.seg_to_full rp (rn - 1) rn (cy_val :: nil)).
  replace (UIntArray.full (rp + (rn - 1) * sizeof(UINT)) 1 (cy_val :: nil))
    with (UIntArray.full (rp + (rn - 1) * sizeof(UINT)) (rn - (rn - 1)) (cy_val :: nil))
    by (f_equal; lia).
  sep_apply_l_atomic (UIntArray.seg_to_full rp 0 (rn - 1) (l ++ l_out)).
  replace (rp + 0 * sizeof(UINT)) with rp by lia.
  replace (rn - 1 - 0) with (rn - 1) by lia.
  sep_apply (UIntArray.full_merge_to_full rp (rn - 1) rn
    (l ++ l_out) (cy_val :: nil)); try lia.
  replace ((l ++ l_out) ++ cy_val :: nil)
    with (l ++ l_out ++ cy_val :: nil) by (rewrite app_assoc; reflexivity).
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact rp rn
    (l ++ l_out ++ cy_val :: nil)
    (Zabs (z_eq * 2 ^ bits_pre)) (Z.max rn cap)); try assumption; try lia.
  entailer!; try lia.
  assert (Hprod_nonneg : 0 <= z_eq * 2 ^ bits_pre).
  { apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]. }
  unfold same_sign; lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_return_wit_6 : mpz_mul_2exp_return_wit_6.
Proof.
  pre_process.
  subst r_pre.
  subst u__mp_alloc.
  subst u__mp_d.
  assert (Hz_neg : z_eq < 0) by (unfold same_sign in PreH8; lia).
  assert (Hbits_eq : bits_pre = 32 * limbs).
  { rewrite (Z.quot_rem' bits_pre 32) at 1. lia. }
  assert (Hpow_eq : 2 ^ bits_pre = UINT_MOD ^ limbs).
  {
    unfold UINT_MOD.
    rewrite Hbits_eq.
    rewrite Z.pow_mul_r by lia.
    reflexivity.
  }
  assert (Hpow_pos : 0 < 2 ^ bits_pre).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hres_neg : z_eq * 2 ^ bits_pre < 0).
  { apply Z.mul_neg_pos; lia. }
  assert (Hsub_l : sublist 0 un l = l).
  { rewrite sublist_self by lia. reflexivity. }
  assert (Hbound_sub : list_within_bound UINT_MOD (sublist 0 un l)).
  { rewrite Hsub_l. exact PreH20. }
  assert (Hlen_join : Zlength (l_2 ++ sublist 0 un l) = rn).
  { rewrite Zlength_app, PreH2. rewrite Zlength_sublist by lia. lia. }
  assert (Hbound_join : list_within_bound UINT_MOD (l_2 ++ sublist 0 un l)).
  {
    clear -PreH3 Hbound_sub.
    induction l_2; simpl in *; auto.
    destruct PreH3 as [? ?].
    split; auto.
  }
  assert (Hval_join :
    list_to_Z UINT_MOD (l_2 ++ sublist 0 un l) =
    Zabs (z_eq * 2 ^ bits_pre)).
  {
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite PreH4, Hsub_l, PreH21, PreH2.
    rewrite <- Hpow_eq.
    rewrite Z.abs_mul.
    replace (Zabs (2 ^ bits_pre)) with (2 ^ bits_pre)
      by (rewrite Z.abs_eq; [reflexivity | lia]).
    ring.
  }
  assert (Hlast_join : last (l_2 ++ sublist 0 un l) 1 >= 1).
  {
    rewrite (list_last_eq_Znth_last (l_2 ++ sublist 0 un l) rn)
      by (try exact Hlen_join; lia).
    rewrite app_Znth2 by (rewrite PreH2; lia).
    rewrite PreH2.
    replace (rn - 1 - limbs) with (un - 1) by lia.
    rewrite Hsub_l.
    rewrite <- (list_last_eq_Znth_last l un); try lia.
  }
  assert (Hcompact_join :
    is_compact_Z UINT_MOD (Zabs (z_eq * 2 ^ bits_pre)) rn).
  {
    eapply is_compact_Z_from_full_last with
      (data := l_2 ++ sublist 0 un l);
      try exact Hlen_join; try exact Hbound_join; try exact Hval_join;
      try exact Hlast_join; lia.
  }
  unfold store_Z.
  Exists rp (-rn) (Z.max rn cap).
  replace (Zabs (- rn)) with rn by lia.
  sep_apply UIntArray.full_to_seg.
  rewrite <- (UIntArray.seg_shift rp limbs 0 un (sublist 0 un l)).
  replace (limbs + 0) with limbs by lia.
  replace (limbs + un) with rn by lia.
  sep_apply (UIntArray.seg_merge_to_seg rp 0 limbs rn
    l_2 (sublist 0 un l)); try lia.
  sep_apply (UIntArray.seg_to_full rp 0 rn
    (l_2 ++ sublist 0 un l)).
  replace (rp + 0 * sizeof(UINT)) with rp by lia.
  replace (rn - 0) with rn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact rp rn
    (l_2 ++ sublist 0 un l)
    (Zabs (z_eq * 2 ^ bits_pre))); try assumption.
  replace (un + limbs) with rn by lia.
  entailer!.
  unfold same_sign; lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_return_wit_7 : mpz_mul_2exp_return_wit_7.
Proof.
  pre_process.
  subst r_pre.
  subst u__mp_alloc.
  subst u__mp_d.
  assert (Hsize_pos : size > 0) by lia.
  assert (Hz_nonneg : 0 <= z_eq) by (unfold same_sign in PreH8; lia).
  assert (Hzabs : Zabs z_eq = z_eq) by lia.
  assert (Hbits_eq : bits_pre = 32 * limbs).
  { rewrite (Z.quot_rem' bits_pre 32) at 1. lia. }
  assert (Hpow_eq : 2 ^ bits_pre = UINT_MOD ^ limbs).
  {
    unfold UINT_MOD.
    rewrite Hbits_eq.
    rewrite Z.pow_mul_r by lia.
    reflexivity.
  }
  assert (Hsub_l : sublist 0 un l = l).
  { rewrite sublist_self by lia. reflexivity. }
  assert (Hbound_sub : list_within_bound UINT_MOD (sublist 0 un l)).
  { rewrite Hsub_l. exact PreH20. }
  assert (Hlen_join : Zlength (l_2 ++ sublist 0 un l) = rn).
  { rewrite Zlength_app, PreH2. rewrite Zlength_sublist by lia. lia. }
  assert (Hbound_join : list_within_bound UINT_MOD (l_2 ++ sublist 0 un l)).
  {
    clear -PreH3 Hbound_sub.
    induction l_2; simpl in *; auto.
    destruct PreH3 as [? ?].
    split; auto.
  }
  assert (Hval_join :
    list_to_Z UINT_MOD (l_2 ++ sublist 0 un l) =
    Zabs (z_eq * 2 ^ bits_pre)).
  {
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite PreH4, Hsub_l, PreH21, PreH2, Hzabs.
    rewrite <- Hpow_eq.
    rewrite Z.abs_eq by
      (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]).
    ring.
  }
  assert (Hlast_join : last (l_2 ++ sublist 0 un l) 1 >= 1).
  {
    rewrite (list_last_eq_Znth_last (l_2 ++ sublist 0 un l) rn)
      by (try exact Hlen_join; lia).
    rewrite app_Znth2 by (rewrite PreH2; lia).
    rewrite PreH2.
    replace (rn - 1 - limbs) with (un - 1) by lia.
    rewrite Hsub_l.
    rewrite <- (list_last_eq_Znth_last l un); try lia.
  }
  assert (Hcompact_join :
    is_compact_Z UINT_MOD (Zabs (z_eq * 2 ^ bits_pre)) rn).
  {
    eapply is_compact_Z_from_full_last with
      (data := l_2 ++ sublist 0 un l);
      try exact Hlen_join; try exact Hbound_join; try exact Hval_join;
      try exact Hlast_join; lia.
  }
  unfold store_Z.
  Exists rp rn (Z.max rn cap).
  replace (Zabs rn) with rn by lia.
  sep_apply UIntArray.full_to_seg.
  rewrite <- (UIntArray.seg_shift rp limbs 0 un (sublist 0 un l)).
  replace (limbs + 0) with limbs by lia.
  replace (limbs + un) with rn by lia.
  sep_apply (UIntArray.seg_merge_to_seg rp 0 limbs rn
    l_2 (sublist 0 un l)); try lia.
  sep_apply (UIntArray.seg_to_full rp 0 rn
    (l_2 ++ sublist 0 un l)).
  replace (rp + 0 * sizeof(UINT)) with rp by lia.
  replace (rn - 0) with rn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact rp rn
    (l_2 ++ sublist 0 un l)
    (Zabs (z_eq * 2 ^ bits_pre))); try assumption.
  replace (un + limbs) with rn by lia.
  entailer!.
  unfold same_sign; lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_1_pure : mpz_mul_2exp_partial_solve_wit_1_pure.
Proof.
  pre_process.
  prop_apply_p (mpd_store_Z_compact_range UINT_MOD ptr (Zabs z_eq) (Zabs size)).
  Intros Habs_range.
  change Int.max_unsigned with 4294967295 in H.
  assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.
  rewrite Hcalc in H.
  assert (Habs_bound : Zabs size <= 2147483647) by nia.
  pose proof (proj1 (Z.abs_le size 2147483647) Habs_bound) as Hrange.
  split_pures.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_3_pure : mpz_mul_2exp_partial_solve_wit_3_pure.
Proof.
  unfold mpz_mul_2exp_partial_solve_wit_3_pure.
  right.
  pre_process.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z_eq) (Zabs size)).
  Intros Hcompact.
  assert (Hz_nonzero : z_eq <> 0).
  {
    intro Hz.
    subst z_eq.
    rewrite Z.abs_0 in H.
    assert (0 < Zabs size) by lia.
    pose proof (is_compact_Z_size_pos_value_pos 0 (Zabs size) H H0).
    lia.
  }
  unfold mpz_mul_2exp_fits in PreH18.
  pose proof (PreH18 (Zabs size) Hz_nonzero H) as Hfits.
  assert (Hquot : bits_pre ÷ 32 = bits_pre / 32).
  { apply Z.quot_div_nonneg; lia. }
  assert (Hbits_div_nonneg : 0 <= bits_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hrem_range : 0 <= bits_pre % 32 < 32).
  { apply Z.rem_bound_pos; lia. }
  assert (Hunsigned : unsigned_last_nbits (bits_pre % 32) 32 = bits_pre % 32).
  { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296. lia. }
  assert (Hshift_zero : unsigned_last_nbits (bits_pre % 32) 32 = 0) by lia.
  assert (Hrem0 : bits_pre % 32 = 0) by (rewrite Hunsigned in Hshift_zero; lia).
  assert (Hbits_div_range : - 2 ^ (32 - 1) <= bits_pre ÷ 32 < 2 ^ (32 - 1)).
  {
    change (2 ^ (32 - 1)) with 2147483648.
    pose proof (Z.abs_nonneg size).
    destruct (Z.eq_dec (bits_pre % 32) 0); [lia | congruence].
  }
  assert (Hsigned : signed_last_nbits (bits_pre ÷ 32) 32 = bits_pre ÷ 32).
  { apply signed_last_nbits_eq; [lia | exact Hbits_div_range]. }
  rewrite Hsigned in *.
  split_pures; dump_pre_spatial; try lia.
Qed. 

Lemma proof_of_mpz_mul_2exp_partial_solve_wit_4_pure : mpz_mul_2exp_partial_solve_wit_4_pure.
Proof.
  unfold mpz_mul_2exp_partial_solve_wit_4_pure.
  right.
  pre_process.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z_eq) (Zabs size)).
  Intros Hcompact.
  assert (Hz_nonzero : z_eq <> 0).
  {
    intro Hz.
    subst z_eq.
    rewrite Z.abs_0 in H.
    assert (0 < Zabs size) by lia.
    pose proof (is_compact_Z_size_pos_value_pos 0 (Zabs size) H H0).
    lia.
  }
  unfold mpz_mul_2exp_fits in PreH18.
  pose proof (PreH18 (Zabs size) Hz_nonzero H) as Hfits.
  assert (Hquot : bits_pre ÷ 32 = bits_pre / 32).
  { apply Z.quot_div_nonneg; lia. }
  assert (Hbits_div_nonneg : 0 <= bits_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hrem_range : 0 <= bits_pre % 32 < 32).
  { apply Z.rem_bound_pos; lia. }
  assert (Hunsigned : unsigned_last_nbits (bits_pre % 32) 32 = bits_pre % 32).
  { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296. lia. }
  destruct (Z.eq_dec (bits_pre % 32) 0) as [Hrem0 | Hremnz].
  {
    rewrite Hrem0 in PreH1.
    change (unsigned_last_nbits 0 32) with 0 in PreH1.
    lia.
  }
  assert (Hbits_div_range : - 2 ^ (32 - 1) <= bits_pre ÷ 32 < 2 ^ (32 - 1)).
  {
    change (2 ^ (32 - 1)) with 2147483648.
    pose proof (Z.abs_nonneg size).
    destruct (Z.eq_dec (bits_pre % 32) 0); [congruence | lia].
  }
  assert (Hsigned : signed_last_nbits (bits_pre ÷ 32) 32 = bits_pre ÷ 32).
  { apply signed_last_nbits_eq; [lia | exact Hbits_div_range]. }
  rewrite Hsigned in *.
  split_pures; dump_pre_spatial; try lia.
Qed. 
