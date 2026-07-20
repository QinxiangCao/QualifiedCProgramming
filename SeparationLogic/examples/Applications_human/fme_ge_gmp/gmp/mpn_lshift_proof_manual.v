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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_lshift_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_lshift_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_lshift_entail_wit_3_nonalias : mpn_lshift_entail_wit_3_nonalias.
Proof.
  unfold mpn_lshift_entail_wit_3_nonalias.
  left.
  intros.
  Exists (@nil Z).
  split_pure_spatial.
  - Intros.
    replace (n_pre - 1 + 1) with n_pre by lia.
    entailer!.
  - Intros.
    entailer!.
    + replace (sublist (n_pre - 1) n_pre l_up_nonalias)
        with (sublist (n_pre - 1) ((n_pre - 1) + 1) l_up_nonalias)
        by (f_equal; lia).
      rewrite mpn_lshift_list_to_Z_single_sublist by lia.
      rewrite list_to_Z_nil.
      replace (UINT_MOD ^ (n_pre - (n_pre - 1))) with UINT_MOD
        by (replace (n_pre - (n_pre - 1)) with 1 by lia; ring).
      ring_simplify.
      replace (UINT_MOD * Z.shiftr (Znth (n_pre - 1) l_up_nonalias 0) (32 - cnt_pre))
        with (Z.shiftr (Znth (n_pre - 1) l_up_nonalias 0) (32 - cnt_pre) * UINT_MOD) by ring.
      apply mpn_lshift_limb_decompose.
      * apply (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (n_pre - 1)); try exact PreH10; lia.
      * lia.
    + rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
    + rewrite Z.shiftr_div_pow2 by lia.
      symmetry.
      apply Z.quot_div_nonneg.
      * apply (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (n_pre - 1)); try exact PreH10; lia.
      * apply Z.pow_pos_nonneg; lia.
    + rewrite Zlength_nil. lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (n_pre - 1) ltac:(lia) PreH10) as Hb.
      unfold UINT_MOD in Hb. lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (n_pre - 1) ltac:(lia) PreH10) as Hb.
      lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace : mpn_lshift_entail_wit_4_inplace.
Proof.
  unfold mpn_lshift_entail_wit_4_inplace.
  left.
  intros.
  Exists (@nil Z).
  split_pure_spatial.
  - Intros.
    replace (n_pre - 1 + 1) with n_pre by lia.
    entailer!.
  - Intros.
    entailer!.
    + replace (sublist (n_pre - 1) n_pre l_up_inplace)
        with (sublist (n_pre - 1) ((n_pre - 1) + 1) l_up_inplace)
        by (f_equal; lia).
      rewrite mpn_lshift_list_to_Z_single_sublist by lia.
      rewrite list_to_Z_nil.
      replace (UINT_MOD ^ (n_pre - (n_pre - 1))) with UINT_MOD
        by (replace (n_pre - (n_pre - 1)) with 1 by lia; ring).
      ring_simplify.
      replace (UINT_MOD * Z.shiftr (Znth (n_pre - 1) l_up_inplace 0) (32 - cnt_pre))
        with (Z.shiftr (Znth (n_pre - 1) l_up_inplace 0) (32 - cnt_pre) * UINT_MOD) by ring.
      apply mpn_lshift_limb_decompose.
      * apply (list_within_bound_Znth_bound UINT_MOD l_up_inplace (n_pre - 1)); try exact PreH10; lia.
      * lia.
    + rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
    + rewrite Z.shiftr_div_pow2 by lia.
      symmetry.
      apply Z.quot_div_nonneg.
      * apply (list_within_bound_Znth_bound UINT_MOD l_up_inplace (n_pre - 1)); try exact PreH10; lia.
      * apply Z.pow_pos_nonneg; lia.
    + rewrite Zlength_nil. lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_up_inplace (n_pre - 1) ltac:(lia) PreH10) as Hb.
      unfold UINT_MOD in Hb. lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_up_inplace (n_pre - 1) ltac:(lia) PreH10) as Hb.
      lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_7_nonalias_inv : mpn_lshift_entail_wit_7_nonalias_inv.
Proof.
  unfold mpn_lshift_entail_wit_7_nonalias_inv.
  left.
  intros.
  Exists l_done_3.
  split_pure_spatial.
  - Intros.
    entailer!.
    replace (i - 1 + 2) with (i + 1) by lia.
    entailer!.
  - Intros.
    entailer!.
    + replace (i - 1 + 1) with i by lia.
      exact PreH16.
    + replace (i - 1 + 1) with i by lia.
      exact PreH15.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (i - 1) ltac:(rewrite PreH10; lia) PreH12) as Hb.
      unfold UINT_MOD in Hb. lia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (i - 1) ltac:(rewrite PreH10; lia) PreH12) as Hb.
      lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_8_inplace_inv : mpn_lshift_entail_wit_8_inplace_inv.
Proof.
  aggressive_pre_process.
  Exists l_done_3.
  entailer!.
  - replace (i - 1 + 2) with (i + 1) by nia.
    entailer!.
  - replace (i - 1 + 1) with i by nia.
    exact PreH16.
  - replace (i - 1 + 1) with i by nia.
    exact PreH15.
  - rewrite Znth_sublist by nia.
    replace (i - 1 - 0 + 0) with (i - 1) by nia.
    reflexivity.
  - rewrite Znth_sublist by nia.
    replace (i - 1 - 0 + 0) with (i - 1) by nia.
    pose proof (list_within_bound_Znth_bound UINT_MOD l_up_inplace (i - 1) ltac:(rewrite PreH10; nia) PreH12) as Hb.
    unfold UINT_MOD in Hb; nia.
  - rewrite Znth_sublist by nia.
    replace (i - 1 - 0 + 0) with (i - 1) by nia.
    pose proof (list_within_bound_Znth_bound UINT_MOD l_up_inplace (i - 1) ltac:(rewrite PreH10; nia) PreH12) as Hb.
    nia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_9_inplace_inv : mpn_lshift_entail_wit_9_inplace_inv.
Proof.
  aggressive_pre_process.
  entailer!.
  - apply mpn_lshift_initial_equation; try assumption.
    + nia.
    + split; assumption.
  - rewrite Zlength_nil. nia.
  - pose proof (list_within_bound_Znth_bound UINT_MOD l_up_inplace (n_pre - 1) ltac:(rewrite PreH9; nia) PreH11) as Hb.
    unfold UINT_MOD in Hb. nia.
  - pose proof (list_within_bound_Znth_bound UINT_MOD l_up_inplace (n_pre - 1) ltac:(rewrite PreH9; nia) PreH11) as Hb.
    nia.
  - apply (mpn_lshift_step_equation l_up_inplace l_done_3 n_pre i_2 cnt_pre retval_2 high_limb_2 low_limb_2 tnc_2);
      try assumption.
    + rewrite PreH9. nia.
    + split; assumption.
  - rewrite PreH6.
    rewrite Z.shiftl_mul_pow2 by nia.
    reflexivity.
  - apply (mpn_lshift_done_bound l_up_inplace l_done_3 n_pre i_2 cnt_pre high_limb_2 low_limb_2 tnc_2);
      try assumption.
    + rewrite PreH9. nia.
    + split; assumption.
    + split; assumption.
  - apply (mpn_lshift_done_length l_up_inplace l_done_3 n_pre i_2
             (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)));
      try assumption.
    rewrite PreH9. nia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_10_nonalias_inv : mpn_lshift_entail_wit_10_nonalias_inv.
Proof.
  aggressive_pre_process.
  Exists ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) :: l_done_3).
  split_pure_spatial.
  - sep_apply (UIntArray.seg_single rp_pre (i_2 + 1) (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))).
    replace (i_2 + 1 + 1) with (i_2 + 2) by lia.
    sep_apply (UIntArray.seg_merge_to_seg rp_pre (i_2 + 1) (i_2 + 2) n_pre
      ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) :: nil) l_done_3).
    simpl.
    entailer!.
    lia.
  - Intros.
    entailer!.
    + apply mpn_lshift_initial_equation; try assumption.
      * nia.
      * split; assumption.
    + rewrite Zlength_nil. nia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (n_pre - 1) ltac:(rewrite PreH11; nia) PreH13) as Hb.
      unfold UINT_MOD in Hb. nia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (n_pre - 1) ltac:(rewrite PreH11; nia) PreH13) as Hb.
      nia.
    + apply (mpn_lshift_step_equation_cons l_up_nonalias l_done_3 n_pre i_2 cnt_pre retval_2 high_limb_2 low_limb_2 tnc_2);
        try assumption.
      * rewrite PreH11. nia.
      * split; assumption.
    + rewrite PreH8.
      rewrite Z.shiftl_mul_pow2 by nia.
      reflexivity.
    + simpl.
      split.
      * unfold UINT_MOD in *. nia.
      * exact PreH14.
    + rewrite Zlength_cons.
      rewrite PreH12.
      unfold Z.succ.
      ring.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_11_nonalias_inv : mpn_lshift_entail_wit_11_nonalias_inv.
Proof.
  unfold mpn_lshift_entail_wit_11_nonalias_inv.
  right.
  intros.
  Exists l_done_3.
  assert (Hi0: i = 0) by nia.
  subst i.
  rewrite (sublist_self l_up_nonalias n_pre) in PreH16 by (symmetry; exact PreH10).
  replace (n_pre - 0) with n_pre in PreH16 by ring.
  entailer!.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_12_inplace_inv : mpn_lshift_entail_wit_12_inplace_inv.
Proof.
  unfold mpn_lshift_entail_wit_12_inplace_inv.
  right.
  intros.
  Exists l_done_3.
  assert (Hi0: i = 0) by nia.
  subst i.
  rewrite (sublist_self l_up_inplace n_pre) in PreH16 by (symmetry; exact PreH10).
  replace (n_pre - 0) with n_pre in PreH16 by ring.
  entailer!.
Qed.

Lemma proof_of_mpn_lshift_return_wit_1_inplace_inv : mpn_lshift_return_wit_1_inplace_inv.
Proof.
  unfold mpn_lshift_return_wit_1_inplace_inv.
  left.
  pre_process.
  subst rp_pre.
  set (prefix := replace_Znth 0 high_limb (sublist 0 1 l_up_inplace)).
  Exists (prefix ++ l_done).
  sep_apply UIntArray.full_to_seg.
  sep_apply (UIntArray.seg_merge_to_full up_pre 0 1 n_pre prefix l_done).
  sep_apply (UIntArray_full_list_within_bound_preserve
               (up_pre + 0 * sizeof(UINT)) (n_pre - 0) (prefix ++ l_done)).
  Intros.
  simpl.
  entailer!.
  - replace (up_pre + 0) with up_pre by nia.
    replace (n_pre - 0) with n_pre by nia.
    entailer!.
  - subst prefix.
    assert (Hrep:
      replace_Znth 0 high_limb (sublist 0 1 l_up_inplace) =
      high_limb :: nil).
    {
      rewrite (replace_Znth_sublist_head l_up_inplace 0 1 high_limb).
      - rewrite Zsublist_nil by nia.
        reflexivity.
      - pose proof (Zlength_nonneg l_done).
        rewrite PreH7.
        nia.
    }
    rewrite Hrep.
    simpl.
    rewrite list_to_Z_cons.
    replace (UINT_MOD * list_to_Z UINT_MOD l_done)
      with (list_to_Z UINT_MOD l_done * UINT_MOD) by ring.
    exact PreH12.
  - subst prefix.
    rewrite Zlength_app.
    rewrite Zlength_replace_Znth.
    rewrite Zlength_sublist by (pose proof (Zlength_nonneg l_done); rewrite PreH7; nia).
    nia.
  - pose proof (Zlength_nonneg l_done).
    nia.
Qed.

Lemma proof_of_mpn_lshift_return_wit_2_nonalias_inv : mpn_lshift_return_wit_2_nonalias_inv.
Proof.
  unfold mpn_lshift_return_wit_2_nonalias_inv.
  right.
  pre_process.
  Exists (high_limb :: l_done).
  sep_apply UIntArray.seg_single.
  replace (0 + 1) with 1 by nia.
  sep_apply (UIntArray.seg_merge_to_full rp_pre 0 1 n_pre
               (high_limb :: nil) l_done).
  simpl.
  entailer!.
  - replace (rp_pre + 0) with rp_pre by nia.
    replace (n_pre - 0) with n_pre by nia.
    entailer!.
  - rewrite list_to_Z_cons.
    replace (UINT_MOD * list_to_Z UINT_MOD l_done)
      with (list_to_Z UINT_MOD l_done * UINT_MOD) by ring.
    exact PreH14.
  - unfold UINT_MOD in *.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    nia.
  - rewrite Zlength_cons.
    nia.
  - pose proof (Zlength_nonneg l_done).
    nia.
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_2 : mpn_lshift_which_implies_wit_2.
Proof.
  unfold mpn_lshift_which_implies_wit_2.
  right.
  intros.
  rewrite (sublist_self l_up_inplace n_pre) by (symmetry; exact PreH3).
  entailer!.
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_4 : mpn_lshift_which_implies_wit_4.
Proof.
  pre_process.
  sep_apply (UIntArray.seg_split_to_seg up_pre 0 (i + 1) (i + 2)
               (sublist 0 (i + 2) l_up_inplace)); try nia.
  entailer!.
  replace (i + 1 - 0) with (i + 1) by nia.
  replace (i + 2 - 0) with (i + 2) by nia.
  rewrite Zsublist_Zsublist00 by nia.
  rewrite Zsublist_Zsublist0 by nia.
  entailer!.
Qed.
