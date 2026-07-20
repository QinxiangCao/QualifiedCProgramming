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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import mod_inv_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import mod_inv_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_odd_positive_entail_wit_1 : mpz_odd_positive_entail_wit_1.
Proof.
  unfold mpz_odd_positive_entail_wit_1.
  left.
  intros.
  sep_apply (store_Z_to_store_Z_read0_nonzero x_pre z); try lia.
  entailer!.
Qed.

Lemma proof_of_mpz_odd_positive_entail_wit_2 : mpz_odd_positive_entail_wit_2.
Proof.
  unfold mpz_odd_positive_entail_wit_2.
  left.
  intros.
  unfold store_Z_read0.
  Intros ptr size cap.
  unfold mpd_store_Z_compact_read0.
  Intros data.
  destruct H1 as [Hval [Hlast [Hbound Hlen]]].
  Exists ptr data cap size.
  sep_apply (UIntArray.full_split_to_seg ptr 1 (Zmax (Zabs size) 1)
                (mpd_read0_data data)).
  - entailer!.
  - unfold Zmax; lia.
Qed.

Lemma proof_of_mpz_odd_positive_return_wit_1 : mpz_odd_positive_return_wit_1.
Proof.
  unfold mpz_odd_positive_return_wit_1.
  left.
  intros.
  split_pure_spatial.
  - unfold store_Z.
    Exists ptr size cap.
    entailer!.
    sep_apply (UIntArray_read0_split_to_full ptr (Zabs size) data);
      try (symmetry; exact PreH7).
    sep_apply (UIntArray_full_to_mpd_store_Z_compact_read0 ptr (Zabs z) (Zabs size) data);
      try assumption; try (symmetry; exact PreH7).
    sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact ptr (Zabs z) (Zabs size) cap).
    entailer!.
  - entailer!.
    rewrite Z.rem_mod_nonneg by lia.
    apply (list_to_Z_limb0_land_even_mod2 data z); try assumption; try lia.
Qed.

Lemma proof_of_mpz_odd_positive_return_wit_2 : mpz_odd_positive_return_wit_2.
Proof.
  unfold mpz_odd_positive_return_wit_2.
  left.
  intros.
  split_pure_spatial.
  - unfold store_Z.
    Exists ptr size cap.
    entailer!.
    sep_apply (UIntArray_read0_split_to_full ptr (Zabs size) data);
      try (symmetry; exact PreH7).
    sep_apply (UIntArray_full_to_mpd_store_Z_compact_read0 ptr (Zabs z) (Zabs size) data);
      try assumption; try (symmetry; exact PreH7).
    sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact ptr (Zabs z) (Zabs size) cap).
    entailer!.
  - entailer!.
    rewrite Z.rem_mod_nonneg by lia.
    apply (list_to_Z_limb0_land_odd_mod2 data z); try assumption; try lia.
Qed.

Lemma proof_of_mod_inv_gmp_entail_wit_1_1 : mod_inv_gmp_entail_wit_1_1.
Proof.
  unfold mod_inv_gmp_entail_wit_1_1.
  right.
  intros.
  assert (Hsame : same_sign retval_5 (zp_low_level_spec - 2)).
  { unfold same_sign; left; lia. }
  assert (Hret : mpz_div_qr_ret_ok retval_5 (zp_low_level_spec - 2)).
  { unfold mpz_div_qr_ret_ok; split; intros; lia. }
  Exists za_low_level_spec (zp_low_level_spec - 2) out 1.
  entailer!.
  - apply mod_inv_pow_loop_init; [exact PreH11 | lia | exact PreH3].
  - unfold mod_norm_spec in PreH3; lia.
  - unfold mod_norm_spec in PreH3; lia.
Qed.

Lemma proof_of_mod_inv_gmp_entail_wit_1_2 : mod_inv_gmp_entail_wit_1_2.
Proof.
  unfold mod_inv_gmp_entail_wit_1_2.
  left.
  intros.
  assert (Hsame : same_sign retval_5 (zp_low_level_spec - 2)).
  { unfold same_sign; left; lia. }
  assert (Hret : mpz_div_qr_ret_ok retval_5 (zp_low_level_spec - 2)).
  { unfold mpz_div_qr_ret_ok; split; intros; lia. }
  Exists za_low_level_spec (zp_low_level_spec - 2) out 1.
  entailer!.
  - apply mod_inv_pow_loop_init; [exact PreH11 | lia | exact PreH3].
  - unfold mod_norm_spec in PreH3; lia.
  - unfold mod_norm_spec in PreH3; lia.
Qed.

Lemma proof_of_mod_inv_gmp_entail_wit_4_1 : mod_inv_gmp_entail_wit_4_1.
Proof.
  unfold mod_inv_gmp_entail_wit_4_1.
  left.
  intros.
  exfalso.
  rewrite Z.pow_1_r in PreH1.
  pose proof (Z.quot_pos zexp_2 2 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_mod_inv_gmp_entail_wit_4_2 : mod_inv_gmp_entail_wit_4_2.
Proof.
  unfold mod_inv_gmp_entail_wit_4_2.
  right.
  intros.
  pose proof PreH3 as Hbase_norm.
  pose proof PreH4 as Hres_norm.
  unfold mod_norm_spec in PreH3, PreH4.
  destruct PreH3 as [_ [[Hout2_lo Hout2_hi] _]].
  destruct PreH4 as [_ [[Hout_lo Hout_hi] _]].
  assert (Hsame : same_sign retval (Z.quot zexp_2 (Z.pow 2 1))).
  { unfold same_sign; left; lia. }
  assert (Hret : mpz_div_qr_ret_ok retval (Z.quot zexp_2 (Z.pow 2 1))).
  { unfold mpz_div_qr_ret_ok; split; intros; lia. }
  assert (Hzexp_pos : zexp_2 > 0).
  { unfold mpz_div_qr_ret_ok in PreH24.
    destruct PreH24 as [_ Hnonzero].
    assert (Hzexp_nonzero : zexp_2 <> 0) by (apply Hnonzero; lia).
    lia. }
  Exists (zbase_2 * zbase_2)
         (Z.quot zexp_2 (Z.pow 2 1))
         out_2 out.
  entailer!.
  eapply (mod_inv_pow_loop_step_odd
            zp_low_level_spec za_low_level_spec
            zresult_2 zbase_2 zexp_2 out out_2);
    [exact PreH25 | exact Hzexp_pos | exact PreH6 |
     exact Hres_norm | exact Hbase_norm].
Qed.

Lemma proof_of_mod_inv_gmp_entail_wit_4_3 : mod_inv_gmp_entail_wit_4_3.
Proof.
  unfold mod_inv_gmp_entail_wit_4_3.
  left.
  intros.
  pose proof PreH3 as Hbase_norm.
  pose proof PreH4 as Hres_norm.
  unfold mod_norm_spec in PreH3, PreH4.
  destruct PreH3 as [_ [[Hout2_lo Hout2_hi] _]].
  destruct PreH4 as [_ [[Hout_lo Hout_hi] _]].
  assert (Hsame : same_sign retval (Z.quot zexp_2 (Z.pow 2 1))).
  { unfold same_sign; left; lia. }
  assert (Hret : mpz_div_qr_ret_ok retval (Z.quot zexp_2 (Z.pow 2 1))).
  { unfold mpz_div_qr_ret_ok; split; intros; lia. }
  assert (Hzexp_pos : zexp_2 > 0).
  { unfold mpz_div_qr_ret_ok in PreH24.
    destruct PreH24 as [_ Hnonzero].
    assert (Hzexp_nonzero : zexp_2 <> 0) by (apply Hnonzero; lia).
    lia. }
  Exists (zbase_2 * zbase_2)
         (Z.quot zexp_2 (Z.pow 2 1))
         out_2 out.
  entailer!.
  - apply store_int_undef_store_int.
  - eapply (mod_inv_pow_loop_step_odd
              zp_low_level_spec za_low_level_spec
              zresult_2 zbase_2 zexp_2 out out_2);
      [exact PreH25 | exact Hzexp_pos | exact PreH6 |
       exact Hres_norm | exact Hbase_norm].
Qed.

Lemma proof_of_mod_inv_gmp_entail_wit_4_4 : mod_inv_gmp_entail_wit_4_4.
Proof.
  unfold mod_inv_gmp_entail_wit_4_4.
  left.
  intros.
  exfalso.
  rewrite Z.pow_1_r in PreH1.
  pose proof (Z.quot_pos zexp_2 2 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_mod_inv_gmp_entail_wit_4_5 : mod_inv_gmp_entail_wit_4_5.
Proof.
  unfold mod_inv_gmp_entail_wit_4_5.
  right.
  intros.
  pose proof PreH3 as Hbase_norm.
  unfold mod_norm_spec in PreH3.
  destruct PreH3 as [_ [[Hout_lo Hout_hi] _]].
  assert (Hsame : same_sign retval (Z.quot zexp_2 (Z.pow 2 1))).
  { unfold same_sign; left; lia. }
  assert (Hret : mpz_div_qr_ret_ok retval (Z.quot zexp_2 (Z.pow 2 1))).
  { unfold mpz_div_qr_ret_ok; split; intros; lia. }
  assert (Hzexp_pos : zexp_2 > 0).
  { unfold mpz_div_qr_ret_ok in PreH23.
    destruct PreH23 as [_ Hnonzero].
    assert (Hzexp_nonzero : zexp_2 <> 0) by (apply Hnonzero; lia).
    lia. }
  Exists (zbase_2 * zbase_2)
         (Z.quot zexp_2 (Z.pow 2 1))
         out zresult_2.
  entailer!.
  eapply (mod_inv_pow_loop_step_even
            zp_low_level_spec za_low_level_spec
            zresult_2 zbase_2 zexp_2 out);
    [exact PreH24 | exact Hzexp_pos | exact PreH5 | exact Hbase_norm].
Qed.

Lemma proof_of_mod_inv_gmp_entail_wit_4_6 : mod_inv_gmp_entail_wit_4_6.
Proof.
  unfold mod_inv_gmp_entail_wit_4_6.
  left.
  intros.
  pose proof PreH3 as Hbase_norm.
  unfold mod_norm_spec in PreH3.
  destruct PreH3 as [_ [[Hout_lo Hout_hi] _]].
  assert (Hsame : same_sign retval (Z.quot zexp_2 (Z.pow 2 1))).
  { unfold same_sign; left; lia. }
  assert (Hret : mpz_div_qr_ret_ok retval (Z.quot zexp_2 (Z.pow 2 1))).
  { unfold mpz_div_qr_ret_ok; split; intros; lia. }
  assert (Hzexp_pos : zexp_2 > 0).
  { unfold mpz_div_qr_ret_ok in PreH23.
    destruct PreH23 as [_ Hnonzero].
    assert (Hzexp_nonzero : zexp_2 <> 0) by (apply Hnonzero; lia).
    lia. }
  Exists (zbase_2 * zbase_2)
         (Z.quot zexp_2 (Z.pow 2 1))
         out zresult_2.
  entailer!.
  - apply store_int_undef_store_int.
  - eapply (mod_inv_pow_loop_step_even
              zp_low_level_spec za_low_level_spec
              zresult_2 zbase_2 zexp_2 out);
      [exact PreH24 | exact Hzexp_pos | exact PreH5 | exact Hbase_norm].
Qed.

Lemma proof_of_mod_inv_gmp_return_wit_1 : mod_inv_gmp_return_wit_1.
Proof.
  unfold mod_inv_gmp_return_wit_1.
  left.
  intros.
  assert (Hs_nonneg : 0 <= s).
  { unfold same_sign in PreH17.
    destruct PreH17 as [[Hs _] | [Hs Hz]]; lia. }
  assert (Hs_zero : s = 0) by lia.
  unfold mpz_div_qr_ret_ok in PreH18.
  destruct PreH18 as [Hzero _].
  assert (Hzexp_zero : zexp = 0) by (apply Hzero; exact Hs_zero).
  Exists zresult.
  entailer!.
  rewrite Hzexp_zero in PreH19.
  exact (mod_inv_pow_loop_done_inverse _ _ _ _ PreH19).
Qed.

Lemma proof_of_mod_inv_gmp_partial_solve_wit_15_pure : mod_inv_gmp_partial_solve_wit_15_pure.
Proof.
  unfold mod_inv_gmp_partial_solve_wit_15_pure.
  left.
  intros.
  unfold mpz_div_qr_ret_ok in PreH18.
  destruct PreH18 as [_ Hnonzero].
  assert (Hzexp_nonzero : zexp <> 0) by (apply Hnonzero; lia).
  entailer!.
Qed.
