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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_make_odd_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_make_odd_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_common_scan_safety_wit_3 : mpn_common_scan_safety_wit_3.
Proof.
  right.
  pre_process.
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [Hi [Hpos Hcase]]]].
  destruct Hcase as [[Heq Hnz] | [Hlt _]].
  - subst. exfalso; lia.
  - split_pures.
    all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpn_common_scan_safety_wit_4 : mpn_common_scan_safety_wit_4.
Proof.
  right.
  pre_process.
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [_ [_ [Hi [Hpos Hcase]]]].
  destruct Hcase as [[Heq Hnz] | [Hlt _]].
  - subst. exfalso; lia.
  - split_pures.
    all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_1 : mpn_common_scan_entail_wit_2_1.
Proof.
  right.
  pre_process.
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [Hux [Hlimb [Hi [Hpos Hcase]]]].
  destruct Hcase as [[Heq Hnz] |
                     [Hi_pos [Hlimb0 [Hzero [Hneq_un Hscan]]]]].
  - subst; exfalso; lia.
  - split_pure_spatial.
    + pre_process.
    + split_pures.
      * dump_pre_spatial.
        replace ((i_pre + 1) - 1) with i_pre by lia.
        unfold mpn_common_scan_target.
        repeat split; try lia; try assumption.
        right; repeat split; try lia; try assumption.
      * dump_pre_spatial; lia.
      * dump_pre_spatial; lia.
      * dump_pre_spatial. apply Hneq_un; lia.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_2_2 : mpn_common_scan_entail_wit_2_2.
Proof.
  right.
  pre_process.
  unfold mpn_common_scan_target in PreH7.
  destruct PreH7 as [Hux [Hlimb [Hi [Hpos Hcase]]]].
  destruct Hcase as [[Heq Hnz] |
                     [Hi_pos [Hlimb0 [Hzero [Hneq_un Hscan]]]]].
  - subst; exfalso; lia.
  - split_pure_spatial.
    + pre_process.
    + split_pures.
      * dump_pre_spatial.
        replace ((i + 1) - 1) with i by lia.
        unfold mpn_common_scan_target.
        repeat split; try lia; try assumption.
        right; repeat split; try lia; try assumption.
      * dump_pre_spatial; lia.
      * dump_pre_spatial; lia.
      * dump_pre_spatial. apply Hneq_un; lia.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_3 : mpn_common_scan_entail_wit_3.
Proof.
  right.
  pre_process.
  unfold mpn_common_scan_target in PreH12.
  destruct PreH12 as [Hux [Hlimb_range [Hi_old [Hpos Hcase]]]].
  destruct Hcase as [[Hpos_i Hlimb_ne] |
                     [Hi_pos [Hlimb0 [Hzero [Hneq_un Hscan]]]]].
  - subst. lia.
  - pose proof (list_within_bound_Znth_bound UINT_MOD l_found i
                  ltac:(lia) PreH10) as Hzi.
    assert (Hnew_range :
              0 <= Z.lxor ux_pre (Znth i l_found 0) <= 4294967295).
    {
      destruct Hux as [Hux0 | Huxmax]; subst.
      - rewrite Z.lxor_0_l.
        change UINT_MOD with 4294967296 in Hzi.
        lia.
      - rewrite Z.lxor_comm.
        change UINT_MOD with 4294967296 in Hzi.
        rewrite lxor_uintmax_sub by lia.
        lia.
    }
    split_pure_spatial.
    + pre_process.
    + split_pures.
      * dump_pre_spatial.
        unfold gmp_scan_limb.
        reflexivity.
      * dump_pre_spatial.
        unfold mpn_common_scan_target.
        repeat split; try lia; try assumption.
        destruct (Z.eq_dec i pos_found) as [Heq | Hneq].
        -- left.
           split; [lia |].
           subst pos_found.
           unfold gmp_scan_limb in Hscan.
           exact Hscan.
        -- right.
           repeat split; try lia; try assumption.
           ++ unfold gmp_scan_limb. apply Hzero; lia.
           ++ intros k Hk. apply Hzero; lia.
           ++ intros k Hk. apply Hneq_un; lia.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_5_1 : mpn_common_scan_entail_wit_5_1.
Proof.
  pre_process.
  Exists odd_2.
  split_pure_spatial.
  - cancel (UIntArray.full up_pre n_found l_found).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_mpn_common_scan_entail_wit_5_2 : mpn_common_scan_entail_wit_5_2.
Proof.
  pre_process.
  Right.
  Exists i_2.
  Exists limb_2.
  Exists odd_2.
  split_pure_spatial.
  - cancel (UIntArray.full up_pre n_found l_found).
    cancel (&( "i") # Int |-> i_2).
    cancel (&( "limb") # UInt |-> limb_2).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_mpn_common_scan_return_wit_1 : mpn_common_scan_return_wit_1.
Proof.
  right.
  pre_process.
  unfold mpn_common_scan_target in PreH10.
  destruct PreH10 as [Hux [Hlimb_range [Hi [Hpos Hcase]]]].
  destruct Hcase as [[Hpos_i Hlimb_ne] |
                     [Hi_pos [Hlimb0 [Hzero [Hneq_un Hscan]]]]].
  - subst pos_found.
    assert (Hi_bound : 0 <= i_pre < 2147483647) by lia.
    assert (Hret :
      unsigned_last_nbits
        (unsigned_last_nbits
           (unsigned_last_nbits i_pre 64 * 32) 64 + cnt) 64 =
      i_pre * 32 + cnt).
    {
      rewrite (unsigned_last_nbits_eq i_pre 64)
        by (change (2 ^ 64) with 18446744073709551616; nia).
      rewrite (unsigned_last_nbits_eq (i_pre * 32) 64)
        by (change (2 ^ 64) with 18446744073709551616; nia).
      rewrite (unsigned_last_nbits_eq (i_pre * 32 + cnt) 64)
        by (change (2 ^ 64) with 18446744073709551616; nia).
      ring.
    }
    split_pure_spatial.
    + pre_process.
    + dump_pre_spatial.
      unfold mpn_common_scan_result.
      split; [exact PreH11 |].
      exists cnt, odd.
      repeat split; try lia.
      rewrite <- Z.rem_mod_nonneg by lia.
      exact PreH4.
  - subst limb_pre.
    assert (Hpow_pos : 0 < 2 ^ cnt) by (apply Z.pow_pos_nonneg; lia).
    nia.
Qed.

Lemma proof_of_mpn_common_scan_return_wit_2 : mpn_common_scan_return_wit_2.
Proof.
  right.
  pre_process.
  unfold mpn_common_scan_target in PreH11.
  destruct PreH11 as [Hux [Hlimb_range [Hi [Hpos Hcase]]]].
  destruct Hcase as [[Hpos_i Hlimb_ne] |
                     [Hi_pos [Hlimb0 [Hzero [Hneq_un Hscan]]]]].
  - subst pos_found.
    assert (Hi_bound : 0 <= i < 2147483647) by lia.
    assert (Hret :
      unsigned_last_nbits
        (unsigned_last_nbits
           (unsigned_last_nbits i 64 * 32) 64 + cnt) 64 =
      i * 32 + cnt).
    {
      rewrite (unsigned_last_nbits_eq i 64)
        by (change (2 ^ 64) with 18446744073709551616; nia).
      rewrite (unsigned_last_nbits_eq (i * 32) 64)
        by (change (2 ^ 64) with 18446744073709551616; nia).
      rewrite (unsigned_last_nbits_eq (i * 32 + cnt) 64)
        by (change (2 ^ 64) with 18446744073709551616; nia).
      ring.
    }
    split_pure_spatial.
    + pre_process.
    + dump_pre_spatial.
      unfold mpn_common_scan_result.
      split; [exact PreH10 |].
      exists cnt, odd.
      repeat split; try lia.
      rewrite <- Z.rem_mod_nonneg by lia.
      exact PreH4.
  - subst limb.
    assert (Hpow_pos : 0 < 2 ^ cnt) by (apply Z.pow_pos_nonneg; lia).
    nia.
Qed.

Lemma proof_of_mpn_scan1_safety_wit_3 : mpn_scan1_safety_wit_3.
Proof.
  right.
  pre_process.
  assert (Hmod : 0 <= bit_pre % 32 < 32) by (apply Z.rem_bound_pos; lia).
  split_pures.
  all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpn_scan1_entail_wit_1 : mpn_scan1_entail_wit_1.
Proof.
  right.
  pre_process.
  unfold mpn_scan1_target in PreH7.
  destruct PreH7 as [Hbit_nonneg [pos Htarget]].
  assert (Hrem : 0 <= bit_pre % 32 < 32) by (apply Z.rem_bound_pos; lia).
  assert (Hsigned :
            signed_last_nbits (bit_pre ÷ 32) 32 = bit_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - split.
      + enough (0 <= bit_pre ÷ 32) by lia.
        apply Z.quot_pos; lia.
      + eapply Z.lt_le_trans; [exact PreH4 |].
        change INT_MAX with 2147483647 in PreH2.
        lia.
  }
  assert (Hq_nonneg : 0 <= bit_pre ÷ 32) by (apply Z.quot_pos; lia).
  assert (Htarget' :
            mpn_common_scan_target l
              (Z.land (Znth (signed_last_nbits (bit_pre ÷ 32) 32) l 0)
                 (unsigned_last_nbits (4294967295 * 2 ^ (bit_pre % 32)) 32))
              (signed_last_nbits (bit_pre ÷ 32) 32)
              (signed_last_nbits (bit_pre ÷ 32) 32) 0 pos).
  {
    rewrite Hsigned.
    assert (Hquot : bit_pre ÷ 32 = bit_pre / 32) by (apply Z.quot_div_nonneg; lia).
    assert (Hremmod : bit_pre % 32 = bit_pre mod 32) by (apply Z.rem_mod_nonneg; lia).
    rewrite Hquot.
    rewrite Hremmod.
    unfold gmp_scan1_limb, gmp_scan1_mask in Htarget.
    rewrite Z.shiftl_mul_pow2 in Htarget by (apply Z.mod_pos_bound; lia).
    exact Htarget.
  }
  Exists pos.
  split_pure_spatial.
  - pre_process.
  - split_pures.
    + dump_pre_spatial. exact Hsigned.
    + dump_pre_spatial. rewrite Hsigned; exact Hq_nonneg.
    + dump_pre_spatial. rewrite Hsigned; exact PreH4.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact Htarget'.
Qed.

Lemma proof_of_mpn_scan1_return_wit_1 : mpn_scan1_return_wit_1.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - pre_process.
  - dump_pre_spatial.
    eapply scan1_common_result_implies_scan1_result; eauto.
Qed.

Lemma proof_of_mpn_scan1_partial_solve_wit_2_pure : mpn_scan1_partial_solve_wit_2_pure.
Proof.
  right.
  pre_process.
  assert (Hrem : 0 <= bit_pre % 32 < 32) by (apply Z.rem_bound_pos; lia).
  dump_pre_spatial.
  rewrite Z.shiftl_mul_pow2 by lia.
  exact PreH11.
Qed.

Lemma proof_of_mpz_make_odd_entail_wit_1 : mpz_make_odd_entail_wit_1.
Proof.
  left.
  pre_process.
  unfold store_Z, mpd_store_Z_compact.
  Intros ptr size cap.
  Intros l.
  destruct H1 as [Hval [Hlast Hbound]].
  assert (Hsize_nonneg : size >= 0) by (eapply same_sign_pos_nonneg_r; eauto).
  assert (Habs_z : Zabs z = z) by lia.
  rewrite Habs_z in Hval.
  assert (Hlen_pos : Zlength l > 0).
  { eapply list_to_Z_positive_length. rewrite Hval. lia. }
  assert (Habs_size : Zabs size = size) by lia.
  assert (Hsize_pos : size > 0).
  { rewrite Habs_size in H2. lia. }
  assert (Htarget : mpn_scan1_target l 0).
  { apply (mpn_scan1_target_0_of_positive l z); auto. }
  Exists ptr l cap size.
  unfold mpd_store_list.
  rewrite Habs_size in *.
  rewrite H2.
  entailer!.
  rewrite <- H2.
  assumption.
Qed.

Lemma proof_of_mpz_make_odd_entail_wit_2 : mpz_make_odd_entail_wit_2.
Proof.
  left.
  pre_process.
  Exists ptr_2 l_2 cap_2 size_2.
  entailer!.
  unfold mpn_scan1_result in PreH1.
  lia.
Qed.

Lemma proof_of_mpz_make_odd_entail_wit_3 : mpz_make_odd_entail_wit_3.
Proof.
  left.
  pre_process.
  pose proof (mpn_scan1_result_make_odd l z shift PreH1 PreH7 PreH11)
    as [Hdecomp [Hodd Hoddpos]].
  Exists (Z.quot z (2 ^ shift)).
  unfold store_Z, mpd_store_Z_compact.
  Exists ptr size cap.
  Exists l.
  entailer!.
  unfold mpd_store_list.
  rewrite PreH6.
  replace (Zabs size) with size by lia.
  entailer!.
  rewrite Z.rem_mod_nonneg by lia.
  exact Hodd.
Qed.

Lemma proof_of_mpz_make_odd_partial_solve_wit_2_pure : mpz_make_odd_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  unfold store_Z.
  Intros ptr size cap.
  prop_apply (store_int_range (&(r_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap).
  Intros_p Hcap_range.
  change Int.max_signed with 2147483647 in Hcap_range.
  change Int.min_signed with (-2147483648) in Hcap_range.
  prop_apply (mpd_store_Z_compact_bound ptr (Zabs z) (Zabs size)).
  Intros_p Hz_bound.
  assert (Hz_pos : 0 < z).
  {
    subst z.
    apply Z.mul_pos_pos.
    - lia.
    - apply Z.pow_pos_nonneg; lia.
  }
  assert (Hpow_le_z : 2 ^ shift <= z).
  {
    subst z.
    assert (Hpow_pos : 0 < 2 ^ shift).
    { apply Z.pow_pos_nonneg; lia. }
    nia.
  }
  assert (Hpow_bound : 2 ^ shift < UINT_MOD ^ Zabs size).
  {
    rewrite Z.abs_eq in Hz_bound by lia.
    lia.
  }
  assert (Hshift_lt : shift < 32 * Zabs size).
  {
    change UINT_MOD with (2 ^ 32) in Hpow_bound.
    rewrite <- Z.pow_mul_r in Hpow_bound by lia.
    apply (proj2 (Z.pow_lt_mono_r_iff 2 shift (32 * Zabs size)
      ltac:(lia) ltac:(lia))).
    exact Hpow_bound.
  }
  assert (Hshift_div : shift ÷ 32 <= Zabs size).
  {
    apply Z.quot_le_upper_bound; lia.
  }
  entailer!.
Qed.
