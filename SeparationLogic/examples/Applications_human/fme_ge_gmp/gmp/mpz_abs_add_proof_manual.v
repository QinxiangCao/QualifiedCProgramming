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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_abs_add_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_abs_add_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_abs_add_safety_wit_1 : mpz_abs_add_safety_wit_1.
Proof.
  unfold mpz_abs_add_safety_wit_1.
  left.
  intros.
  prop_apply_p (mpd_store_Z_compact_range UINT_MOD bptr (Zabs zb_r_eq_a) (Zabs bsize)).
  Intros.
  pose proof H as Hb_range.
  change Int.max_unsigned with 4294967295 in Hb_range.
  assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.
  rewrite Hcalc in Hb_range.
  entailer!.
Qed.

Lemma proof_of_mpz_abs_add_safety_wit_3 : mpz_abs_add_safety_wit_3.
Proof.
  unfold mpz_abs_add_safety_wit_3.
  left.
  intros.
  prop_apply_p (mpd_store_Z_compact_range UINT_MOD rptr (Zabs za_r_eq_a) (Zabs rsize)).
  Intros.
  pose proof H as Hr_range.
  change Int.max_unsigned with 4294967295 in Hr_range.
  assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.
  rewrite Hcalc in Hr_range.
  entailer!.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_1 : mpz_abs_add_entail_wit_1.
Proof.
  pre_process.
  unfold store_Z.
  Intros rptr rsize rcap.
  Intros bptr bsize bcap.
  Exists bptr rptr bcap rcap bsize rsize.
  pre_process.
  prop_apply (store_int_range (&(a_pre # "__mpz_struct" ->ₛ "_mp_size")) rsize).
  Intros.
  prop_apply (store_int_range (&(a_pre # "__mpz_struct" ->ₛ "_mp_alloc")) rcap).
  Intros.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_size")) bsize).
  Intros.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_alloc")) bcap).
  Intros.
  match goal with
  | H : Int.min_signed <= rsize <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  match goal with
  | H : Int.min_signed <= rcap <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  match goal with
  | H : Int.min_signed <= bsize <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  match goal with
  | H : Int.min_signed <= bcap <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_2_rp_eq_ap : mpz_abs_add_entail_wit_2_rp_eq_ap.
Proof.
  pre_process.
  prop_apply (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) z_callee__mp_alloc).
  Intros.
  match goal with
  | H : Int.min_signed <= z_callee__mp_alloc <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  subst a_pre.
  Exists z_callee__mp_alloc.
  replace retval with (Zabs rsize) by lia.
  replace retval_2 with (Zabs bsize) by lia.
  replace z_callee__mp_alloc with (Z.max (Z.max (Zabs rsize + 1) 1) rcap) by lia.
  entailer!.
  all: lia.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_3_rp_eq_bp : mpz_abs_add_entail_wit_3_rp_eq_bp.
Proof.
  pre_process.
  prop_apply (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) z_callee__mp_alloc).
  Intros.
  match goal with
  | H : Int.min_signed <= z_callee__mp_alloc <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  subst a_pre.
  Exists z_callee__mp_alloc.
  replace retval with (Zabs rsize) by lia.
  replace retval_2 with (Zabs bsize) by lia.
  replace z_callee__mp_alloc with (Z.max (Z.max (Zabs bsize + 1) 1) rcap) by lia.
  sep_apply (UIntArray.undef_seg_split_to_undef_seg
    retval_3 (Zabs rsize) (Zabs bsize) (Z.max (Z.max (Zabs bsize + 1) 1) rcap)); try lia.
  entailer!.
  all: lia.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_6_rp_eq_ap : mpz_abs_add_entail_wit_6_rp_eq_ap.
Proof.
  pre_process.
  prop_apply (mpn_add_ret_0_or_1_compact
    rptr_new (Zabs za_r_eq_a) (Zabs zb_r_eq_a) val_r_out_2 an bn retval
    PreH14 PreH19 PreH16 PreH15).
  Intros.
  prop_apply (mpd_store_Z_bound rptr_new val_r_out_2 an).
  Intros.
  match goal with
  | Hb : 0 <= val_r_out_2 < UINT_MOD ^ an |- _ =>
      pose proof Hb as Hval_bound
  end.
  match goal with
  | Hret : retval = 0 \/ retval = 1 |- _ => destruct Hret as [Hret | Hret]; subst retval
  end.
  - assert (Hcompact: is_compact_Z UINT_MOD val_r_out_2 an).
    {
      replace val_r_out_2 with (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
      replace an with (Z.max an bn) by (rewrite Z.max_l; lia).
      eapply is_compact_Z_add_0; eauto.
      rewrite Z.max_l by lia.
      lia.
    }
    Left.
    Exists val_r_out_2.
    Exists rcap_new_2.
    subst a.
    sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) bn).
    entailer!.
    all: try lia; try assumption.
  - assert (Hcompact: is_compact_Z UINT_MOD (val_r_out_2 + UINT_MOD ^ an) (an + 1)).
    {
      replace (val_r_out_2 + UINT_MOD ^ an) with
        (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
      replace (an + 1) with (Z.max an bn + 1) by (rewrite Z.max_l; lia).
      eapply is_compact_Z_add_1; eauto.
      - rewrite Z.max_l by lia.
        lia.
      - rewrite Z.max_l by lia.
        lia.
    }
    Right.
    Exists val_r_out_2.
    Exists rcap_new_2.
    subst a.
    sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) bn).
    entailer!.
    all: try lia; try assumption.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_7_rp_eq_bp : mpz_abs_add_entail_wit_7_rp_eq_bp.
Proof.
  pre_process.
  prop_apply (mpn_add_ret_0_or_1_compact
    rptr_new (Zabs zb_r_eq_a) (Zabs za_r_eq_a) val_r_out_2 an bn retval
    PreH14 ltac:(lia) PreH16 PreH15).
  Intros.
  prop_apply (mpd_store_Z_bound rptr_new val_r_out_2 an).
  Intros.
  match goal with
  | Hb : 0 <= val_r_out_2 < UINT_MOD ^ an |- _ =>
      pose proof Hb as Hval_bound
  end.
  match goal with
  | Hret : retval = 0 \/ retval = 1 |- _ => destruct Hret as [Hret | Hret]; subst retval
  end.
  - assert (Hcompact: is_compact_Z UINT_MOD val_r_out_2 an).
    {
      replace val_r_out_2 with (Zabs zb_r_eq_a + Zabs za_r_eq_a) by lia.
      replace an with (Z.max an bn) by (rewrite Z.max_l; lia).
      eapply is_compact_Z_add_0; eauto.
      rewrite Z.max_l by lia.
      lia.
    }
    Left.
    Exists val_r_out_2.
    Exists rcap_new_2.
    sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) an).
    entailer!.
    all: try lia; try assumption.
  - assert (Hcompact: is_compact_Z UINT_MOD (val_r_out_2 + UINT_MOD ^ an) (an + 1)).
    {
      replace (val_r_out_2 + UINT_MOD ^ an) with
        (Zabs zb_r_eq_a + Zabs za_r_eq_a) by lia.
      replace (an + 1) with (Z.max an bn + 1) by (rewrite Z.max_l; lia).
      eapply is_compact_Z_add_1; eauto.
      - rewrite Z.max_l by lia.
        lia.
      - rewrite Z.max_l by lia.
        lia.
    }
    Right.
    Exists val_r_out_2.
    Exists rcap_new_2.
    sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) an).
    entailer!.
    all: try lia; try assumption.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_1_rp_eq_bp : mpz_abs_add_return_wit_1_rp_eq_bp.
Proof.
  pre_process.
  assert (Hsize_ret:
    signed_last_nbits (unsigned_last_nbits an 32 + cy) 32 = an).
  {
    subst cy.
    pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos val_r_out an PreH18)
      as [Han_nonneg _].
    assert (Han_u32 : 0 <= an < 2 ^ 32)
      by (change (2 ^ 32) with 4294967296; lia).
    assert (Han_s32 : - 2 ^ (32 - 1) <= an < 2 ^ (32 - 1))
      by (change (2 ^ (32 - 1)) with 2147483648; lia).
    rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
    replace (an + 0) with an by lia.
    rewrite signed_last_nbits_eq.
    2:{ lia. }
    2:{ exact Han_s32. }
    lia.
  }
  subst cy.
  subst b.
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Exists rptr_new rsize rcap_new.
  Exists bptr bsize bcap.
  rewrite Hsize_ret.
  replace (Zabs an) with an by lia.
  replace (Zabs bsize) with an by lia.
  replace (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  replace (Zabs za_r_eq_a + Zabs zb_r_eq_a) with val_r_out by lia.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact rptr_new val_r_out an).
  sep_apply (store_uint_undef_store_uint (rptr_new + an * sizeof(UINT)) 0).
  sep_apply (UIntArray.undef_seg_single rptr_new an).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg.
  entailer!.
  all: try assumption; try (unfold same_sign; left; lia); lia.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_2_rp_eq_bp : mpz_abs_add_return_wit_2_rp_eq_bp.
Proof.
  pre_process.
  assert (Hsize_ret:
    signed_last_nbits (unsigned_last_nbits an 32 + cy) 32 = an + 1).
  {
    subst cy.
    assert (Han_u32 : 0 <= an < 2 ^ 32)
      by (change (2 ^ 32) with 4294967296; lia).
    assert (Han1_s32 : - 2 ^ (32 - 1) <= an + 1 < 2 ^ (32 - 1))
      by (change (2 ^ (32 - 1)) with 2147483648; lia).
    rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
    rewrite signed_last_nbits_eq.
    2:{ lia. }
    2:{ exact Han1_s32. }
    lia.
  }
  subst cy.
  subst b.
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Exists rptr_new rsize rcap_new.
  Exists bptr bsize bcap.
  rewrite Hsize_ret.
  replace (Zabs (an + 1)) with (an + 1) by lia.
  replace (Zabs bsize) with an by lia.
  replace (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  sep_apply (mpd_store_Z_append_one_compact rptr_new val_r_out an).
  replace (val_r_out + UINT_MOD ^ an) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  entailer!.
  all: try assumption; try (unfold same_sign; left; lia); lia.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_3_rp_eq_ap : mpz_abs_add_return_wit_3_rp_eq_ap.
Proof.
  pre_process.
  assert (Hsize_ret:
    signed_last_nbits (unsigned_last_nbits an 32 + cy) 32 = an).
  {
    subst cy.
    assert (Han_u32 : 0 <= an < 2 ^ 32)
      by (change (2 ^ 32) with 4294967296; lia).
    assert (Han_s32 : - 2 ^ (32 - 1) <= an < 2 ^ (32 - 1))
      by (change (2 ^ (32 - 1)) with 2147483648; lia).
    rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
    replace (an + 0) with an by lia.
    rewrite signed_last_nbits_eq.
    2:{ lia. }
    2:{ exact Han_s32. }
    lia.
  }
  subst cy.
  subst a.
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Exists rptr_new rsize rcap_new.
  Exists bptr bsize bcap.
  rewrite Hsize_ret.
  replace (Zabs an) with an by lia.
  replace (Zabs bsize) with bn by lia.
  replace (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  replace (Zabs za_r_eq_a + Zabs zb_r_eq_a) with val_r_out by lia.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact rptr_new val_r_out an).
  sep_apply (store_uint_undef_store_uint (rptr_new + an * sizeof(UINT)) 0).
  sep_apply (UIntArray.undef_seg_single rptr_new an).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg.
  entailer!.
  all: try assumption; try (unfold same_sign; left; lia); lia.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_4_rp_eq_ap : mpz_abs_add_return_wit_4_rp_eq_ap.
Proof.
  pre_process.
  assert (Hsize_ret:
    signed_last_nbits (unsigned_last_nbits an 32 + cy) 32 = an + 1).
  {
    subst cy.
    assert (Han_u32 : 0 <= an < 2 ^ 32)
      by (change (2 ^ 32) with 4294967296; lia).
    assert (Han1_s32 : - 2 ^ (32 - 1) <= an + 1 < 2 ^ (32 - 1))
      by (change (2 ^ (32 - 1)) with 2147483648; lia).
    rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
    rewrite signed_last_nbits_eq.
    2:{ lia. }
    2:{ exact Han1_s32. }
    lia.
  }
  subst cy.
  subst a.
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Exists rptr_new rsize rcap_new.
  Exists bptr bsize bcap.
  rewrite Hsize_ret.
  replace (Zabs (an + 1)) with (an + 1) by lia.
  replace (Zabs bsize) with bn by lia.
  replace (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  sep_apply (mpd_store_Z_append_one_compact rptr_new val_r_out an).
  replace (val_r_out + UINT_MOD ^ an) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  entailer!.
  all: try assumption; try (unfold same_sign; left; lia); lia.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_5_pure : mpz_abs_add_partial_solve_wit_5_pure.
Proof.
  pre_process.
  prop_apply (mpd_store_Z_compact_range UINT_MOD bptr (Zabs zb_r_eq_a) (Zabs bsize)).
  Intros.
  change Int.max_unsigned with 4294967295 in *.
  assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.
  rewrite Hcalc in *.
  entailer!.
  all: lia.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_6_pure : mpz_abs_add_partial_solve_wit_6_pure.
Proof.
  pre_process.
  prop_apply (mpd_store_Z_compact_range UINT_MOD rptr (Zabs za_r_eq_a) (Zabs rsize)).
  Intros.
  change Int.max_unsigned with 4294967295 in *.
  assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.
  rewrite Hcalc in *.
  entailer!.
  all: lia.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_7_rp_eq_bp_pure : mpz_abs_add_partial_solve_wit_7_rp_eq_bp_pure.
Proof. pre_process. Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_9_rp_eq_ap_pure : mpz_abs_add_partial_solve_wit_9_rp_eq_ap_pure.
Proof. pre_process. Qed.
