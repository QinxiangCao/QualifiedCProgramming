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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_2_invert_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_2_invert_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_div_qr_2_invert_entail_wit_1 : mpn_div_qr_2_invert_entail_wit_1.
Proof.
  unfold mpn_div_qr_2_invert_entail_wit_1.
  left.
  intros.
  unfold div_inverse_slot.
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_2_invert_entail_wit_2_1 : mpn_div_qr_2_invert_entail_wit_2_1.
Proof.
  unfold mpn_div_qr_2_invert_entail_wit_2_1.
  right.
  intros.
  entailer!.
  - assert (Hlow_bound: 0 <= d0_pre < UINT_MOD) by (unfold UINT_MOD; lia).
    assert (Hshift_bound: 1 <= shift < 32) by lia.
    pose proof (mpn_lshift_lor_add d1_pre d0_pre shift Hlow_bound Hshift_bound) as Hlor.
    replace (unsigned_last_nbits (d1_pre * 2 ^ shift) 32)
      with (unsigned_last_nbits (Z.shiftl d1_pre shift) 32) in Hlor.
    2: { rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
    assert (Hd1bits:
      unsigned_last_nbits (Z.shiftl d1_pre shift) 32 =
        d1_pre * 2 ^ shift).
    {
      rewrite Z.shiftl_mul_pow2 by lia.
      apply unsigned_last_nbits_eq.
      lia.
    }
    pose proof (mpn_lshift_limb_decompose d0_pre shift Hlow_bound Hshift_bound) as Hdec.
    rewrite Hlor, Hd1bits.
    replace ((d1_pre * UINT_MOD + d0_pre) * 2 ^ shift) with
      (d1_pre * 2 ^ shift * UINT_MOD + d0_pre * 2 ^ shift) by ring.
    rewrite <- Hdec.
    ring.
  - assert (Hlow_bound: 0 <= d0_pre < UINT_MOD) by (unfold UINT_MOD; lia).
    assert (Hshift_bound: 1 <= shift < 32) by lia.
    pose proof (mpn_lshift_lor_add d1_pre d0_pre shift Hlow_bound Hshift_bound) as Hlor.
    replace (unsigned_last_nbits (d1_pre * 2 ^ shift) 32)
      with (unsigned_last_nbits (Z.shiftl d1_pre shift) 32) in Hlor.
    2: { rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
    assert (Hd1bits:
      unsigned_last_nbits (Z.shiftl d1_pre shift) 32 =
        d1_pre * 2 ^ shift).
    {
      rewrite Z.shiftl_mul_pow2 by lia.
      apply unsigned_last_nbits_eq.
      lia.
    }
    rewrite Hlor, Hd1bits.
    change (Z.quot UINT_MOD 2) with (2 ^ 31).
    eapply Z.le_trans; [exact PreH8|].
    assert (Hsh: 0 <= Z.shiftr d0_pre (32 - shift)).
    {
      rewrite Z.shiftr_div_pow2 by lia.
      apply Z.div_pos; lia.
    }
    lia.
  - pose proof (mpn_lshift_join_limb_bound
      (unsigned_last_nbits (d1_pre * 2 ^ shift) 32)
      d0_pre d1_pre shift ltac:(lia) ltac:(lia) ltac:(reflexivity)) as Hrange.
    replace (unsigned_last_nbits (d1_pre * 2 ^ shift) 32)
      with (unsigned_last_nbits (Z.shiftl d1_pre shift) 32) in Hrange.
    2: { rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
    change UINT_MOD with 4294967296 in Hrange.
    lia.
  - pose proof (unsigned_Lastnbits_range (Z.shiftl d0_pre shift) 32 ltac:(lia)) as Hrange.
    lia.
  - pose proof (unsigned_Lastnbits_range (Z.shiftl d0_pre shift) 32 ltac:(lia)) as Hrange.
    lia.
Qed.

Lemma proof_of_mpn_div_qr_2_invert_entail_wit_2_2 : mpn_div_qr_2_invert_entail_wit_2_2.
Proof.
  unfold mpn_div_qr_2_invert_entail_wit_2_2.
  right.
  intros.
  assert (Hshift0: shift = 0) by lia.
  subst shift.
  entailer!.
  - change (Z.quot UINT_MOD 2) with (2 ^ 31).
    change (2 ^ 0) with 1 in PreH8.
    replace (d1_pre * 1) with d1_pre in PreH8 by ring.
    exact PreH8.
Qed.

Lemma proof_of_mpn_div_qr_2_invert_return_wit_1 : mpn_div_qr_2_invert_return_wit_1.
Proof.
  unfold mpn_div_qr_2_invert_return_wit_1.
  left.
  intros.
  subst inv_shift.
  unfold store_div_inverse, div_inverse_store.
  Exists shift nd1 nd0 retval.
  split_pure_spatial.
  - destruct (Z.eq_dec 2 1) as [Heq|_]; [lia|].
    entailer!.
  - dump_pre_spatial.
    unfold gmp_div_inverse_valid, div_inverse_den.
    destruct (Z.eq_dec 2 1) as [Heq|_]; [lia|].
    change (UINT_MOD ^ (2 - 2)) with 1.
    repeat split.
    + lia.
    + lia.
    + assert (Hprod_pos: 0 < (d1_pre * UINT_MOD + d0_pre) * 2 ^ shift).
      {
        rewrite <- PreH9.
        unfold UINT_MOD in *.
        change (Z.quot UINT_MOD 2) with 2147483648 in PreH10.
        nia.
      }
      assert (Hpow_pos: 0 < 2 ^ shift) by (apply Z.pow_pos_nonneg; lia).
      nia.
    + exact PreH5.
    + exact PreH6.
    + change (Z.quot UINT_MOD 2) with 2147483648 in PreH10.
      lia.
    + exact PreH11.
    + exact PreH12.
    + exact PreH13.
    + exact PreH1.
    + exact PreH2.
    + rewrite <- PreH9.
      change (UINT_MOD ^ 2) with (UINT_MOD * UINT_MOD).
      unfold UINT_MOD in *.
      change (Z.quot UINT_MOD 2) with 2147483648 in PreH10.
      nia.
    + right.
      split; [lia|].
      rewrite Z.div_1_r.
      exact PreH9.
    + exact PreH10.
    + replace (nd1 * UINT_MOD + nd0) with (UINT_MOD * nd1 + nd0) by ring.
      exact PreH3.
    + replace (nd1 * UINT_MOD + nd0) with (UINT_MOD * nd1 + nd0) by ring.
      exact PreH4.
Qed.
