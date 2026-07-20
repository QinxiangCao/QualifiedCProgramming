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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_1_invert_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_1_invert_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_div_qr_1_invert_entail_wit_1 : mpn_div_qr_1_invert_entail_wit_1.
Proof.
  unfold mpn_div_qr_1_invert_entail_wit_1.
  left.
  intros.
  unfold div_inverse_slot.
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_1_invert_return_wit_1 : mpn_div_qr_1_invert_return_wit_1.
Proof.
  unfold mpn_div_qr_1_invert_return_wit_1.
  left.
  intros.
  assert (Hbits:
    unsigned_last_nbits (Z.shiftl d_pre shift) 32 =
    d_pre * Z.pow 2 shift).
  {
    rewrite Z.shiftl_mul_pow2 by lia.
    apply unsigned_last_nbits_eq.
    lia.
  }
  unfold store_div_inverse, div_inverse_store.
  Exists shift (unsigned_last_nbits (Z.shiftl d_pre shift) 32) 0 retval.
  split_pure_spatial.
  - destruct (Z.eq_dec 1 1) as [_|Hneq]; [|congruence].
    entailer!.
  - dump_pre_spatial.
    unfold gmp_div_inverse_valid, div_inverse_den.
    rewrite Hbits in *.
    destruct (Z.eq_dec 1 1) as [_|Hneq]; [|congruence].
    change (UINT_MOD ^ 1) with UINT_MOD.
    change UINT_MOD with (2 ^ 32).
    change (UINT_MOD / 2) with 2147483648.
    change (Z.pow 2 31) with 2147483648 in PreH9.
    change (Z.pow 2 32) with 4294967296 in PreH10.
    repeat split.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact PreH10.
    + left. split; [reflexivity|reflexivity].
    + exact PreH9.
    + replace ((retval + 2 ^ 32) * (2 ^ 32 * (d_pre * 2 ^ shift))) with
        ((retval + UINT_MOD) * (UINT_MOD * (d_pre * 2 ^ shift) + 0))
        by (unfold UINT_MOD; ring).
      replace ((2 ^ 32) ^ 3 - 1) with (UINT_MOD ^ 3 - 1)
        by (unfold UINT_MOD; reflexivity).
      exact PreH3.
    + replace ((2 ^ 32) ^ 3 - 1) with (UINT_MOD ^ 3 - 1)
        by (unfold UINT_MOD; reflexivity).
      replace ((retval + 2 ^ 32 + 1) * (2 ^ 32 * (d_pre * 2 ^ shift))) with
        ((retval + UINT_MOD + 1) * (UINT_MOD * (d_pre * 2 ^ shift) + 0))
        by (unfold UINT_MOD; ring).
      exact PreH4.
Qed.

Lemma proof_of_mpn_div_qr_1_invert_partial_solve_wit_2_pure : mpn_div_qr_1_invert_partial_solve_wit_2_pure.
Proof.
  unfold mpn_div_qr_1_invert_partial_solve_wit_2_pure.
  left.
  intros.
  assert (Hbits:
    unsigned_last_nbits (Z.shiftl d_pre shift) 32 =
    d_pre * Z.pow 2 shift).
  {
    rewrite Z.shiftl_mul_pow2 by lia.
    apply unsigned_last_nbits_eq.
    lia.
  }
  entailer!.
  rewrite Hbits.
  change (UINT_MOD ÷ 2) with 2147483648.
  change (Z.pow 2 31) with 2147483648 in PreH5.
  change (Z.pow 2 32) with 4294967296 in PreH6.
  lia.
Qed.
