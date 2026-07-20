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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_udiv_qr_3by2_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_udiv_qr_3by2_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.
Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_9_1 : gmp_udiv_qr_3by2_entail_wit_9_1.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_9_1.
  left.
  intros.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  assert (Hlow: unsigned_last_nbits (rmid0 - d0_pre) 32 = rmid0 - d0_pre).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  assert (HNlt: n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre <
                 (d1_pre * 4294967296 + d0_pre) * 4294967296).
  { assert (n2_pre * 4294967296 + n1_pre <=
            d1_pre * 4294967296 + d0_pre - 1) by abstract lia.
    nia. }
  assert (HRgeD: d1_pre * 4294967296 + d0_pre <= rmid1 * 4294967296 + rmid0) by nia.
  assert (Hq_lt: qmid < 4294967295).
  { destruct (Z_lt_ge_dec qmid 4294967295) as [Hlt | Hge]; [exact Hlt |].
    assert (qmid = 4294967295) by abstract lia.
    subst qmid.
    rewrite PreH24 in HNlt.
    nia. }
  assert (Hq: unsigned_last_nbits (qmid + 1) 32 = qmid + 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  assert (Hrem: ((rmid1 - d1_pre) - 0) * 4294967296 + (rmid0 - d0_pre) =
                (rmid1 * 4294967296 + rmid0) - (d1_pre * 4294967296 + d0_pre)) by abstract ring.
  assert (Hupdate:
    n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre =
    unsigned_last_nbits (qmid + 1) 32 * (d1_pre * 4294967296 + d0_pre) +
      ((rmid1 - d1_pre) - 0) * 4294967296 +
      unsigned_last_nbits (rmid0 - d0_pre) 32).
  { rewrite Hq, Hlow, PreH24. ring. }
  assert (Hres:
    ((rmid1 - d1_pre) - 0) * 4294967296 +
      unsigned_last_nbits (rmid0 - d0_pre) 32 <
    d1_pre * 4294967296 + d0_pre).
  { rewrite Hlow, Hrem. lia. }
  assert (Hlow_hi: unsigned_last_nbits (rmid0 - d0_pre) 32 <= 4294967295) by (rewrite Hlow; lia).
  assert (Hlow_lo: 0 <= unsigned_last_nbits (rmid0 - d0_pre) 32) by (rewrite Hlow; lia).
  assert (Hhi_hi: (rmid1 - d1_pre) - 0 <= 4294967295) by abstract lia.
  assert (Hq_hi: unsigned_last_nbits (qmid + 1) 32 <= 4294967295) by (rewrite Hq; lia).
  assert (Hq_lo: 0 <= unsigned_last_nbits (qmid + 1) 32) by (rewrite Hq; lia).
  clear PreH24 HNlt HRgeD Hq_lt Hrem.
  split_pure_spatial.
  2: split_pures.
  all: try (dump_pre_spatial; change UINT_MOD with 4294967296 in *;
            first [ exact Hupdate
                  | exact Hres
                  | exact Hlow_hi
                  | exact Hlow_lo
                  | exact Hhi_hi
                  | exact Hq_hi
                  | exact Hq_lo
                  | lia ]).
  all: cancel.
  1: apply store_uint_undef_store_uint.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_9_2 : gmp_udiv_qr_3by2_entail_wit_9_2.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_9_2.
  left.
  intros.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  assert (Hlow: unsigned_last_nbits (rmid0 - d0_pre) 32 =
                rmid0 - d0_pre + 4294967296).
  { replace (rmid0 - d0_pre) with
      ((rmid0 - d0_pre + 4294967296) - 4294967296) by ring.
    rewrite unsigned_last_nbits_underflow_32 by lia.
    ring. }
  set (D := d1_pre * 4294967296 + d0_pre).
  set (R := rmid1 * 4294967296 + rmid0).
  assert (HNlt: n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre <
                 D * 4294967296).
  { subst D.
    assert (n2_pre * 4294967296 + n1_pre <=
            d1_pre * 4294967296 + d0_pre - 1) by lia.
    nia. }
  assert (HRgeD: D <= R).
  { subst D R. lia. }
  assert (Hq_lt: qmid < 4294967295).
  { destruct (Z_lt_ge_dec qmid 4294967295) as [Hlt | Hge]; [exact Hlt |].
    assert (qmid = 4294967295) by lia.
    subst qmid.
    fold D R in PreH24.
    nia. }
  assert (Hq: unsigned_last_nbits (qmid + 1) 32 = qmid + 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  assert (Hrem_eq: ((rmid1 - d1_pre) - 1) * 4294967296 +
                     unsigned_last_nbits (rmid0 - d0_pre) 32 = R - D).
  { rewrite Hlow. subst D R. ring. }
  assert (Hupdate:
    n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre =
      unsigned_last_nbits (qmid + 1) 32 * D +
      ((rmid1 - d1_pre) - 1) * 4294967296 +
      unsigned_last_nbits (rmid0 - d0_pre) 32).
  { rewrite Hq.
    replace ((qmid + 1) * D + ((rmid1 - d1_pre) - 1) * 4294967296 +
               unsigned_last_nbits (rmid0 - d0_pre) 32)
      with (qmid * D + R) by (rewrite Hlow; subst D R; ring).
    fold D R in PreH24.
    subst R.
    replace (qmid * D + (rmid1 * 4294967296 + rmid0))
      with (qmid * D + rmid1 * 4294967296 + rmid0) by ring.
    exact PreH24. }
  assert (Hres:
    ((rmid1 - d1_pre) - 1) * 4294967296 +
      unsigned_last_nbits (rmid0 - d0_pre) 32 < D).
  { replace (((rmid1 - d1_pre) - 1) * 4294967296 +
               unsigned_last_nbits (rmid0 - d0_pre) 32)
      with (R - D) by (rewrite <- Hrem_eq; ring).
    lia. }
  split_pure_spatial.
  2: split_pures.
  all: try (dump_pre_spatial; change UINT_MOD with 4294967296 in *;
            rewrite ?Hq, ?Hlow; fold D; first [exact Hupdate | exact Hres | lia]).
  all: cancel.
  1: apply store_uint_undef_store_uint.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_9_3 : gmp_udiv_qr_3by2_entail_wit_9_3.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_9_3.
  left.
  intros.
  split_pure_spatial.
  2: split_pures.
  all: try (dump_pre_spatial; change UINT_MOD with 4294967296 in *;
            try rewrite unsigned_last_nbits_eq by lia; lia).
  all: cancel.
  1: apply store_uint_undef_store_uint.
  - dump_pre_spatial.
    pose proof (unsigned_Lastnbits_range (qmid + 1) 32 ltac:(lia)) as Hr.
    change (2 ^ 32) with 4294967296 in Hr.
    lia.
  - dump_pre_spatial.
    pose proof (unsigned_Lastnbits_range (qmid + 1) 32 ltac:(lia)) as Hr.
    change (2 ^ 32) with 4294967296 in Hr.
    lia.
  - dump_pre_spatial.
    change UINT_MOD with 4294967296 in *.
    assert (HDpos: 0 < d1_pre * 4294967296 + d0_pre) by nia.
    assert (HNlt: n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre <
                   (d1_pre * 4294967296 + d0_pre) * 4294967296) by nia.
    assert (HRgeD: d1_pre * 4294967296 + d0_pre <= rmid1 * 4294967296 + rmid0) by nia.
    assert (Hq_lt: qmid < 4294967295) by nia.
    rewrite unsigned_last_nbits_eq by abstract lia.
    nia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_9_4 : gmp_udiv_qr_3by2_entail_wit_9_4.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_9_4.
  left.
  intros.
  split_pure_spatial.
  2: split_pures.
  all: try (dump_pre_spatial; change UINT_MOD with 4294967296 in *;
            try rewrite unsigned_last_nbits_eq by lia; lia).
  all: cancel.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_9_5 : gmp_udiv_qr_3by2_entail_wit_9_5.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_9_5.
  left.
  intros.
  split_pure_spatial.
  2: split_pures.
  all: try (dump_pre_spatial; change UINT_MOD with 4294967296 in *;
            try rewrite unsigned_last_nbits_eq by lia; lia).
  all: cancel.
Qed.
