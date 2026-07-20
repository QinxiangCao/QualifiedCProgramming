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
Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_1 : gmp_udiv_qr_3by2_entail_wit_8_1.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_8_1.
  left.
  intros.
  subst m.
  replace (Z.land 0 d0_pre) with 0 by reflexivity.
  replace (Z.land 0 d1_pre) with 0 by reflexivity.
  repeat rewrite Z.add_0_r.
  repeat rewrite Z.add_0_l.
  repeat rewrite unsigned_revolutive by abstract lia.
  repeat rewrite unsigned_last_nbits_eq by
    (change (2 ^ 32) with 4294967296; lia).
  split_pure_spatial.
  2: {
    split_pures.
    all: try (dump_pre_spatial; change UINT_MOD with 4294967296 in *;
              change (4294967296 ÷ 2) with 2147483648 in *;
              first [ reflexivity
                    | exact PreH1 | exact PreH2 | exact PreH3 | exact PreH4 | exact PreH5 | exact PreH6 |
                      exact PreH7 | exact PreH8 | exact PreH9 | exact PreH10 |
                      exact PreH11 | exact PreH12 | exact PreH13 | exact PreH14 |
                      exact PreH15 | exact PreH16 | exact PreH17 | exact PreH18 | exact PreH19 | exact PreH20 |
                      exact PreH21 | exact PreH22 | exact PreH23 | exact PreH24 |
                      exact PreH25 | exact PreH26 | exact PreH27 | exact PreH28 |
                      exact PreH29 | exact PreH30
                    | lia ]).
  }
  all: try cancel.
  sep_apply store_uint_undef_store_uint.
  sep_apply store_uint_undef_store_uint.
  sep_apply store_uint_undef_store_uint.
  cancel.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_2 : gmp_udiv_qr_3by2_entail_wit_8_2.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_8_2.
  left.
  intros.
  subst m.
  replace (Z.land 0 d0_pre) with 0 in PreH1 by reflexivity.
  rewrite Z.add_0_r in PreH1.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change (2 ^ 32) with 4294967296; lia).
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_3 : gmp_udiv_qr_3by2_entail_wit_8_3.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_8_3.
  right.
  intros.
  subst m qpre qext.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  assert (Hland0: Z.land 4294967295 d0_pre = d0_pre).
  { rewrite Z.land_comm.
    change 4294967295 with (Z.ones 32).
    rewrite Z.land_ones by abstract lia.
    rewrite Z.mod_small by abstract lia.
    reflexivity. }
  assert (Hland1: Z.land 4294967295 d1_pre = d1_pre).
  { rewrite Z.land_comm.
    change 4294967295 with (Z.ones 32).
    rewrite Z.land_ones by abstract lia.
    rewrite Z.mod_small by abstract lia.
    reflexivity. }
  assert (Hlow_lt: rpre0 + d0_pre < 4294967296).
  { destruct (Z_lt_ge_dec (rpre0 + d0_pre) 4294967296) as [Hlt | Hge]; [exact Hlt |].
    rewrite Hland0 in PreH1.
    assert (Hbig: unsigned_last_nbits (rpre0 + d0_pre) 32 =
                  rpre0 + d0_pre - 4294967296).
    { apply unsigned_last_nbits_overflow_32. lia. }
    rewrite Hbig in PreH1.
    lia. }
  assert (Hlow: unsigned_last_nbits (rpre0 + Z.land 4294967295 d0_pre) 32 =
                rpre0 + d0_pre).
  { rewrite Hland0. apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296. lia. }
  replace (4294967296 ^ 2) with (4294967296 * 4294967296) in PreH28 by reflexivity.
  assert (Hhi_ge: 4294967296 <= rpre1 + d1_pre) by abstract lia.
  assert (Hhi: unsigned_last_nbits
                 (unsigned_last_nbits (rpre1 + Z.land 4294967295 d1_pre) 32 + 0) 32 =
               rpre1 + d1_pre - 4294967296).
  { rewrite Hland1.
    assert (Hinner_range: 4294967296 <= rpre1 + d1_pre < 2 * 4294967296) by abstract lia.
    rewrite (unsigned_last_nbits_overflow_32 (rpre1 + d1_pre) Hinner_range).
    rewrite Z.add_0_r.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  split_pure_spatial.
  1: entailer!.
  split_pures.
  - dump_pre_spatial.
    rewrite Hhi, Hlow.
    change (0 + 4294967295) with 4294967295.
    replace (4294967295 * (d1_pre * 4294967296 + d0_pre) +
             (rpre1 + d1_pre - 4294967296) * 4294967296 +
             (rpre0 + d0_pre))
      with (4294967296 * (d1_pre * 4294967296 + d0_pre) +
            rpre1 * 4294967296 + rpre0 - 4294967296 ^ 2) by abstract ring.
    rewrite <- PreH29.
    ring.
  - dump_pre_spatial.
    rewrite Hhi, Hlow.
    assert (Hrem_lt_B2:
      (rpre1 + d1_pre - 4294967296) * 4294967296 + (rpre0 + d0_pre) <
      4294967296 ^ 2).
    { change (4294967296 ^ 2) with (4294967296 * 4294967296).
      lia. }
    assert (HB2_le_2D:
      4294967296 ^ 2 <= 2 * (d1_pre * 4294967296 + d0_pre)).
    { change (4294967296 ÷ 2) with 2147483648 in PreH11.
      change (4294967296 ^ 2) with (4294967296 * 4294967296).
      lia. }
    lia.
  - dump_pre_spatial. rewrite Hlow. lia.
  - dump_pre_spatial. rewrite Hhi. lia.
  - dump_pre_spatial. rewrite Hhi. lia.
Qed.
