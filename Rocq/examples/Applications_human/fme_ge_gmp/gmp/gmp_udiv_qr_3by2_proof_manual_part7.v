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
Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_1 :
  gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  assert (Hlow_ge: 4294967296 <= rpre0 + d0_pre).
  { destruct (Z_lt_ge_dec (rpre0 + d0_pre) 4294967296) as [Hlt | Hge].
    - rewrite Hland0 in PreH1.
      assert (Hsmall: unsigned_last_nbits (rpre0 + d0_pre) 32 = rpre0 + d0_pre).
      { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296.
        split; [apply Z.add_nonneg_nonneg; [exact PreH23 | exact PreH13] | exact Hlt]. }
      rewrite Hsmall in PreH1.
      nia.
    - apply Z.ge_le in Hge. exact Hge. }
  assert (Hlow: unsigned_last_nbits (rpre0 + Z.land 4294967295 d0_pre) 32 =
                rpre0 + d0_pre - 4294967296).
  { rewrite Hland0. apply unsigned_last_nbits_overflow_32. nia. }
  assert (Hhi_ge: 4294967296 <= rpre1 + d1_pre + 1) by nia.
  assert (Hhi: unsigned_last_nbits
                 (unsigned_last_nbits (rpre1 + Z.land 4294967295 d1_pre) 32 + 1) 32 =
               rpre1 + d1_pre + 1 - 4294967296).
  { rewrite Hland1.
    destruct (Z_le_gt_dec 4294967296 (rpre1 + d1_pre)) as [Hov | Hno].
    - assert (Hinner_range: 4294967296 <= rpre1 + d1_pre < 2 * 4294967296) by abstract lia.
      rewrite (unsigned_last_nbits_overflow_32 (rpre1 + d1_pre) Hinner_range).
      assert (Houter_range: 0 <= rpre1 + d1_pre - 4294967296 + 1 < 4294967296) by abstract lia.
      rewrite (unsigned_last_nbits_eq (rpre1 + d1_pre - 4294967296 + 1) 32)
        by (change (2 ^ 32) with 4294967296; exact Houter_range).
      ring.
    - assert (Hinner_range: 0 <= rpre1 + d1_pre < 2 ^ 32).
      { change (2 ^ 32) with 4294967296. lia. }
      rewrite (unsigned_last_nbits_eq (rpre1 + d1_pre) 32 Hinner_range).
      assert (Heq: rpre1 + d1_pre + 1 = 4294967296) by abstract lia.
      rewrite Heq.
      assert (Houter_range: 4294967296 <= 4294967296 < 2 * 4294967296) by abstract lia.
      rewrite (unsigned_last_nbits_overflow_32 4294967296 Houter_range).
      ring. }
  rewrite Hhi, Hlow.
  change (0 + 4294967295) with 4294967295.
  replace (4294967295 * (d1_pre * 4294967296 + d0_pre) +
           (rpre1 + d1_pre + 1 - 4294967296) * 4294967296 +
           (rpre0 + d0_pre - 4294967296))
    with (4294967296 * (d1_pre * 4294967296 + d0_pre) +
          rpre1 * 4294967296 + rpre0 - 4294967296 ^ 2) by abstract ring.
  rewrite <- PreH29.
  ring.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_2 :
  gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  assert (Hlow_ge: 4294967296 <= rpre0 + d0_pre).
  { destruct (Z_lt_ge_dec (rpre0 + d0_pre) 4294967296) as [Hlt | Hge].
    - rewrite Hland0 in PreH1.
      assert (Hsmall: unsigned_last_nbits (rpre0 + d0_pre) 32 =
                      rpre0 + d0_pre).
      { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296.
        split; [apply Z.add_nonneg_nonneg; [exact PreH23 | exact PreH13] |
                exact Hlt]. }
      rewrite Hsmall in PreH1.
      nia.
    - apply Z.ge_le in Hge. exact Hge. }
  assert (Hlow: unsigned_last_nbits
                 (rpre0 + Z.land 4294967295 d0_pre) 32 =
               rpre0 + d0_pre - 4294967296).
  { rewrite Hland0. apply unsigned_last_nbits_overflow_32. nia. }
  assert (Hhi_ge: 4294967296 <= rpre1 + d1_pre + 1) by nia.
  assert (Hhi: unsigned_last_nbits
                 (unsigned_last_nbits
                    (rpre1 + Z.land 4294967295 d1_pre) 32 + 1) 32 =
               rpre1 + d1_pre + 1 - 4294967296).
  { rewrite Hland1.
    destruct (Z_le_gt_dec 4294967296 (rpre1 + d1_pre)) as [Hov | Hno].
    - assert (Hinner_range:
        4294967296 <= rpre1 + d1_pre < 2 * 4294967296) by abstract lia.
      rewrite (unsigned_last_nbits_overflow_32
        (rpre1 + d1_pre) Hinner_range).
      assert (Houter_range:
        0 <= rpre1 + d1_pre - 4294967296 + 1 < 4294967296)
        by abstract lia.
      rewrite (unsigned_last_nbits_eq
        (rpre1 + d1_pre - 4294967296 + 1) 32)
        by (change (2 ^ 32) with 4294967296; exact Houter_range).
      ring.
    - assert (Hinner_range: 0 <= rpre1 + d1_pre < 2 ^ 32).
      { change (2 ^ 32) with 4294967296. lia. }
      rewrite (unsigned_last_nbits_eq
        (rpre1 + d1_pre) 32 Hinner_range).
      assert (Heq: rpre1 + d1_pre + 1 = 4294967296) by abstract lia.
      rewrite Heq.
      assert (Houter_range:
        4294967296 <= 4294967296 < 2 * 4294967296) by abstract lia.
      rewrite (unsigned_last_nbits_overflow_32 4294967296 Houter_range).
      ring. }
  rewrite Hhi, Hlow.
  nia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_3 :
  gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst m.
  pose proof (unsigned_Lastnbits_range (rpre0 + Z.land UINT_MAX d0_pre) 32 ltac:(lia))
    as Hrange.
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_4 :
  gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst m.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (rpre1 + Z.land UINT_MAX d1_pre) 32 + 1) 32 ltac:(lia))
    as Hrange.
  change UINT_MAX with 4294967295.
  change (2 ^ 32) with 4294967296 in Hrange.
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_5 :
  gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst m.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (rpre1 + Z.land UINT_MAX d1_pre) 32 + 1) 32 ltac:(lia))
    as Hrange.
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_4 :
  gmp_udiv_qr_3by2_entail_wit_8_4.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_1.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_2.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_3.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_4.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_5.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_1 :
  gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  assert (Hhi_lt: rpre1 + d1_pre < 4294967296).
  { apply (Zmult_lt_reg_r _ _ 4294967296); [lia |].
    nia. }
  assert (Hhi: unsigned_last_nbits
                 (unsigned_last_nbits (rpre1 + Z.land 4294967295 d1_pre) 32 + 0) 32 =
               rpre1 + d1_pre).
  { rewrite Hland1, Z.add_0_r.
    assert (Hinner: unsigned_last_nbits (rpre1 + d1_pre) 32 = rpre1 + d1_pre).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite Hinner.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  rewrite Hhi, Hlow.
  change (0 + 4294967295) with 4294967295.
  replace (4294967295 * (d1_pre * 4294967296 + d0_pre) +
           (rpre1 + d1_pre) * 4294967296 +
           (rpre0 + d0_pre))
    with (4294967296 * (d1_pre * 4294967296 + d0_pre) +
          rpre1 * 4294967296 + rpre0) by abstract ring.
  reflexivity.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_2 :
  gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  { destruct (Z_lt_ge_dec (rpre0 + d0_pre) 4294967296) as [Hlt | Hge];
      [exact Hlt |].
    rewrite Hland0 in PreH1.
    assert (Hbig: unsigned_last_nbits (rpre0 + d0_pre) 32 =
                  rpre0 + d0_pre - 4294967296).
    { apply unsigned_last_nbits_overflow_32. lia. }
    rewrite Hbig in PreH1.
    lia. }
  assert (Hlow: unsigned_last_nbits
                 (rpre0 + Z.land 4294967295 d0_pre) 32 =
               rpre0 + d0_pre).
  { rewrite Hland0. apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296. lia. }
  replace (4294967296 ^ 2) with (4294967296 * 4294967296) in PreH28
    by reflexivity.
  assert (Hhi_lt: rpre1 + d1_pre < 4294967296).
  { apply (Zmult_lt_reg_r _ _ 4294967296); [lia |].
    nia. }
  assert (Hhi: unsigned_last_nbits
                 (unsigned_last_nbits
                    (rpre1 + Z.land 4294967295 d1_pre) 32 + 0) 32 =
               rpre1 + d1_pre).
  { rewrite Hland1, Z.add_0_r.
    assert (Hinner: unsigned_last_nbits (rpre1 + d1_pre) 32 =
                    rpre1 + d1_pre).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite Hinner.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  rewrite Hhi, Hlow.
  replace ((rpre1 + d1_pre) * 4294967296 + (rpre0 + d0_pre))
    with (rpre1 * 4294967296 + rpre0 +
          (d1_pre * 4294967296 + d0_pre)) by abstract ring.
  assert (HB2_le_2D: 4294967296 * 4294967296 <=
                     2 * (d1_pre * 4294967296 + d0_pre)).
  { change (4294967296 ÷ 2) with 2147483648 in PreH11.
    nia. }
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_3 :
  gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst m.
  pose proof (unsigned_Lastnbits_range (rpre0 + Z.land UINT_MAX d0_pre) 32 ltac:(lia))
    as Hrange.
  change UINT_MAX with 4294967295.
  change (2 ^ 32) with 4294967296 in Hrange.
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_4 :
  gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst m.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (rpre1 + Z.land UINT_MAX d1_pre) 32 + 0) 32 ltac:(lia))
    as Hrange.
  change UINT_MAX with 4294967295.
  change (2 ^ 32) with 4294967296 in Hrange.
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_5 :
  gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst m.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (rpre1 + Z.land UINT_MAX d1_pre) 32 + 0) 32 ltac:(lia))
    as Hrange.
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_5 :
  gmp_udiv_qr_3by2_entail_wit_8_5.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_1.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_2.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_3.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_4.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_5.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_1 :
  gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  assert (Hlow_ge: 4294967296 <= rpre0 + d0_pre).
  { destruct (Z_lt_ge_dec (rpre0 + d0_pre) 4294967296) as [Hlt | Hge].
    - rewrite Hland0 in PreH1.
      assert (Hsmall: unsigned_last_nbits (rpre0 + d0_pre) 32 = rpre0 + d0_pre).
      { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296.
        split; [apply Z.add_nonneg_nonneg; [exact PreH23 | exact PreH13] | exact Hlt]. }
      rewrite Hsmall in PreH1.
      nia.
    - apply Z.ge_le in Hge. exact Hge. }
  assert (Hlow: unsigned_last_nbits (rpre0 + Z.land 4294967295 d0_pre) 32 =
                rpre0 + d0_pre - 4294967296).
  { rewrite Hland0. apply unsigned_last_nbits_overflow_32. nia. }
  replace (4294967296 ^ 2) with (4294967296 * 4294967296) in PreH28 by reflexivity.
  assert (Hhi_lt: rpre1 + d1_pre + 1 < 4294967296).
  { apply (Zmult_lt_reg_r _ _ 4294967296); [lia |].
    nia. }
  assert (Hhi: unsigned_last_nbits
                 (unsigned_last_nbits (rpre1 + Z.land 4294967295 d1_pre) 32 + 1) 32 =
               rpre1 + d1_pre + 1).
  { rewrite Hland1.
    assert (Hinner: unsigned_last_nbits (rpre1 + d1_pre) 32 = rpre1 + d1_pre).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite Hinner.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  rewrite Hhi, Hlow.
  change (0 + 4294967295) with 4294967295.
  replace (4294967295 * (d1_pre * 4294967296 + d0_pre) +
           (rpre1 + d1_pre + 1) * 4294967296 +
           (rpre0 + d0_pre - 4294967296))
    with (4294967296 * (d1_pre * 4294967296 + d0_pre) +
          rpre1 * 4294967296 + rpre0) by abstract ring.
  reflexivity.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_2 :
  gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  assert (Hlow_ge: 4294967296 <= rpre0 + d0_pre).
  { destruct (Z_lt_ge_dec (rpre0 + d0_pre) 4294967296) as [Hlt | Hge].
    - rewrite Hland0 in PreH1.
      assert (Hsmall: unsigned_last_nbits (rpre0 + d0_pre) 32 =
                      rpre0 + d0_pre).
      { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296.
        split; [apply Z.add_nonneg_nonneg; [exact PreH23 | exact PreH13] |
                exact Hlt]. }
      rewrite Hsmall in PreH1.
      nia.
    - apply Z.ge_le in Hge. exact Hge. }
  assert (Hlow: unsigned_last_nbits
                 (rpre0 + Z.land 4294967295 d0_pre) 32 =
               rpre0 + d0_pre - 4294967296).
  { rewrite Hland0. apply unsigned_last_nbits_overflow_32. nia. }
  replace (4294967296 ^ 2) with (4294967296 * 4294967296) in PreH28
    by reflexivity.
  assert (Hhi_lt: rpre1 + d1_pre + 1 < 4294967296).
  { apply (Zmult_lt_reg_r _ _ 4294967296); [lia |].
    nia. }
  assert (Hhi: unsigned_last_nbits
                 (unsigned_last_nbits
                    (rpre1 + Z.land 4294967295 d1_pre) 32 + 1) 32 =
               rpre1 + d1_pre + 1).
  { rewrite Hland1.
    assert (Hinner: unsigned_last_nbits (rpre1 + d1_pre) 32 =
                    rpre1 + d1_pre).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite Hinner.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  rewrite Hhi, Hlow.
  replace ((rpre1 + d1_pre + 1) * 4294967296 +
           (rpre0 + d0_pre - 4294967296))
    with (rpre1 * 4294967296 + rpre0 +
          (d1_pre * 4294967296 + d0_pre)) by abstract ring.
  assert (HB2_le_2D: 4294967296 * 4294967296 <=
                     2 * (d1_pre * 4294967296 + d0_pre)).
  { change (4294967296 ÷ 2) with 2147483648 in PreH11.
    nia. }
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_3 :
  gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst m.
  pose proof (unsigned_Lastnbits_range (rpre0 + Z.land UINT_MAX d0_pre) 32 ltac:(lia))
    as Hrange.
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_4 :
  gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst m.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (rpre1 + Z.land UINT_MAX d1_pre) 32 + 1) 32 ltac:(lia))
    as Hrange.
  change UINT_MAX with 4294967295.
  change (2 ^ 32) with 4294967296 in Hrange.
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_5 :
  gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst m.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (rpre1 + Z.land UINT_MAX d1_pre) 32 + 1) 32 ltac:(lia))
    as Hrange.
  lia.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_8_6 :
  gmp_udiv_qr_3by2_entail_wit_8_6.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_1.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_2.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_3.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_4.
  + Goal_apply proof_of_gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_5.
Qed.
