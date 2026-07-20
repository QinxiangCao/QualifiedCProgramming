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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_invert_3by2_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_invert_3by2_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_invert_3by2_entail_wit_1 : mpn_invert_3by2_entail_wit_1.
Proof.
  pre_process; entailer!.
  - pose proof (Z.land_nonneg u1_pre 65535) as Hland; lia.
  - pose proof (mpn_invert_u1_range u1_pre PreH1 PreH2); lia.
  - pose proof (land_65535_bounds u1_pre
                  (mpn_invert_u1_range u1_pre PreH1 PreH2)) as [? ?].
    lia.
  - apply (mpn_invert_u1_high_nonzero u1_pre PreH1 PreH2).
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_2 : mpn_invert_3by2_entail_wit_2.
Proof.
  pre_process; entailer!.
  - pose proof (mpn_invert_qh_quot_range
                  u1_pre (Z.shiftr u1_pre 16) PreH6 PreH7 eq_refl)
      as [_ Hqh].
    lia.
  - pose proof (mpn_invert_qh_quot_range
                  u1_pre (Z.shiftr u1_pre 16) PreH6 PreH7 eq_refl)
      as [Hqh _].
    lia.
  - pose proof (mpn_invert_u1_split16 u1_pre PreH6 PreH7)
      as [_ [_ Hsplit]].
    exact Hsplit.
  - pose proof (mpn_invert_u1_split16 u1_pre PreH6 PreH7)
      as [_ [[_ Huh] _]].
    lia.
  - pose proof (mpn_invert_u1_split16 u1_pre PreH6 PreH7)
      as [_ [[Huh _] _]].
    lia.
  - pose proof (mpn_invert_u1_split16 u1_pre PreH6 PreH7)
      as [[_ Hul] _].
    lia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_3_1 : mpn_invert_3by2_entail_wit_3_1.
Proof.
  unfold mpn_invert_3by2_entail_wit_3_1.
  right.
  intros.
  set (r0 := Z.lor
      (unsigned_last_nbits
         (Z.shiftl
            (unsigned_last_nbits
               (unsigned_last_nbits (Z.lnot u1_pre) 32 -
                qh0 * uh0) 32) 16) 32) 65535).
  set (p0 := qh0 * ul0).
  set (r1 := unsigned_last_nbits (r0 + u1_pre) 32).
  set (r2 := unsigned_last_nbits (r1 + u1_pre) 32).
  fold r0 in PreH1, PreH2, PreH3.
  fold p0 in PreH1, PreH3.
  fold r1 in PreH1, PreH2.
  assert (Hu: 0 <= u1_pre < 4294967296) by (subst u1_pre; nia).
  pose proof (mpn_invert_qh_rem_bounds u1_pre uh0 qh0 Hu ltac:(lia) PreH10)
    as [Hle Hrem].
  assert (Hr0: r0 = (4294967295 - u1_pre - qh0 * uh0) * 65536 + 65535).
  { subst r0.
    replace (qh0 * uh0) with (unsigned_last_nbits (qh0 * uh0) 32) at 1.
    - apply mpn_invert_rinit_simpl; lia.
    - apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296; nia. }
  assert (Hp0: p0 = qh0 * ul0) by reflexivity.
  assert (Hcase: r0 < p0) by lia.
  assert (Hnowrap: r0 + u1_pre < 4294967296).
  { destruct (Z_lt_ge_dec (r0 + u1_pre) 4294967296) as [Hnowrap | Hwrap]; [lia |].
    assert (Hr1wrap: r1 = r0 + u1_pre - 4294967296).
    { subst r1. apply unsigned_last_nbits_overflow_32. nia. }
    nia. }
  assert (Hr1: r1 = r0 + u1_pre).
  { subst r1.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296; nia. }
  assert (Hcase1: r0 + u1_pre < p0) by nia.
  pose proof (mpn_invert_first_two_adjust_simpl
                u1_pre ul0 uh0 qh0 (4294967295 - u1_pre - qh0 * uh0)
                r0 p0 ltac:(lia) ltac:(lia) PreH15 ltac:(lia)
                Hrem ltac:(nia) Hr0 Hp0 Hcase Hnowrap ltac:(nia) Hcase1)
    as [Heq [Hrng Hqh_pos]].
  assert (Hqhdec1: unsigned_last_nbits (qh0 - 1) 32 = qh0 - 1).
  { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296; lia. }
  assert (Hqhdec2:
            unsigned_last_nbits (unsigned_last_nbits (qh0 - 1) 32 - 1) 32 =
            qh0 - 2).
  { rewrite Hqhdec1.
    replace (qh0 - 1 - 1) with (qh0 - 2) by ring.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296; lia. }
  assert (Hfinal: unsigned_last_nbits (r2 - p0) 32 = r0 + 2 * u1_pre - p0).
  { subst r2.
    destruct (Z_lt_ge_dec (r1 + u1_pre) 4294967296) as [Hnowrap2 | Hwrap2].
    - assert (Hr2: unsigned_last_nbits (r1 + u1_pre) 32 = r1 + u1_pre).
      { apply unsigned_last_nbits_eq.
        change (2 ^ 32) with 4294967296; lia. }
      rewrite Hr2.
      rewrite Hr1.
      replace (r0 + u1_pre + u1_pre - p0) with
        (r0 + 2 * u1_pre - p0) by ring.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296; lia.
    - assert (Hr2: unsigned_last_nbits (r1 + u1_pre) 32 =
                   r1 + u1_pre - 4294967296).
      { apply unsigned_last_nbits_overflow_32. nia. }
      rewrite Hr2.
      rewrite Hr1.
      replace (r0 + u1_pre + u1_pre - 4294967296 - p0)
        with ((r0 + 2 * u1_pre - p0) - 4294967296) by ring.
      apply unsigned_last_nbits_underflow_32.
      lia. }
  clear PreH1 PreH2 PreH3 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
        PreH15 PreH16 PreH17 PreH18 Hu Hle Hrem Hr0 Hp0 Hcase Hnowrap Hr1
        Hcase1 Hqhdec1 Hqhdec2.
  fold r0. fold r1. fold r2. fold p0.
  entailer!.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_3_2 : mpn_invert_3by2_entail_wit_3_2.
Proof.
  unfold mpn_invert_3by2_entail_wit_3_2.
  right.
  intros.
  set (r0 := Z.lor
      (unsigned_last_nbits
         (Z.shiftl
            (unsigned_last_nbits
               (unsigned_last_nbits (Z.lnot u1_pre) 32 -
                qh0 * uh0) 32) 16) 32) 65535).
  set (p0 := qh0 * ul0).
  set (r1 := unsigned_last_nbits (r0 + u1_pre) 32).
  fold r0 in PreH1, PreH2, PreH3.
  fold p0 in PreH1, PreH3.
  fold r1 in PreH1, PreH2.
  assert (Hu: 0 <= u1_pre < 4294967296) by (subst u1_pre; nia).
  pose proof (mpn_invert_qh_rem_bounds u1_pre uh0 qh0 Hu ltac:(lia) PreH10)
    as [Hle Hrem].
  assert (Hr0: r0 = (4294967295 - u1_pre - qh0 * uh0) * 65536 + 65535).
  { subst r0.
    replace (qh0 * uh0) with (unsigned_last_nbits (qh0 * uh0) 32) at 1.
    - apply mpn_invert_rinit_simpl; lia.
    - apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296; nia. }
  assert (Hp0: p0 = qh0 * ul0) by reflexivity.
  assert (Hcase: r0 < p0) by lia.
  assert (Hnowrap: r0 + u1_pre < 4294967296).
  { destruct (Z_lt_ge_dec (r0 + u1_pre) 4294967296) as [Hnowrap | Hwrap]; [lia |].
    assert (Hr1wrap: r1 = r0 + u1_pre - 4294967296).
    { subst r1. apply unsigned_last_nbits_overflow_32. nia. }
    nia. }
  assert (Hr1: r1 = r0 + u1_pre).
  { subst r1.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296; nia. }
  assert (Hcase1: p0 <= r0 + u1_pre) by nia.
  pose proof (mpn_invert_first_one_adjust_simpl
                u1_pre ul0 uh0 qh0 (4294967295 - u1_pre - qh0 * uh0)
                r0 p0 ltac:(lia) ltac:(lia) PreH15 ltac:(lia)
                Hrem ltac:(nia) Hr0 Hp0 Hcase Hnowrap Hcase1)
    as [Heq [Hrng Hqh_pos]].
  assert (Hqhdec: unsigned_last_nbits (qh0 - 1) 32 = qh0 - 1).
  { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296; lia. }
  assert (Hfinal: r1 - p0 = r0 + u1_pre - p0) by nia.
  clear PreH1 PreH2 PreH3 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
        PreH15 PreH16 Hu Hle Hrem Hr0 Hp0 Hcase Hnowrap Hr1 Hcase1 Hqhdec.
  fold r0. fold r1. fold p0.
  entailer!.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_3_3 : mpn_invert_3by2_entail_wit_3_3.
Proof.
  unfold mpn_invert_3by2_entail_wit_3_3.
  right.
  intros.
  set (r0 := Z.lor
      (unsigned_last_nbits
         (Z.shiftl
            (unsigned_last_nbits
               (unsigned_last_nbits (Z.lnot u1_pre) 32 -
                qh0 * uh0) 32) 16) 32) 65535).
  set (p0 := qh0 * ul0).
  set (r1 := unsigned_last_nbits (r0 + u1_pre) 32).
  fold r0 in PreH1, PreH2.
  fold p0 in PreH2.
  fold r1 in PreH1.
  assert (Hu: 0 <= u1_pre < 4294967296) by (subst u1_pre; nia).
  pose proof (mpn_invert_qh_rem_bounds u1_pre uh0 qh0 Hu ltac:(lia) PreH9)
    as [Hle Hrem].
  assert (Hr0: r0 = (4294967295 - u1_pre - qh0 * uh0) * 65536 + 65535).
  { subst r0.
    replace (qh0 * uh0) with (unsigned_last_nbits (qh0 * uh0) 32) at 1.
    - apply mpn_invert_rinit_simpl; lia.
    - apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296; nia. }
  assert (Hp0: p0 = qh0 * ul0) by reflexivity.
  assert (Hcase: r0 < p0) by lia.
  assert (Hwrap: 4294967296 <= r0 + u1_pre).
  { destruct (Z_lt_ge_dec (r0 + u1_pre) 4294967296) as [Hnowrap | Hwrap]; [| lia].
    assert (Hr1_nowrap: r1 = r0 + u1_pre).
    { subst r1.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296; nia. }
    nia. }
  assert (Hrem_eq :
    4294967295 - u1_pre =
      qh0 * uh0 + (4294967295 - u1_pre - qh0 * uh0)) by ring.
  pose proof (mpn_invert_first_overflow_simpl
                u1_pre ul0 uh0 qh0 (4294967295 - u1_pre - qh0 * uh0)
                r0 p0 ltac:(lia) ltac:(lia) PreH14 ltac:(lia)
                Hrem Hrem_eq Hr0 Hp0 Hcase Hwrap)
    as [Heq [Hrng Hqh_pos]].
  assert (Hqhdec: unsigned_last_nbits (qh0 - 1) 32 = qh0 - 1).
  { apply unsigned_last_nbits_eq. change (2 ^ 32) with 4294967296; lia. }
  assert (Hr1: unsigned_last_nbits (r0 + u1_pre) 32 =
               r0 + u1_pre - 4294967296).
  { apply unsigned_last_nbits_overflow_32. nia. }
  assert (Hfinal:
            unsigned_last_nbits (unsigned_last_nbits (r0 + u1_pre) 32 - p0) 32 =
            r0 + u1_pre - p0).
  { rewrite Hr1.
    replace (r0 + u1_pre - 4294967296 - p0)
      with ((r0 + u1_pre - p0) - 4294967296) by ring.
    apply unsigned_last_nbits_underflow_32.
    lia. }
  clear PreH1 PreH2 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
        PreH15 Hu Hle Hrem Hr0 Hp0 Hcase Hwrap Hqhdec.
  fold r0. fold r1. fold p0.
  fold r1 in Hfinal. fold p0 in Hfinal.
  entailer!.
  all: rewrite Hfinal; lia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_3_4 : mpn_invert_3by2_entail_wit_3_4.
Proof.
  unfold mpn_invert_3by2_entail_wit_3_4.
  right.
  intros.
  set (r0 := Z.lor
      (unsigned_last_nbits
         (Z.shiftl
            (unsigned_last_nbits
               (unsigned_last_nbits (Z.lnot u1_pre) 32 -
                qh0 * uh0) 32) 16) 32) 65535).
  set (p0 := qh0 * ul0).
  fold r0 in PreH1.
  fold p0 in PreH1.
  assert (Hu: 0 <= u1_pre < 4294967296) by (subst u1_pre; nia).
  pose proof (mpn_invert_qh_rem_bounds u1_pre uh0 qh0 Hu ltac:(lia) PreH8)
    as [Hle Hrem].
  assert (Hr0: r0 = (4294967295 - u1_pre - qh0 * uh0) * 65536 + 65535).
  { subst r0.
    replace (qh0 * uh0) with (unsigned_last_nbits (qh0 * uh0) 32) at 1.
    - apply mpn_invert_rinit_simpl; lia.
    - apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296; nia. }
  assert (Hp0: p0 = qh0 * ul0) by reflexivity.
  assert (Hcase: p0 <= r0) by lia.
  assert (Hrem_eq :
    4294967295 - u1_pre =
      qh0 * uh0 + (4294967295 - u1_pre - qh0 * uh0)) by ring.
  pose proof (mpn_invert_first_no_adjust_simpl
                u1_pre ul0 uh0 qh0 (4294967295 - u1_pre - qh0 * uh0)
                r0 p0 ltac:(lia) ltac:(lia) PreH13 ltac:(lia)
                Hrem Hrem_eq Hr0 Hp0 Hcase)
    as [Heq Hrng].
  clear PreH1 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
        PreH15 Hu Hle Hrem Hr0 Hp0 Hcase Hrem_eq.
  fold r0. fold p0.
  entailer!.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_4 : mpn_invert_3by2_entail_wit_4.
Proof.
  unfold mpn_invert_3by2_entail_wit_4.
  right.
  intros.
  entailer!.
  - pose proof (unsigned_Lastnbits_range
                  (unsigned_last_nbits (Z.shiftr rhalf 16 * qh0) 32 + rhalf)
                  32 ltac:(lia)) as Hp.
    lia.
  - pose proof (unsigned_Lastnbits_range
                  (unsigned_last_nbits (Z.shiftr rhalf 16 * qh0) 32 + rhalf)
                  32 ltac:(lia)) as Hp.
    change (2 ^ 32) with 4294967296 in Hp.
    lia.
  - pose proof (unsigned_Lastnbits_range
                  (Z.shiftr
                     (unsigned_last_nbits
                        (unsigned_last_nbits (Z.shiftr rhalf 16 * qh0) 32 + rhalf) 32)
                     16 + 1) 32 ltac:(lia)) as Hq.
    lia.
  - pose proof (mpn_invert_second_p_bounds u1_pre qh0 rhalf
                  ltac:(lia) ltac:(lia) PreH9) as Hp.
    pose proof (mpn_invert_second_p_unsigned u1_pre qh0 rhalf
                  ltac:(lia) ltac:(lia) PreH9) as Hp_eq.
    rewrite Hp_eq.
    rewrite (mpn_invert_second_ql_unsigned
               (Z.shiftr rhalf 16 * qh0 + rhalf) Hp).
    pose proof (mpn_invert_second_ql_bounds
                  (Z.shiftr rhalf 16 * qh0 + rhalf) Hp) as Hq.
    lia.
  - apply (mpn_invert_second_p_unsigned u1_pre qh0 rhalf);
      lia || exact PreH9.
  - pose proof (mpn_invert_second_p_bounds u1_pre qh0 rhalf
                  ltac:(lia) ltac:(lia) PreH9) as Hp.
    rewrite (mpn_invert_second_p_unsigned u1_pre qh0 rhalf
               ltac:(lia) ltac:(lia) PreH9).
    apply mpn_invert_second_ql_unsigned.
    exact Hp.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_5_1 : mpn_invert_3by2_entail_wit_5_1.
Proof.
  unfold mpn_invert_3by2_entail_wit_5_1.
  right.
  intros.
  set (rout :=
    unsigned_last_nbits
      (unsigned_last_nbits
         (unsigned_last_nbits (Z.shiftl rhalf 16) 32 + 65535) 32 -
       unsigned_last_nbits (ql0 * u1_pre) 32) 32) in *.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  pose proof (mpn_invert_second_adjust_simpl
    u1_pre qh0 rhalf p0 ql0 rout
    ltac:(lia) ltac:(lia) ltac:(lia) PreH10
    ltac:(lia) ltac:(lia) PreH15 PreH16 eq_refl PreH1)
    as (Hmq & Hrng & Heqv & Hql_ge1).
  assert (Hql_dec: unsigned_last_nbits (ql0 - 1) 32 = ql0 - 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  entailer!;
  try rewrite Hql_dec;
  try exact Heqv;
  try lia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_5_2 : mpn_invert_3by2_entail_wit_5_2.
Proof.
  unfold mpn_invert_3by2_entail_wit_5_2.
  right.
  intros.
  set (rout :=
    unsigned_last_nbits
      (unsigned_last_nbits
         (unsigned_last_nbits (Z.shiftl rhalf 16) 32 + 65535) 32 -
       unsigned_last_nbits (ql0 * u1_pre) 32) 32) in *.
  entailer!.
  all: pose proof (mpn_invert_second_no_adjust_simpl
                u1_pre qh0 rhalf p0 ql0 rout
                ltac:(lia) ltac:(lia) PreH10 ltac:(lia) ltac:(lia)
                PreH15 PreH16 eq_refl PreH1) as [Hmq [Hrng Heqv]].
  - lia.
  - lia.
  - lia.
  - change UINT_MOD with 4294967296.
    exact Heqv.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_6 : mpn_invert_3by2_entail_wit_6.
Proof.
  unfold mpn_invert_3by2_entail_wit_6.
  right.
  intros.
  assert (Hm: unsigned_last_nbits (unsigned_last_nbits (Z.shiftl qh0 16) 32 + ql0) 32 =
              qh0 * 65536 + ql0).
  { assert (Hshift: unsigned_last_nbits (Z.shiftl qh0 16) 32 = qh0 * 65536).
    { unfold unsigned_last_nbits.
      rewrite Z.shiftl_mul_pow2 by lia.
      change (2 ^ 16) with 65536.
      change (2 ^ 32) with 4294967296.
      apply Z.mod_small.
      nia. }
    rewrite Hshift.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  entailer!.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_7_1 : mpn_invert_3by2_entail_wit_7_1.
Proof.
  unfold mpn_invert_3by2_entail_wit_7_1.
  right.
  intros.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  assert (Hm_hi: mpre <= 4294967294).
  { destruct (Z_lt_ge_dec mpre 4294967295) as [Hlt | Hge].
    - lia.
    - assert (Hmpre: mpre = 4294967295) by lia.
      subst mpre.
      assert (Hlower:
        4294967296 ^ 2 <=
        ((4294967295 + 4294967296) * u1_pre + rpre)).
      { lia. }
      lia. }
  assert (Hm_next:
            unsigned_last_nbits (mpre + 1) 32 = mpre + 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  entailer!.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_8_1 : mpn_invert_3by2_entail_wit_8_1.
Proof.
  unfold mpn_invert_3by2_entail_wit_8_1.
  right.
  intros.
  assert (Hu_pos: 0 < u1_pre) by lia.
  assert (Hu_bound: u1_pre < 4294967296).
  { change UINT_MAX with 4294967295 in PreH5; lia. }
  assert (Hu0_bound: 0 < u0_pre < 4294967296).
  { change UINT_MAX with 4294967295 in PreH7; lia. }
  assert (Hr_bound: 0 <= r0 < 4294967296) by lia.
  rewrite (unsigned_lnot_32 r0 Hr_bound) in *.
  set (a := 4294967295 - r0) in *.
  set (s := unsigned_last_nbits (a + u0_pre) 32) in *.
  assert (Hs_range: 0 <= s < 4294967296).
  { subst s. apply unsigned_Lastnbits_range. lia. }
  assert (Ha_range: 0 <= a < 4294967296) by (subst a; lia).
  assert (Hs_eq: s = a + u0_pre - 4294967296).
  { subst s.
    destruct (Z_lt_ge_dec (a + u0_pre) 4294967296) as [Hno|Hov].
    - assert (unsigned_last_nbits (a + u0_pre) 32 = a + u0_pre).
      { apply unsigned_last_nbits_eq.
        change (2 ^ 32) with 4294967296.
        lia. }
      lia.
    - apply unsigned_last_nbits_overflow_32.
      lia. }
  assert (Hu_half: 2147483648 <= u1_pre).
  { change UINT_MOD with 4294967296 in PreH13.
    change (4294967296 ÷ 2) with 2147483648 in PreH13.
    lia. }
  assert (Hm_pos: 2 <= m0).
  { subst s a.
    change UINT_MOD with 4294967296 in PreH12.
    change (4294967296 ^ 2) with 18446744073709551616 in PreH12.
    nia. }
  assert (Hm_dec1: unsigned_last_nbits (m0 - 1) 32 = m0 - 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  assert (Hm_dec2:
            unsigned_last_nbits (unsigned_last_nbits (m0 - 1) 32 - 1) 32 =
            m0 - 2).
  { rewrite Hm_dec1.
    replace (m0 - 1 - 1) with (m0 - 2) by ring.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  assert (Hs_sub2:
            unsigned_last_nbits ((s - u1_pre) - u1_pre) 32 =
            s - 2 * u1_pre + 4294967296).
  { pose proof (unsigned_last_nbits_underflow_32
                  (s - 2 * u1_pre + 4294967296) ltac:(lia)) as Hunder.
    replace (s - 2 * u1_pre + 4294967296 - 4294967296) with
      ((s - u1_pre) - u1_pre) in Hunder by ring.
    exact Hunder. }
  entailer!;
  try rewrite Hm_dec2;
  try rewrite Hs_sub2;
  subst s a;
  change UINT_MOD with 4294967296 in *;
  change (4294967296 ^ 2) with 18446744073709551616 in *;
  nia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_8_2 : mpn_invert_3by2_entail_wit_8_2.
Proof.
  unfold mpn_invert_3by2_entail_wit_8_2.
  right.
  intros.
  assert (Hu_pos: 0 < u1_pre) by lia.
  assert (Hu_bound: u1_pre < 4294967296)
    by (change UINT_MAX with 4294967295 in PreH5; lia).
  assert (Hu0_bound: 0 < u0_pre < 4294967296)
    by (change UINT_MAX with 4294967295 in PreH7; lia).
  assert (Hr_bound: 0 <= r0 < 4294967296) by lia.
  rewrite (unsigned_lnot_32 r0 Hr_bound) in *.
  set (a := 4294967295 - r0) in *.
  set (s := unsigned_last_nbits (a + u0_pre) 32) in *.
  assert (Hs_range: 0 <= s < 4294967296).
  { subst s. apply unsigned_Lastnbits_range. lia. }
  assert (Ha_range: 0 <= a < 4294967296) by (subst a; lia).
  assert (Hs_eq: s = a + u0_pre - 4294967296).
  { subst s.
    destruct (Z_lt_ge_dec (a + u0_pre) 4294967296) as [Hno|Hov].
    - assert (unsigned_last_nbits (a + u0_pre) 32 = a + u0_pre).
      { apply unsigned_last_nbits_eq.
        change (2 ^ 32) with 4294967296.
        lia. }
      lia.
    - apply unsigned_last_nbits_overflow_32.
      lia. }
  assert (Hm_pos: 1 <= m0).
  { change UINT_MOD with 4294967296 in PreH12.
    change (4294967296 ^ 2) with 18446744073709551616 in PreH12.
    nia. }
  assert (Hm_dec: unsigned_last_nbits (m0 - 1) 32 = m0 - 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  assert (Hs_sub: unsigned_last_nbits (s - u1_pre) 32 = s - u1_pre + 4294967296).
  { pose proof (unsigned_last_nbits_underflow_32
                  (s - u1_pre + 4294967296) ltac:(lia)) as Hunder.
    replace (s - u1_pre + 4294967296 - 4294967296) with
      (s - u1_pre) in Hunder by ring.
    exact Hunder. }
  entailer!;
  try rewrite Hm_dec;
  try rewrite Hs_sub;
  subst s a;
  change UINT_MOD with 4294967296 in *;
  change (4294967296 ^ 2) with 18446744073709551616 in *;
  nia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_8_3 : mpn_invert_3by2_entail_wit_8_3.
Proof.
  unfold mpn_invert_3by2_entail_wit_8_3.
  right.
  intros.
  assert (Hu_pos: 0 < u1_pre) by lia.
  assert (Hu_bound: u1_pre < 4294967296).
  { change UINT_MAX with 4294967295 in PreH4; lia. }
  assert (Hu0_bound: 0 < u0_pre < 4294967296).
  { change UINT_MAX with 4294967295 in PreH6; lia. }
  assert (Hr_bound: 0 <= r0 < 4294967296) by lia.
  rewrite (unsigned_lnot_32 r0 Hr_bound) in *.
  set (a := 4294967295 - r0) in *.
  set (s := unsigned_last_nbits (a + u0_pre) 32) in *.
  assert (Hs_range: 0 <= s < 4294967296).
  { subst s. apply unsigned_Lastnbits_range. lia. }
  assert (Ha_range: 0 <= a < 4294967296) by (subst a; lia).
  assert (Hs_eq: s = a + u0_pre).
  { subst s.
    destruct (Z_lt_ge_dec (a + u0_pre) 4294967296) as [Hno|Hov].
    - apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia.
    - assert (Hover: unsigned_last_nbits (a + u0_pre) 32 = a + u0_pre - 4294967296).
      { apply unsigned_last_nbits_overflow_32. lia. }
      assert (unsigned_last_nbits (a + u0_pre) 32 < u0_pre) by lia.
      lia. }
  entailer!;
  subst s;
  subst a;
  change UINT_MOD with 4294967296 in *;
  change (4294967296 ^ 2) with 18446744073709551616 in *;
  nia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_12_1 : mpn_invert_3by2_entail_wit_12_1.
Proof.
  unfold mpn_invert_3by2_entail_wit_12_1.
  right.
  intros.
  set (r2 := unsigned_last_nbits (r1 + thv) 32) in *.
  assert (Hrth_wrap: 4294967296 <= r1 + thv).
  { destruct (Z_lt_ge_dec (r1 + thv) 4294967296) as [Hno | Hwrap]; [| lia].
    assert (Hnoeq: r2 = r1 + thv).
    { subst r2.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite Hnoeq in PreH4.
    lia. }
  assert (Hr2_eq: r2 = r1 + thv - 4294967296).
  { subst r2.
    apply unsigned_last_nbits_overflow_32.
    lia. }
  assert (Hr2_range: 0 <= r2 < 4294967296).
  { subst r2. apply unsigned_Lastnbits_range. lia. }
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  change (4294967296 ^ 2) with 18446744073709551616 in *.
  change (4294967296 ^ 3) with 79228162514264337593543950336 in *.
  change (Z.lor 0 (Z.land 0 0)) with 0.
  pose proof (mpn_invert_final_carry_one_lt
    u0_pre u1_pre m1 r1 tlv thv r2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    PreH18 PreH19 PreH20 Hr2_eq Hr2_range
    ltac:(lia)) as (Hm_ge1 & Hle & Hlt).
  assert (Hm_dec1: unsigned_last_nbits (m1 - 1) 32 = m1 - 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  rewrite Hm_dec1.
  entailer!;
  lia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_12_2 : mpn_invert_3by2_entail_wit_12_2.
Proof.
  unfold mpn_invert_3by2_entail_wit_12_2.
  right.
  intros.
  set (r2 := unsigned_last_nbits (r1 + thv) 32) in *.
  assert (Hrth_wrap: 4294967296 <= r1 + thv).
  { destruct (Z_lt_ge_dec (r1 + thv) 4294967296) as [Hno | Hwrap]; [| lia].
    assert (Hnoeq: r2 = r1 + thv).
    { subst r2.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite Hnoeq in PreH4.
    lia. }
  assert (Hr2_eq: r2 = r1 + thv - 4294967296).
  { subst r2.
    apply unsigned_last_nbits_overflow_32.
    lia. }
  assert (Hr2_range: 0 <= r2 < 4294967296).
  { subst r2. apply unsigned_Lastnbits_range. lia. }
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  change (4294967296 ^ 2) with 18446744073709551616 in *.
  change (4294967296 ^ 3) with 79228162514264337593543950336 in *.
  change (Z.lor 0 (Z.land 0 1)) with 0.
  pose proof (mpn_invert_final_carry_one_lt
    u0_pre u1_pre m1 r1 tlv thv r2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    PreH18 PreH19 PreH20 Hr2_eq Hr2_range
    ltac:(lia)) as (Hm_ge1 & Hle & Hlt).
  assert (Hm_dec1: unsigned_last_nbits (m1 - 1) 32 = m1 - 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  rewrite Hm_dec1.
  entailer!;
  lia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_12_3 : mpn_invert_3by2_entail_wit_12_3.
Proof.
  unfold mpn_invert_3by2_entail_wit_12_3.
  right.
  intros.
  set (r2 := unsigned_last_nbits (r1 + thv) 32) in *.
  assert (Hrth_wrap: 4294967296 <= r1 + thv).
  { destruct (Z_lt_ge_dec (r1 + thv) 4294967296) as [Hno | Hwrap]; [| lia].
    assert (Hnoeq: r2 = r1 + thv).
    { subst r2.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite Hnoeq in PreH4.
    lia. }
  assert (Hr2_eq: r2 = r1 + thv - 4294967296).
  { subst r2.
    apply unsigned_last_nbits_overflow_32.
    lia. }
  assert (Hr2_range: 0 <= r2 < 4294967296).
  { subst r2. apply unsigned_Lastnbits_range. lia. }
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  change (4294967296 ^ 2) with 18446744073709551616 in *.
  change (4294967296 ^ 3) with 79228162514264337593543950336 in *.
  change (Z.lor 0 (Z.land 1 0)) with 0.
  pose proof (mpn_invert_final_carry_one_eq
    u0_pre u1_pre m1 r1 tlv thv r2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    PreH18 PreH19 PreH20 Hr2_eq Hr2_range
    ltac:(lia) ltac:(lia)) as (Hm_ge1 & Hle & Hlt).
  assert (Hm_dec1: unsigned_last_nbits (m1 - 1) 32 = m1 - 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  rewrite Hm_dec1.
  entailer!;
  lia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_12_4 : mpn_invert_3by2_entail_wit_12_4.
Proof.
  unfold mpn_invert_3by2_entail_wit_12_4.
  right.
  intros.
  set (r2 := unsigned_last_nbits (r1 + thv) 32) in *.
  assert (Hrth_wrap: 4294967296 <= r1 + thv).
  { destruct (Z_lt_ge_dec (r1 + thv) 4294967296) as [Hno | Hwrap]; [| lia].
    assert (Hnoeq: r2 = r1 + thv).
    { subst r2.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite Hnoeq in PreH4.
    lia. }
  assert (Hr2_eq: r2 = r1 + thv - 4294967296).
  { subst r2.
    apply unsigned_last_nbits_overflow_32.
    lia. }
  assert (Hr2_range: 0 <= r2 < 4294967296).
  { subst r2. apply unsigned_Lastnbits_range. lia. }
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  change (4294967296 ^ 2) with 18446744073709551616 in *.
  change (4294967296 ^ 3) with 79228162514264337593543950336 in *.
  change (Z.lor 0 (Z.land 1 1)) with 1.
  pose proof (mpn_invert_final_carry_two
    u0_pre u1_pre m1 r1 tlv thv r2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    PreH18 PreH19 PreH20 Hr2_eq Hr2_range
    ltac:(right; split; lia)) as (Hm_ge2 & Hle & Hlt).
  assert (Hm_dec1: unsigned_last_nbits (m1 - 1) 32 = m1 - 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  assert (Hm_dec2:
    unsigned_last_nbits (unsigned_last_nbits (m1 - 1) 32 - 1) 32 =
    m1 - 2).
  { rewrite Hm_dec1.
    replace (m1 - 1 - 1) with (m1 - 2) by ring.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  rewrite Hm_dec2.
  entailer!;
  lia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_12_5 : mpn_invert_3by2_entail_wit_12_5.
Proof.
  unfold mpn_invert_3by2_entail_wit_12_5.
  right.
  intros.
  set (r2 := unsigned_last_nbits (r1 + thv) 32) in *.
  assert (Hrth_wrap: 4294967296 <= r1 + thv).
  { destruct (Z_lt_ge_dec (r1 + thv) 4294967296) as [Hno | Hwrap]; [| lia].
    assert (Hnoeq: r2 = r1 + thv).
    { subst r2.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite Hnoeq in PreH4.
    lia. }
  assert (Hr2_eq: r2 = r1 + thv - 4294967296).
  { subst r2.
    apply unsigned_last_nbits_overflow_32.
    lia. }
  assert (Hr2_range: 0 <= r2 < 4294967296).
  { subst r2. apply unsigned_Lastnbits_range. lia. }
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  change (4294967296 ^ 2) with 18446744073709551616 in *.
  change (4294967296 ^ 3) with 79228162514264337593543950336 in *.
  change (Z.lor 1 (Z.land 0 0)) with 1.
  pose proof (mpn_invert_final_carry_two
    u0_pre u1_pre m1 r1 tlv thv r2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    PreH18 PreH19 PreH20 Hr2_eq Hr2_range
    ltac:(left; lia)) as (Hm_ge2 & Hle & Hlt).
  assert (Hm_dec1: unsigned_last_nbits (m1 - 1) 32 = m1 - 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  assert (Hm_dec2:
    unsigned_last_nbits (unsigned_last_nbits (m1 - 1) 32 - 1) 32 =
    m1 - 2).
  { rewrite Hm_dec1.
    replace (m1 - 1 - 1) with (m1 - 2) by ring.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  rewrite Hm_dec2.
  entailer!;
  lia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_12_6 : mpn_invert_3by2_entail_wit_12_6.
Proof.
  unfold mpn_invert_3by2_entail_wit_12_6.
  right.
  intros.
  set (r2 := unsigned_last_nbits (r1 + thv) 32) in *.
  assert (Hrth_wrap: 4294967296 <= r1 + thv).
  { destruct (Z_lt_ge_dec (r1 + thv) 4294967296) as [Hno | Hwrap]; [| lia].
    assert (Hnoeq: r2 = r1 + thv).
    { subst r2.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite Hnoeq in PreH4.
    lia. }
  assert (Hr2_eq: r2 = r1 + thv - 4294967296).
  { subst r2.
    apply unsigned_last_nbits_overflow_32.
    lia. }
  assert (Hr2_range: 0 <= r2 < 4294967296).
  { subst r2. apply unsigned_Lastnbits_range. lia. }
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  change (4294967296 ^ 2) with 18446744073709551616 in *.
  change (4294967296 ^ 3) with 79228162514264337593543950336 in *.
  change (Z.lor 1 (Z.land 0 1)) with 1.
  pose proof (mpn_invert_final_carry_two
    u0_pre u1_pre m1 r1 tlv thv r2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    PreH18 PreH19 PreH20 Hr2_eq Hr2_range
    ltac:(left; lia)) as (Hm_ge2 & Hle & Hlt).
  assert (Hm_dec1: unsigned_last_nbits (m1 - 1) 32 = m1 - 1).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  assert (Hm_dec2:
    unsigned_last_nbits (unsigned_last_nbits (m1 - 1) 32 - 1) 32 =
    m1 - 2).
  { rewrite Hm_dec1.
    replace (m1 - 1 - 1) with (m1 - 2) by ring.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  rewrite Hm_dec2.
  entailer!;
  lia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_12_7 : mpn_invert_3by2_entail_wit_12_7.
Proof.
  unfold mpn_invert_3by2_entail_wit_12_7.
  right.
  intros.
  set (r2 := unsigned_last_nbits (r1 + thv) 32) in *.
  assert (Hrth_no_wrap: r1 + thv < 4294967296).
  { destruct (Z_lt_ge_dec (r1 + thv) 4294967296) as [Hnowrap | Hwrap]; [lia |].
    assert (Hwrap_eq: r2 = r1 + thv - 4294967296).
    { subst r2.
      apply unsigned_last_nbits_overflow_32.
      lia. }
    rewrite Hwrap_eq in PreH1.
    lia. }
  assert (Hrth_eq: r2 = r1 + thv).
  { subst r2.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  change (4294967296 ^ 2) with 18446744073709551616 in *.
  change (4294967296 ^ 3) with 79228162514264337593543950336 in *.
  pose proof (mpn_invert_final_no_carry
    u0_pre u1_pre m1 r1 tlv thv
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia)
    PreH15 PreH16 PreH17 Hrth_no_wrap) as [Hle Hlt].
  rewrite Hrth_eq.
  entailer!;
  lia.
Qed.

Lemma proof_of_mpn_invert_3by2_entail_wit_13_2 : mpn_invert_3by2_entail_wit_13_2.
Proof.
  unfold mpn_invert_3by2_entail_wit_13_2.
  right.
  intros.
  change UINT_MOD with 4294967296 in *.
  change (4294967296 ^ 2) with 18446744073709551616 in *.
  change (4294967296 ^ 3) with 79228162514264337593543950336 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  entailer!.
Qed.
