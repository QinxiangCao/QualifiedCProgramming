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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_udiv_qrnnd_preinv_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_udiv_qrnnd_preinv_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_gmp_udiv_qrnnd_preinv_return_wit_1 : gmp_udiv_qrnnd_preinv_return_wit_1.
Proof.
  assert (Hsplit1 : gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_1).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_1; intros.
  assert (Hql: unsigned_last_nbits (w0_value + nl_pre) 32 = w0_value + nl_pre) by
    (unfold unsigned_last_nbits in PreH3 |- *;
     change (2 ^ 32) with 4294967296 in *;
     assert (Hcond: (nl_pre + w0_value) mod 4294967296 >= w0_value) by
       (replace (nl_pre + w0_value) with (w0_value + nl_pre) by ring;
        exact PreH3);
     pose proof (Z_mod_add_uncarry nl_pre w0_value 4294967296
       ltac:(lia) ltac:(lia) ltac:(lia) Hcond) as Hunc;
     replace (w0_value + nl_pre) with (nl_pre + w0_value) by ring;
     symmetry; exact Hunc).
  assert (Hqh: unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 =
               w1_value + (nh_pre + 1)) by
    (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296;
     change UINT_MOD with 4294967296 in *;
     change (4294967296 ÷ 2) with 2147483648 in *; nia).
  rewrite Hqh; repeat rewrite unsigned_revolutive by lia.
  replace (Z.land (-0) d_pre) with 0 by reflexivity.
  repeat rewrite Z.add_0_r; repeat rewrite Z.add_0_l.
  rewrite Hqh in *.
  repeat rewrite unsigned_revolutive in * by lia.
  rewrite Hql in PreH2.
  replace (w1_value + (nh_pre + 1) + 0) with
    (w1_value + (nh_pre + 1)) in PreH2 by ring.
  rewrite Hqh in PreH2.
  repeat rewrite unsigned_revolutive in PreH2 by lia.
  replace (Z.land (-0) d_pre) with 0 in PreH1 by reflexivity.
  repeat rewrite Z.add_0_r in PreH1; repeat rewrite Z.add_0_l in PreH1.
  repeat rewrite unsigned_revolutive in PreH1 by lia.
  rewrite Hqh in PreH1.
  repeat rewrite unsigned_revolutive in PreH1 by lia.
  rewrite unsigned_last_nbits_sub_low_32.
  change UINT_MOD with 4294967296 in *.
  replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
    ((nh_pre * 4294967296 + nl_pre -
      (w1_value + nh_pre + 1 + 0) * d_pre) +
     (- nh_pre) * 4294967296) by ring.
  rewrite unsigned_last_nbits_add_mul_32.
  set (R := nh_pre * 4294967296 + nl_pre -
            (w1_value + nh_pre + 1 + 0) * d_pre) in *.
  rewrite unsigned_last_nbits_sub_low_32 in PreH1, PreH2.
  replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
    (R + (- nh_pre) * 4294967296) in PreH1 by (subst R; ring).
  replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
    (R + (- nh_pre) * 4294967296) in PreH2 by (subst R; ring).
  rewrite unsigned_last_nbits_add_mul_32 in PreH1, PreH2.
  assert (Hql_range: 0 <= w0_value + nl_pre < 4294967296) by
    (pose proof (unsigned_Lastnbits_range (w0_value + nl_pre) 32
       ltac:(lia)) as Hr;
     rewrite Hql in Hr; lia).
  assert (Hdlo: 2147483648 <= d_pre) by
    (change (4294967296 ÷ 2) with 2147483648 in PreH21; lia).
  assert (Hc0: 0 = 0 \/ 0 = 1) by (left; reflexivity).
  assert (Hcarry0: w0_value + nl_pre =
                    0 * 4294967296 + (w0_value + nl_pre)) by ring.
  pose proof (udiv_preinv_error_range d_pre di_pre nh_pre nl_pre
    w0_value w1_value (w0_value + nl_pre) 0 Hdlo PreH22 PreH23 PreH24
    PreH17 PreH18 PreH19 PreH20 PreH7 PreH8 PreH4 PreH10
    (proj1 Hql_range) (proj2 Hql_range) Hc0 Hcarry0 PreH16 PreH25 PreH26)
    as HRrange.
  fold R in HRrange.
  destruct (Z_lt_ge_dec R 0) as [HRneg | HRnonneg].
  - assert (HuR: unsigned_last_nbits R 32 = R + 4294967296).
    { unfold unsigned_last_nbits.
      change (2 ^ 32) with 4294967296.
      symmetry.
      apply Z.mod_unique with (q := -1); [left; lia | ring]. }
    rewrite HuR in PreH2.
    set (e := 4294967296 ^ 2 - (di_pre + 4294967296) * d_pre).
    pose proof (udiv_preinv_e_bounds d_pre di_pre Hdlo PreH22 PreH23 PreH24
      PreH25 PreH26) as He.
    fold e in He.
    assert (Hdi_eq: di_pre * d_pre =
      4294967296 ^ 2 - 4294967296 * d_pre - e) by (subst e; ring).
    assert (Hmul_d:
      (w1_value * 4294967296 + w0_value) * d_pre =
      nh_pre * di_pre * d_pre) by (rewrite PreH16; ring).
    assert (Hformula:
      4294967296 * R =
      w0_value * d_pre + nl_pre * 4294967296 + nh_pre * e -
      d_pre * 4294967296) by (subst R; nia).
    assert (Hgt: R + 4294967296 > w0_value + nl_pre).
    { enough (0 < 4294967296 * (R + 4294967296 -
                 (w0_value + nl_pre))) by nia.
      replace (4294967296 * (R + 4294967296 - (w0_value + nl_pre))) with
        (4294967296 * R +
         4294967296 * (4294967296 - (w0_value + nl_pre))) by ring.
      rewrite Hformula.
      replace (nl_pre * 4294967296 +
               4294967296 * (4294967296 - (w0_value + nl_pre))) with
        (4294967296 * (4294967296 - w0_value)) by ring.
      nia. }
    lia.
  - assert (HuR: unsigned_last_nbits R 32 = R).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296. lia. }
    rewrite HuR in PreH1.
    rewrite HuR.
    assert (Hqplus_range: 0 <= w1_value + (nh_pre + 1) + 1 < 4294967296).
    { split; [lia|].
      assert (HNlt: nh_pre * 4294967296 + nl_pre < d_pre * 4294967296)
        by nia.
      assert (HRge: R >= d_pre) by lia.
      subst R. nia. }
    rewrite unsigned_last_nbits_eq by
      (change (2 ^ 32) with 4294967296; exact Hqplus_range).
    subst R. ring.
  }
  assert (Hsplit2 : gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_2).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_2; intros.
  replace (Z.land (-0) d_pre) with 0 by reflexivity.
  repeat rewrite Z.add_0_r; repeat rewrite Z.add_0_l.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (nl_pre -
        unsigned_last_nbits
          (unsigned_last_nbits
             (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 *
           d_pre) 32) 32) 32 ltac:(lia)) as Hr.
  change (2 ^ 32) with 4294967296 in Hr.
  change UINT_MOD with 4294967296 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  replace (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) with
    (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32) in Hr by ring.
  lia.
  }
  assert (Hsplit3 : gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_3).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_3; intros.
  pose proof (unsigned_Lastnbits_range
    ((unsigned_last_nbits
        (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 + -0) + 1)
    32 ltac:(lia)) as Hq.
  change UINT_MAX with 4294967295.
  lia.
  }
  assert (Hsplit4 : gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_4).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_4; intros.
  pose proof (unsigned_Lastnbits_range
    ((unsigned_last_nbits
        (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 + -0) + 1)
    32 ltac:(lia)) as Hq.
  lia.
  }
  aggressive_pre_process.
  - exact (Hsplit1
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit2
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit3
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit4
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
Qed.

Lemma proof_of_gmp_udiv_qrnnd_preinv_return_wit_2 : gmp_udiv_qrnnd_preinv_return_wit_2.
Proof.
  assert (Hsplit1 : gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_1).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_1; intros.
  assert (Hql: unsigned_last_nbits (w0_value + nl_pre) 32 = w0_value + nl_pre) by
    (unfold unsigned_last_nbits in PreH3 |- *;
     change (2 ^ 32) with 4294967296 in *;
     assert (Hcond: (nl_pre + w0_value) mod 4294967296 >= w0_value) by
       (replace (nl_pre + w0_value) with (w0_value + nl_pre) by ring;
        exact PreH3);
     pose proof (Z_mod_add_uncarry nl_pre w0_value 4294967296
       ltac:(lia) ltac:(lia) ltac:(lia) Hcond) as Hunc;
     replace (w0_value + nl_pre) with (nl_pre + w0_value) by ring;
     symmetry; exact Hunc).
  assert (Hqh: unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 =
               w1_value + (nh_pre + 1)) by
    (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296;
     change UINT_MOD with 4294967296 in *;
     change (4294967296 ÷ 2) with 2147483648 in *; nia).
  assert (Hm1: unsigned_last_nbits (-1) 32 = 4294967295) by reflexivity.
  rewrite Hqh; rewrite Hm1.
  repeat rewrite unsigned_revolutive by lia.
  rewrite Z_land_m1_l.
  repeat rewrite Z.add_0_r; repeat rewrite Z.add_0_l.
  rewrite Hqh in *.
  repeat rewrite unsigned_revolutive in * by lia.
  rewrite Hql in PreH2.
  replace (w1_value + (nh_pre + 1) + 0) with
    (w1_value + (nh_pre + 1)) in PreH2 by ring.
  rewrite Hqh in PreH2.
  repeat rewrite unsigned_revolutive in PreH2 by lia.
  rewrite unsigned_last_nbits_sub_low_32.
  change UINT_MOD with 4294967296 in *.
  replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
    ((nh_pre * 4294967296 + nl_pre -
      (w1_value + nh_pre + 1 + 0) * d_pre) +
     (- nh_pre) * 4294967296) by ring.
  rewrite unsigned_last_nbits_add_mul_32.
  set (R := nh_pre * 4294967296 + nl_pre -
            (w1_value + nh_pre + 1 + 0) * d_pre) in *.
  rewrite unsigned_last_nbits_sub_low_32 in PreH2.
  replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
    (R + (- nh_pre) * 4294967296) in PreH2 by (subst R; ring).
  rewrite unsigned_last_nbits_add_mul_32 in PreH2.
  replace (w1_value + (nh_pre + 1) + 0) with
    (w1_value + (nh_pre + 1)) in PreH1 by ring.
  rewrite Hqh in PreH1.
  repeat rewrite unsigned_revolutive in PreH1 by lia.
  rewrite Z_land_m1_l in PreH1.
  replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
    (R + (- nh_pre) * 4294967296) in PreH1 by (subst R; ring).
  replace (unsigned_last_nbits (R + (- nh_pre) * 4294967296) 32) with
    (unsigned_last_nbits R 32) in PreH1 by
      (rewrite unsigned_last_nbits_add_mul_32; reflexivity).
  assert (Hql_range: 0 <= w0_value + nl_pre < 4294967296) by
    (pose proof (unsigned_Lastnbits_range (w0_value + nl_pre) 32
       ltac:(lia)) as Hr;
     rewrite Hql in Hr; lia).
  assert (Hdlo: 2147483648 <= d_pre) by
    (change (4294967296 ÷ 2) with 2147483648 in PreH21; lia).
  assert (Hc0: 0 = 0 \/ 0 = 1) by (left; reflexivity).
  assert (Hcarry0: w0_value + nl_pre =
                    0 * 4294967296 + (w0_value + nl_pre)) by ring.
  pose proof (udiv_preinv_error_range d_pre di_pre nh_pre nl_pre
    w0_value w1_value (w0_value + nl_pre) 0 Hdlo PreH22 PreH23 PreH24
    PreH17 PreH18 PreH19 PreH20 PreH7 PreH8 PreH4 PreH10
    (proj1 Hql_range) (proj2 Hql_range) Hc0 Hcarry0 PreH16 PreH25 PreH26)
    as HRrange.
  fold R in HRrange.
  set (e := 4294967296 ^ 2 - (di_pre + 4294967296) * d_pre).
  pose proof (udiv_preinv_e_bounds d_pre di_pre Hdlo PreH22 PreH23 PreH24
    PreH25 PreH26) as He.
  fold e in He.
  assert (Hformula:
    4294967296 * R =
    w0_value * d_pre + nl_pre * 4294967296 + nh_pre * e -
    d_pre * 4294967296) by (subst R e; nia).
  assert (HR_nonneg_le: R >= 0 -> R <= w0_value + nl_pre).
  { intro HRn.
    enough (4294967296 * R <= 4294967296 * (w0_value + nl_pre)) by nia.
    rewrite Hformula.
    replace (4294967296 * (w0_value + nl_pre)) with
      (w0_value * 4294967296 + nl_pre * 4294967296) by ring.
    nia. }
  assert (HRneg: R < 0).
  { destruct (Z_lt_ge_dec R 0) as [Hlt | Hge]; [exact Hlt|].
    pose proof (HR_nonneg_le Hge).
    assert (HuR_nonneg: unsigned_last_nbits R 32 = R).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296. lia. }
    rewrite HuR_nonneg in PreH2.
    lia. }
  assert (HuR: unsigned_last_nbits R 32 = R + 4294967296).
  { unfold unsigned_last_nbits.
    change (2 ^ 32) with 4294967296.
    symmetry.
    apply Z.mod_unique with (q := -1); [left; lia | ring]. }
  rewrite HuR.
  assert (HRd_range: 0 <= R + d_pre < 4294967296).
  { split.
    - enough (0 <= 4294967296 * (R + d_pre)) by nia.
      replace (4294967296 * (R + d_pre)) with
        (4294967296 * R + 4294967296 * d_pre) by ring.
      rewrite Hformula. nia.
    - lia. }
  replace (unsigned_last_nbits (R + 4294967296 + d_pre) 32) with
    (R + d_pre).
  2:{ replace (R + 4294967296 + d_pre) with
        ((R + d_pre) + 1 * 4294967296) by ring.
      rewrite unsigned_last_nbits_add_mul_32.
      symmetry.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      exact HRd_range. }
  subst R.
  replace (unsigned_last_nbits
    (unsigned_last_nbits (w1_value + (nh_pre + 1) + 4294967295) 32 + 1) 32)
    with (w1_value + nh_pre + 1).
  - ring.
  - assert (Hqrange0: 0 <= w1_value + (nh_pre + 1) < 4294967296).
    { pose proof (unsigned_Lastnbits_range (w1_value + (nh_pre + 1)) 32
        ltac:(lia)) as Hr.
      rewrite Hqh in Hr.
      change UINT_MOD with 4294967296 in *.
      lia. }
    replace (w1_value + (nh_pre + 1) + 4294967295) with
      ((w1_value + nh_pre) + 1 * 4294967296) by ring.
    rewrite unsigned_last_nbits_add_mul_32.
    replace (unsigned_last_nbits (w1_value + nh_pre) 32) with
      (w1_value + nh_pre).
    + symmetry.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia.
    + symmetry.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia.
  }
  assert (Hsplit2 : gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_2).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_2; intros.
  rewrite Z_land_m1_l.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (nl_pre -
        unsigned_last_nbits
          (unsigned_last_nbits
             (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 *
           d_pre) 32) 32 + d_pre) 32 ltac:(lia)) as Hr.
  change (2 ^ 32) with 4294967296 in Hr.
  change UINT_MOD with 4294967296 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  lia.
  }
  assert (Hsplit3 : gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_3).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_3; intros.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (unsigned_last_nbits
          (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 +
        unsigned_last_nbits (-1) 32) 32 + 1) 32 ltac:(lia)) as Hq.
  change UINT_MAX with 4294967295.
  change (2 ^ 32) with 4294967296 in Hq.
  lia.
  }
  assert (Hsplit4 : gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_4).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_4; intros.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (unsigned_last_nbits
          (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 +
        unsigned_last_nbits (-1) 32) 32 + 1) 32 ltac:(lia)) as Hq.
  lia.
  }
  aggressive_pre_process.
  - exact (Hsplit1
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit2
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit3
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit4
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
Qed.

Lemma proof_of_gmp_udiv_qrnnd_preinv_return_wit_3 : gmp_udiv_qrnnd_preinv_return_wit_3.
Proof.
  assert (Hsplit1 : gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_1).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_1; intros.
  assert (Hql: unsigned_last_nbits (w0_value + nl_pre) 32 =
               w0_value + nl_pre - 4294967296) by
    (unfold unsigned_last_nbits in PreH3 |- *;
     change (2 ^ 32) with 4294967296 in *;
     assert (Hcond: (nl_pre + w0_value) mod 4294967296 < w0_value) by
       (replace (nl_pre + w0_value) with (w0_value + nl_pre) by ring;
        exact PreH3);
     pose proof (Z_mod_add_carry nl_pre w0_value 4294967296
       ltac:(lia) ltac:(lia) ltac:(lia) Hcond) as Hcarry;
     replace (w0_value + nl_pre) with (nl_pre + w0_value) by ring;
     lia).
  assert (Hqh: unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 =
               w1_value + (nh_pre + 1)) by
    (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296;
     change UINT_MOD with 4294967296 in *;
     change (4294967296 ÷ 2) with 2147483648 in *; nia).
  rewrite Hqh; repeat rewrite unsigned_revolutive by lia.
  replace (Z.land (-0) d_pre) with 0 by reflexivity.
  repeat rewrite Z.add_0_r; repeat rewrite Z.add_0_l.
  rewrite Hqh in *.
  repeat rewrite unsigned_revolutive in * by lia.
  rewrite Hql in PreH2.
  replace (w1_value + (nh_pre + 1) + 1) with
    (w1_value + (nh_pre + 2)) in PreH2 by ring.
  assert (Hqbase_range: 0 <= w1_value + (nh_pre + 1) < 4294967296).
  { pose proof (unsigned_Lastnbits_range (w1_value + (nh_pre + 1)) 32
      ltac:(lia)) as Hr.
    rewrite Hqh in Hr.
    change (2 ^ 32) with 4294967296 in Hr.
    change UINT_MOD with 4294967296 in *.
    lia. }
  assert (Hq0_range: 0 <= w1_value + (nh_pre + 2) < 4294967296).
  { split; [lia|].
    destruct (Z_lt_ge_dec (w1_value + (nh_pre + 2)) 4294967296)
      as [Hlt | Hge]; [lia|].
    assert (Hq0eq: w1_value + (nh_pre + 2) = 4294967296) by lia.
    replace (unsigned_last_nbits (w1_value + (nh_pre + 2)) 32) with
      0 in PreH2.
    2:{ rewrite Hq0eq.
        unfold unsigned_last_nbits.
        change (2 ^ 32) with 4294967296.
        rewrite Z.mod_same by lia.
        reflexivity. }
    replace (unsigned_last_nbits (0 * d_pre) 32) with 0 in PreH2
      by reflexivity.
    replace (unsigned_last_nbits (nl_pre - 0) 32) with nl_pre in PreH2.
    2:{ replace (nl_pre - 0) with nl_pre by ring.
        symmetry.
        apply unsigned_last_nbits_eq.
        change (2 ^ 32) with 4294967296.
        change UINT_MOD with 4294967296 in *.
        lia. }
    change UINT_MOD with 4294967296 in *.
    lia. }
  replace (unsigned_last_nbits (w1_value + (nh_pre + 2)) 32) with
    (w1_value + (nh_pre + 2)) in PreH2 by
    (symmetry; apply unsigned_last_nbits_eq;
     change (2 ^ 32) with 4294967296; exact Hq0_range).
  replace (w1_value + (nh_pre + 2)) with
    (w1_value + (nh_pre + 1) + 1) in PreH2 by ring.
  replace (unsigned_last_nbits (w1_value + (nh_pre + 1) + 1) 32)
    with (w1_value + (nh_pre + 1) + 1) in PreH1 by
    (symmetry; apply unsigned_last_nbits_eq;
     change (2 ^ 32) with 4294967296; lia).
  replace (Z.land (-0) d_pre) with 0 in PreH1 by reflexivity.
  repeat rewrite Z.add_0_r in PreH1; repeat rewrite Z.add_0_l in PreH1.
  change UINT_MOD with 4294967296 in *.
  replace (unsigned_last_nbits (w1_value + (nh_pre + 1) + 1) 32)
    with (w1_value + (nh_pre + 1) + 1) by
    (symmetry; apply unsigned_last_nbits_eq;
     change (2 ^ 32) with 4294967296; lia).
  rewrite unsigned_last_nbits_sub_low_32.
  replace (nl_pre - (w1_value + (nh_pre + 1) + 1) * d_pre) with
    ((nh_pre * 4294967296 + nl_pre -
      (w1_value + nh_pre + 1 + 1) * d_pre) +
     (- nh_pre) * 4294967296) by ring.
  rewrite unsigned_last_nbits_add_mul_32.
  set (R := nh_pre * 4294967296 + nl_pre -
            (w1_value + nh_pre + 1 + 1) * d_pre) in *.
  rewrite unsigned_last_nbits_sub_low_32 in PreH1, PreH2.
  replace (nl_pre - (w1_value + (nh_pre + 1) + 1) * d_pre) with
    (R + (- nh_pre) * 4294967296) in PreH1 by (subst R; ring).
  replace (nl_pre - (w1_value + (nh_pre + 1) + 1) * d_pre) with
    (R + (- nh_pre) * 4294967296) in PreH2 by (subst R; ring).
  rewrite unsigned_last_nbits_add_mul_32 in PreH1, PreH2.
  assert (Hql_range: 0 <= w0_value + nl_pre - 4294967296 < 4294967296) by
    (pose proof (unsigned_Lastnbits_range (w0_value + nl_pre) 32
       ltac:(lia)) as Hr;
     rewrite Hql in Hr; change (2 ^ 32) with 4294967296 in Hr; lia).
  assert (Hdlo: 2147483648 <= d_pre) by
    (change (4294967296 ÷ 2) with 2147483648 in PreH21; lia).
  assert (Hc1: 1 = 0 \/ 1 = 1) by (right; reflexivity).
  assert (Hcarry1: w0_value + nl_pre =
                    1 * 4294967296 + (w0_value + nl_pre - 4294967296))
    by ring.
  pose proof (udiv_preinv_error_range d_pre di_pre nh_pre nl_pre
    w0_value w1_value (w0_value + nl_pre - 4294967296) 1
    Hdlo PreH22 PreH23 PreH24 PreH17 PreH18 PreH19 PreH20
    PreH7 PreH8 PreH4 PreH10 (proj1 Hql_range) (proj2 Hql_range)
    Hc1 Hcarry1 PreH16 PreH25 PreH26) as HRrange.
  fold R in HRrange.
  destruct (Z_lt_ge_dec R 0) as [HRneg | HRnonneg].
  - assert (HuR: unsigned_last_nbits R 32 = R + 4294967296).
    { unfold unsigned_last_nbits.
      change (2 ^ 32) with 4294967296.
      symmetry.
      apply Z.mod_unique with (q := -1); [left; lia | ring]. }
    rewrite HuR in PreH2.
    set (e := 4294967296 ^ 2 - (di_pre + 4294967296) * d_pre).
    pose proof (udiv_preinv_e_bounds d_pre di_pre Hdlo PreH22 PreH23
      PreH24 PreH25 PreH26) as He.
    fold e in He.
    assert (Hformula:
      4294967296 * R =
      w0_value * d_pre + nl_pre * 4294967296 + nh_pre * e -
      2 * d_pre * 4294967296) by (subst R e; nia).
    assert (Hgt: R + 4294967296 > w0_value + nl_pre - 4294967296).
    { enough (0 < 4294967296 *
                 (R + 4294967296 - (w0_value + nl_pre - 4294967296)))
        by nia.
      replace (4294967296 *
                 (R + 4294967296 - (w0_value + nl_pre - 4294967296))) with
        (4294967296 * R +
         4294967296 * (2 * 4294967296 - w0_value - nl_pre)) by ring.
      rewrite Hformula. nia. }
    lia.
  - assert (HuR: unsigned_last_nbits R 32 = R).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296. lia. }
    rewrite HuR in PreH1.
    rewrite HuR in PreH1.
    rewrite HuR.
    assert (Hqplus_range:
      0 <= w1_value + (nh_pre + 1) + 1 + 1 < 4294967296).
    { split; [lia|].
      assert (HNlt: nh_pre * 4294967296 + nl_pre <
                     d_pre * 4294967296) by nia.
      assert (HRge: R >= d_pre) by lia.
      subst R.
      apply (Zmult_lt_reg_r
        (w1_value + (nh_pre + 1) + 1 + 1) 4294967296 d_pre).
      + lia.
      + assert (Hleprod:
          (w1_value + (nh_pre + 1) + 1 + 1) * d_pre <=
          nh_pre * 4294967296 + nl_pre) by lia.
        assert (Hltprod:
          nh_pre * 4294967296 + nl_pre < 4294967296 * d_pre) by lia.
        lia. }
    rewrite unsigned_last_nbits_eq by
      (change (2 ^ 32) with 4294967296; exact Hqplus_range).
    subst R. ring.
  }
  assert (Hsplit2 : gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_2).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_2; intros.
  replace (Z.land (-0) d_pre) with 0 by reflexivity.
  repeat rewrite Z.add_0_r; repeat rewrite Z.add_0_l.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (nl_pre -
        unsigned_last_nbits
          (unsigned_last_nbits
             (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 1) 32 *
           d_pre) 32) 32) 32 ltac:(lia)) as Hr.
  change (2 ^ 32) with 4294967296 in Hr.
  change UINT_MOD with 4294967296 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  lia.
  }
  assert (Hsplit3 : gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_3).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_3; intros.
  pose proof (unsigned_Lastnbits_range
    (((unsigned_last_nbits
         (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 1) 32 + -0)
      + 1)) 32 ltac:(lia)) as Hq.
  change UINT_MAX with 4294967295.
  lia.
  }
  assert (Hsplit4 : gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_4).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_4; intros.
  pose proof (unsigned_Lastnbits_range
    (((unsigned_last_nbits
         (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 1) 32 + -0)
      + 1)) 32 ltac:(lia)) as Hq.
  lia.
  }
  aggressive_pre_process.
  - exact (Hsplit1
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit2
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit3
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit4
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
Qed.

Lemma proof_of_gmp_udiv_qrnnd_preinv_return_wit_4 : gmp_udiv_qrnnd_preinv_return_wit_4.
Proof.
  assert (Hsplit1 : gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_1).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_1; intros.
  assert (Hql: unsigned_last_nbits (w0_value + nl_pre) 32 =
               w0_value + nl_pre - 4294967296) by
    (unfold unsigned_last_nbits in PreH3 |- *;
     change (2 ^ 32) with 4294967296 in *;
     assert (Hcond: (nl_pre + w0_value) mod 4294967296 < w0_value) by
       (replace (nl_pre + w0_value) with (w0_value + nl_pre) by ring;
        exact PreH3);
     pose proof (Z_mod_add_carry nl_pre w0_value 4294967296
       ltac:(lia) ltac:(lia) ltac:(lia) Hcond) as Hcarry;
     replace (w0_value + nl_pre) with (nl_pre + w0_value) by ring;
     lia).
  assert (Hqh: unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 =
               w1_value + (nh_pre + 1)) by
    (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296;
     change UINT_MOD with 4294967296 in *;
     change (4294967296 ÷ 2) with 2147483648 in *; nia).
  assert (Hm1: unsigned_last_nbits (-1) 32 = 4294967295) by reflexivity.
  rewrite Hqh; rewrite Hm1.
  repeat rewrite unsigned_revolutive by lia.
  rewrite Z_land_m1_l.
  repeat rewrite Z.add_0_r; repeat rewrite Z.add_0_l.
  rewrite Hqh in *.
  repeat rewrite unsigned_revolutive in * by lia.
  rewrite Hql in PreH2.
  replace (w1_value + (nh_pre + 1) + 1) with
    (w1_value + (nh_pre + 2)) in PreH2 by ring.
  assert (Hqbase_range: 0 <= w1_value + (nh_pre + 1) < 4294967296).
  { pose proof (unsigned_Lastnbits_range (w1_value + (nh_pre + 1)) 32
      ltac:(lia)) as Hr.
    rewrite Hqh in Hr.
    change (2 ^ 32) with 4294967296 in Hr.
    change UINT_MOD with 4294967296 in *.
    lia. }
  assert (Hq0_range: 0 <= w1_value + (nh_pre + 2) < 4294967296).
  { split; [lia|].
    destruct (Z_lt_ge_dec (w1_value + (nh_pre + 2)) 4294967296)
      as [Hlt | Hge]; [lia|].
    assert (Hq0eq: w1_value + (nh_pre + 2) = 4294967296) by lia.
    replace (unsigned_last_nbits (w1_value + (nh_pre + 2)) 32) with
      0 in PreH2.
    2:{ rewrite Hq0eq.
        unfold unsigned_last_nbits.
        change (2 ^ 32) with 4294967296.
        rewrite Z.mod_same by lia.
        reflexivity. }
    replace (unsigned_last_nbits (0 * d_pre) 32) with 0 in PreH2
      by reflexivity.
    replace (unsigned_last_nbits (nl_pre - 0) 32) with nl_pre in PreH2.
    2:{ replace (nl_pre - 0) with nl_pre by ring.
        symmetry.
        apply unsigned_last_nbits_eq.
        change (2 ^ 32) with 4294967296.
        change UINT_MOD with 4294967296 in *.
        lia. }
    change UINT_MOD with 4294967296 in *.
    assert (Hq0_w0_le_d: w0_value <= d_pre).
    { set (e := 4294967296 ^ 2 - (di_pre + 4294967296) * d_pre).
      pose proof (udiv_preinv_e_bounds d_pre di_pre
        ltac:(change (4294967296 ÷ 2) with 2147483648 in PreH21; lia)
        PreH22 PreH23 PreH24 PreH25 PreH26) as He.
      fold e in He.
      subst e.
      nia. }
    assert (Hcarry_low: 4294967296 <= w0_value + nl_pre).
    { pose proof (unsigned_Lastnbits_range (w0_value + nl_pre) 32
        ltac:(lia)) as Hr.
      rewrite Hql in Hr.
      change (2 ^ 32) with 4294967296 in Hr.
      lia. }
    assert (Hpre1_simpl: unsigned_last_nbits (nl_pre + d_pre) 32 >= d_pre).
    { replace (w1_value + (nh_pre + 1) + 1) with 4294967296 in PreH1
        by lia.
      replace (unsigned_last_nbits 4294967296 32) with 0 in PreH1.
      2:{ unfold unsigned_last_nbits.
          change (2 ^ 32) with 4294967296.
          rewrite Z.mod_same by lia.
          reflexivity. }
      replace (unsigned_last_nbits (0 * d_pre) 32) with 0 in PreH1
        by reflexivity.
      replace (nl_pre - 0) with nl_pre in PreH1 by ring.
      replace (unsigned_last_nbits nl_pre 32) with nl_pre in PreH1.
      2:{ symmetry.
          apply unsigned_last_nbits_eq.
          change (2 ^ 32) with 4294967296.
          lia. }
      rewrite Z_land_m1_l in PreH1.
      exact PreH1. }
    assert (Hnl_d_lt: nl_pre + d_pre < 4294967296).
    { destruct (Z_lt_ge_dec (nl_pre + d_pre) 4294967296) as [Hlt | Hge2];
        [lia|].
      assert (Hsum_hi: nl_pre + d_pre < 2 * 4294967296) by lia.
      replace (unsigned_last_nbits (nl_pre + d_pre) 32) with
        (nl_pre + d_pre - 4294967296) in Hpre1_simpl.
      - lia.
      - unfold unsigned_last_nbits.
        change (2 ^ 32) with 4294967296.
        rewrite Z.mod_eq by lia.
        assert (Hdiv1: 1 = (nl_pre + d_pre) / 4294967296).
        { apply Z.div_unique with (r := nl_pre + d_pre - 4294967296);
            lia. }
        rewrite <- Hdiv1.
        ring. }
    lia. }
  replace (unsigned_last_nbits (w1_value + (nh_pre + 2)) 32) with
    (w1_value + (nh_pre + 2)) in PreH2 by
    (symmetry; apply unsigned_last_nbits_eq;
     change (2 ^ 32) with 4294967296; exact Hq0_range).
  replace (w1_value + (nh_pre + 2)) with
    (w1_value + (nh_pre + 1) + 1) in PreH2 by ring.
  replace (unsigned_last_nbits (w1_value + (nh_pre + 1) + 1) 32)
    with (w1_value + (nh_pre + 1) + 1) by
    (symmetry; apply unsigned_last_nbits_eq;
     change (2 ^ 32) with 4294967296; lia).
  rewrite unsigned_last_nbits_sub_low_32.
  change UINT_MOD with 4294967296 in *.
  replace (nl_pre - (w1_value + (nh_pre + 1) + 1) * d_pre) with
    ((nh_pre * 4294967296 + nl_pre -
      (w1_value + nh_pre + 1 + 1) * d_pre) +
     (- nh_pre) * 4294967296) by ring.
  rewrite unsigned_last_nbits_add_mul_32.
  set (R := nh_pre * 4294967296 + nl_pre -
            (w1_value + nh_pre + 1 + 1) * d_pre) in *.
  replace (unsigned_last_nbits (w1_value + (nh_pre + 1) + 1) 32)
    with (w1_value + (nh_pre + 1) + 1) in PreH1 by
    (symmetry; apply unsigned_last_nbits_eq;
     change (2 ^ 32) with 4294967296; lia).
  rewrite unsigned_last_nbits_sub_low_32 in PreH1, PreH2.
  replace (nl_pre - (w1_value + (nh_pre + 1) + 1) * d_pre) with
    (R + (- nh_pre) * 4294967296) in PreH1 by (subst R; ring).
  replace (nl_pre - (w1_value + (nh_pre + 1) + 1) * d_pre) with
    (R + (- nh_pre) * 4294967296) in PreH2 by (subst R; ring).
  rewrite unsigned_last_nbits_add_mul_32 in PreH1, PreH2.
  rewrite Z_land_m1_l in PreH1.
  assert (Hql_range: 0 <= w0_value + nl_pre - 4294967296 < 4294967296) by
    (pose proof (unsigned_Lastnbits_range (w0_value + nl_pre) 32
       ltac:(lia)) as Hr;
     rewrite Hql in Hr; change (2 ^ 32) with 4294967296 in Hr; lia).
  assert (Hdlo: 2147483648 <= d_pre) by
    (change (4294967296 ÷ 2) with 2147483648 in PreH21; lia).
  assert (Hc1: 1 = 0 \/ 1 = 1) by (right; reflexivity).
  assert (Hcarry1: w0_value + nl_pre =
                    1 * 4294967296 + (w0_value + nl_pre - 4294967296))
    by ring.
  pose proof (udiv_preinv_error_range d_pre di_pre nh_pre nl_pre
    w0_value w1_value (w0_value + nl_pre - 4294967296) 1
    Hdlo PreH22 PreH23 PreH24 PreH17 PreH18 PreH19 PreH20
    PreH7 PreH8 PreH4 PreH10 (proj1 Hql_range) (proj2 Hql_range)
    Hc1 Hcarry1 PreH16 PreH25 PreH26) as HRrange.
  fold R in HRrange.
  set (e := 4294967296 ^ 2 - (di_pre + 4294967296) * d_pre).
  pose proof (udiv_preinv_e_bounds d_pre di_pre Hdlo PreH22 PreH23
    PreH24 PreH25 PreH26) as He.
  fold e in He.
  assert (Hformula:
    4294967296 * R =
    w0_value * d_pre + nl_pre * 4294967296 + nh_pre * e -
    2 * d_pre * 4294967296) by (subst R e; nia).
  assert (Hcarry_low: 4294967296 <= w0_value + nl_pre).
  { pose proof (unsigned_Lastnbits_range (w0_value + nl_pre) 32
      ltac:(lia)) as Hr.
    rewrite Hql in Hr.
    change (2 ^ 32) with 4294967296 in Hr.
    lia. }
  assert (Hbase_nonneg:
    0 <= w0_value * d_pre + nl_pre * 4294967296 - d_pre * 4294967296).
  { replace (w0_value * d_pre + nl_pre * 4294967296 -
             d_pre * 4294967296) with
      ((nl_pre - (4294967296 - w0_value)) * 4294967296 +
       (4294967296 - w0_value) * (4294967296 - d_pre)) by ring.
    apply Z.add_nonneg_nonneg; apply Z.mul_nonneg_nonneg; lia. }
  assert (HRd_nonneg: 0 <= R + d_pre).
  { enough (0 <= 4294967296 * (R + d_pre)) by nia.
    replace (4294967296 * (R + d_pre)) with
      (4294967296 * R + 4294967296 * d_pre) by ring.
    rewrite Hformula.
    nia. }
  assert (HRnonneg: R >= 0).
  { destruct (Z_lt_ge_dec R 0) as [HRlt | HRge]; [|lia].
    assert (HuR_neg: unsigned_last_nbits R 32 = R + 4294967296).
    { unfold unsigned_last_nbits.
      change (2 ^ 32) with 4294967296.
      symmetry.
      apply Z.mod_unique with (q := -1); [left; lia | ring]. }
    rewrite HuR_neg in PreH1.
    replace (unsigned_last_nbits (R + 4294967296 + d_pre) 32) with
      (R + d_pre) in PreH1.
    2:{ replace (R + 4294967296 + d_pre) with
          ((R + d_pre) + 1 * 4294967296) by ring.
        rewrite unsigned_last_nbits_add_mul_32.
        symmetry.
        apply unsigned_last_nbits_eq.
        change (2 ^ 32) with 4294967296.
        lia. }
    lia. }
  assert (HRd_range: 0 <= R + d_pre < 4294967296).
  { split; [exact HRd_nonneg|].
    destruct (Z_lt_ge_dec (R + d_pre) 4294967296) as [Hlt | Hge_sum];
      [lia|].
    assert (HuR_nonneg: unsigned_last_nbits R 32 = R).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite HuR_nonneg in PreH1.
    replace (unsigned_last_nbits (R + d_pre) 32) with
      (R + d_pre - 4294967296) in PreH1.
    - lia.
    - unfold unsigned_last_nbits.
      change (2 ^ 32) with 4294967296.
      rewrite Z.mod_eq by lia.
      assert (Hdiv1: 1 = (R + d_pre) / 4294967296).
      { apply Z.div_unique with (r := R + d_pre - 4294967296); lia. }
      rewrite <- Hdiv1.
      ring. }
  assert (HuR: unsigned_last_nbits R 32 = R).
  { apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    lia. }
  rewrite HuR.
  replace (unsigned_last_nbits (R + d_pre) 32) with (R + d_pre).
  2:{ symmetry.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      exact HRd_range. }
  replace (unsigned_last_nbits
    (unsigned_last_nbits (w1_value + (nh_pre + 1) + 1 + 4294967295) 32 + 1) 32)
    with (w1_value + (nh_pre + 1) + 1).
  2:{ replace (w1_value + (nh_pre + 1) + 1 + 4294967295) with
        ((w1_value + (nh_pre + 1)) + 1 * 4294967296) by ring.
      rewrite unsigned_last_nbits_add_mul_32.
      rewrite Hqh.
      symmetry.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
  subst R. ring.
  }
  assert (Hsplit2 : gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_2).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_2; intros.
  rewrite Z_land_m1_l.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (nl_pre -
        unsigned_last_nbits
          (unsigned_last_nbits
             (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 1) 32 *
           d_pre) 32) 32 + d_pre) 32 ltac:(lia)) as Hr.
  change (2 ^ 32) with 4294967296 in Hr.
  change UINT_MOD with 4294967296 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  lia.
  }
  assert (Hsplit3 : gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_3).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_3; intros.
  match goal with
  | |- unsigned_last_nbits ?q 32 <= UINT_MAX =>
      pose proof (unsigned_Lastnbits_range q 32 ltac:(lia)) as Hq
  end.
  change UINT_MAX with 4294967295.
  change (2 ^ 32) with 4294967296 in Hq.
  lia.
  }
  assert (Hsplit4 : gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_4).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_4; intros.
  match goal with
  | |- 0 <= unsigned_last_nbits ?q 32 =>
      pose proof (unsigned_Lastnbits_range q 32 ltac:(lia)) as Hq
  end.
  change (2 ^ 32) with 4294967296 in Hq.
  lia.
  }
  aggressive_pre_process.
  - exact (Hsplit1
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit2
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit3
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit4
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
Qed.

Lemma proof_of_gmp_udiv_qrnnd_preinv_return_wit_5 : gmp_udiv_qrnnd_preinv_return_wit_5.
Proof.
  pre_process.
  Exists (unsigned_last_nbits
    (unsigned_last_nbits
       (nl_pre -
        unsigned_last_nbits
          (unsigned_last_nbits
             (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 *
           d_pre) 32) 32 + Z.land (-0) d_pre) 32).
  Exists (unsigned_last_nbits
    (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 + -0).
  split_pure_spatial.
  - cancel (q_pre # UInt |->
      (unsigned_last_nbits
         (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 + -0)).
    cancel (r_pre # UInt |->
      unsigned_last_nbits
        (unsigned_last_nbits
           (nl_pre -
            unsigned_last_nbits
              (unsigned_last_nbits
                 (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 *
               d_pre) 32) 32 + Z.land (-0) d_pre) 32).
  - split_pures.
    + dump_pre_spatial.
      pose proof (unsigned_Lastnbits_range
        (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32
        ltac:(lia)) as Hq.
      lia.
    + dump_pre_spatial.
      pose proof (unsigned_Lastnbits_range
        (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32
        ltac:(lia)) as Hq.
      change UINT_MAX with 4294967295.
      lia.
    + dump_pre_spatial.
      pose proof (unsigned_Lastnbits_range
        (unsigned_last_nbits
           (nl_pre -
            unsigned_last_nbits
              (unsigned_last_nbits
                 (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 *
               d_pre) 32) 32 + Z.land (-0) d_pre) 32 ltac:(lia)) as Hr.
      lia.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial.
      assert (Hql: unsigned_last_nbits (w0_value + nl_pre) 32 =
                   w0_value + nl_pre) by
        (unfold unsigned_last_nbits in PreH3 |- *;
         change (2 ^ 32) with 4294967296 in *;
         assert (Hcond: (nl_pre + w0_value) mod 4294967296 >= w0_value) by
           (replace (nl_pre + w0_value) with (w0_value + nl_pre) by ring;
            exact PreH3);
         pose proof (Z_mod_add_uncarry nl_pre w0_value 4294967296
           ltac:(lia) ltac:(lia) ltac:(lia) Hcond) as Hunc;
         replace (w0_value + nl_pre) with (nl_pre + w0_value) by ring;
         symmetry; exact Hunc).
      assert (Hqh: unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 =
                   w1_value + (nh_pre + 1)) by
        (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296;
         change UINT_MOD with 4294967296 in *;
         change (4294967296 ÷ 2) with 2147483648 in *; nia).
      rewrite Hqh; repeat rewrite unsigned_revolutive by lia.
      replace (Z.land (-0) d_pre) with 0 by reflexivity.
      repeat rewrite Z.add_0_r; repeat rewrite Z.add_0_l.
      rewrite Hqh in *.
      repeat rewrite unsigned_revolutive in * by lia.
      rewrite Hql in PreH2.
      replace (w1_value + (nh_pre + 1) + 0) with
        (w1_value + (nh_pre + 1)) in PreH2 by ring.
      rewrite Hqh in PreH2.
      repeat rewrite unsigned_revolutive in PreH2 by lia.
      replace (Z.land (-0) d_pre) with 0 in PreH1 by reflexivity.
      repeat rewrite Z.add_0_r in PreH1; repeat rewrite Z.add_0_l in PreH1.
      repeat rewrite unsigned_revolutive in PreH1 by lia.
      rewrite Hqh in PreH1.
      repeat rewrite unsigned_revolutive in PreH1 by lia.
      rewrite unsigned_last_nbits_sub_low_32.
      change UINT_MOD with 4294967296 in *.
      replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
        ((nh_pre * 4294967296 + nl_pre -
          (w1_value + nh_pre + 1 + 0) * d_pre) +
         (- nh_pre) * 4294967296) by ring.
      rewrite unsigned_last_nbits_add_mul_32.
      set (R := nh_pre * 4294967296 + nl_pre -
                (w1_value + nh_pre + 1 + 0) * d_pre) in *.
      rewrite unsigned_last_nbits_sub_low_32 in PreH1, PreH2.
      replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
        (R + (- nh_pre) * 4294967296) in PreH1 by (subst R; ring).
      replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
        (R + (- nh_pre) * 4294967296) in PreH2 by (subst R; ring).
      rewrite unsigned_last_nbits_add_mul_32 in PreH1, PreH2.
      assert (Hql_range: 0 <= w0_value + nl_pre < 4294967296) by
        (pose proof (unsigned_Lastnbits_range (w0_value + nl_pre) 32
           ltac:(lia)) as Hr;
         rewrite Hql in Hr; lia).
      assert (Hdlo: 2147483648 <= d_pre) by
        (change (4294967296 ÷ 2) with 2147483648 in PreH21; lia).
      assert (Hc0: 0 = 0 \/ 0 = 1) by (left; reflexivity).
      assert (Hcarry0: w0_value + nl_pre =
                        0 * 4294967296 + (w0_value + nl_pre)) by ring.
      pose proof (udiv_preinv_error_range d_pre di_pre nh_pre nl_pre
        w0_value w1_value (w0_value + nl_pre) 0 Hdlo PreH22 PreH23 PreH24
        PreH17 PreH18 PreH19 PreH20 PreH7 PreH8 PreH4 PreH10
        (proj1 Hql_range) (proj2 Hql_range) Hc0 Hcarry0 PreH16 PreH25 PreH26)
        as HRrange.
      fold R in HRrange.
      destruct (Z_lt_ge_dec R 0) as [HRneg | HRnonneg].
      * assert (HuR: unsigned_last_nbits R 32 = R + 4294967296).
        { unfold unsigned_last_nbits.
          change (2 ^ 32) with 4294967296.
          symmetry.
          apply Z.mod_unique with (q := -1); [left; lia | ring]. }
        rewrite HuR in PreH2.
        set (e := 4294967296 ^ 2 - (di_pre + 4294967296) * d_pre).
        pose proof (udiv_preinv_e_bounds d_pre di_pre Hdlo PreH22 PreH23
          PreH24 PreH25 PreH26) as He.
        fold e in He.
        assert (Hdi_eq: di_pre * d_pre =
          4294967296 ^ 2 - 4294967296 * d_pre - e) by (subst e; ring).
        assert (Hmul_d:
          (w1_value * 4294967296 + w0_value) * d_pre =
          nh_pre * di_pre * d_pre) by (rewrite PreH16; ring).
        assert (Hformula:
          4294967296 * R =
          w0_value * d_pre + nl_pre * 4294967296 + nh_pre * e -
          d_pre * 4294967296) by (subst R; nia).
        assert (Hgt: R + 4294967296 > w0_value + nl_pre).
        { enough (0 < 4294967296 * (R + 4294967296 -
                     (w0_value + nl_pre))) by nia.
          replace (4294967296 * (R + 4294967296 -
                    (w0_value + nl_pre))) with
            (4294967296 * R +
             4294967296 * (4294967296 - (w0_value + nl_pre))) by ring.
          rewrite Hformula. nia. }
        lia.
      * assert (HuR: unsigned_last_nbits R 32 = R).
        { apply unsigned_last_nbits_eq.
          change (2 ^ 32) with 4294967296. lia. }
        rewrite HuR in PreH1.
        rewrite HuR.
        nia.
Qed.

Lemma proof_of_gmp_udiv_qrnnd_preinv_return_wit_6 : gmp_udiv_qrnnd_preinv_return_wit_6.
Proof.
  assert (Hsplit1 : gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_1).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_1; intros.
  assert (Hql: unsigned_last_nbits (w0_value + nl_pre) 32 = w0_value + nl_pre) by
    (unfold unsigned_last_nbits in PreH3 |- *;
     change (2 ^ 32) with 4294967296 in *;
     assert (Hcond: (nl_pre + w0_value) mod 4294967296 >= w0_value) by
       (replace (nl_pre + w0_value) with (w0_value + nl_pre) by ring;
        exact PreH3);
     pose proof (Z_mod_add_uncarry nl_pre w0_value 4294967296
       ltac:(lia) ltac:(lia) ltac:(lia) Hcond) as Hunc;
     replace (w0_value + nl_pre) with (nl_pre + w0_value) by ring;
     symmetry; exact Hunc).
  assert (Hqh: unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 =
               w1_value + (nh_pre + 1)) by
    (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296;
     change UINT_MOD with 4294967296 in *;
     change (4294967296 ÷ 2) with 2147483648 in *; nia).
  assert (Hm1: unsigned_last_nbits (-1) 32 = 4294967295) by reflexivity.
  rewrite Hqh; rewrite Hm1.
  repeat rewrite unsigned_revolutive by lia.
  rewrite Z_land_m1_l.
  repeat rewrite Z.add_0_r; repeat rewrite Z.add_0_l.
  rewrite Hqh in *.
  repeat rewrite unsigned_revolutive in * by lia.
  rewrite Hql in PreH2.
  replace (w1_value + (nh_pre + 1) + 0) with
    (w1_value + (nh_pre + 1)) in PreH2 by ring.
  rewrite Hqh in PreH2.
  repeat rewrite unsigned_revolutive in PreH2 by lia.
  replace (w1_value + (nh_pre + 1) + 0) with
    (w1_value + (nh_pre + 1)) in PreH1 by ring.
  rewrite Hqh in PreH1.
  repeat rewrite unsigned_revolutive in PreH1 by lia.
  rewrite Z_land_m1_l in PreH1.
  change UINT_MOD with 4294967296 in *.
  rewrite unsigned_last_nbits_sub_low_32.
  replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
    ((nh_pre * 4294967296 + nl_pre -
      (w1_value + nh_pre + 1 + 0) * d_pre) +
     (- nh_pre) * 4294967296) by ring.
  rewrite unsigned_last_nbits_add_mul_32.
  set (R := nh_pre * 4294967296 + nl_pre -
            (w1_value + nh_pre + 1 + 0) * d_pre) in *.
  rewrite unsigned_last_nbits_sub_low_32 in PreH1, PreH2.
  replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
    (R + (- nh_pre) * 4294967296) in PreH1 by (subst R; ring).
  replace (nl_pre - (w1_value + (nh_pre + 1)) * d_pre) with
    (R + (- nh_pre) * 4294967296) in PreH2 by (subst R; ring).
  rewrite unsigned_last_nbits_add_mul_32 in PreH1, PreH2.
  assert (Hql_range: 0 <= w0_value + nl_pre < 4294967296) by
    (pose proof (unsigned_Lastnbits_range (w0_value + nl_pre) 32
       ltac:(lia)) as Hr;
     rewrite Hql in Hr; lia).
  assert (Hdlo: 2147483648 <= d_pre) by
    (change (4294967296 ÷ 2) with 2147483648 in PreH21; lia).
  assert (Hc0: 0 = 0 \/ 0 = 1) by (left; reflexivity).
  assert (Hcarry0: w0_value + nl_pre =
                    0 * 4294967296 + (w0_value + nl_pre)) by ring.
  pose proof (udiv_preinv_error_range d_pre di_pre nh_pre nl_pre
    w0_value w1_value (w0_value + nl_pre) 0 Hdlo PreH22 PreH23 PreH24
    PreH17 PreH18 PreH19 PreH20 PreH7 PreH8 PreH4 PreH10
    (proj1 Hql_range) (proj2 Hql_range) Hc0 Hcarry0 PreH16 PreH25 PreH26)
    as HRrange.
  fold R in HRrange.
  set (e := 4294967296 ^ 2 - (di_pre + 4294967296) * d_pre).
  pose proof (udiv_preinv_e_bounds d_pre di_pre Hdlo PreH22 PreH23 PreH24
    PreH25 PreH26) as He.
  fold e in He.
  assert (Hformula:
    4294967296 * R =
    w0_value * d_pre + nl_pre * 4294967296 + nh_pre * e -
    d_pre * 4294967296) by (subst R e; nia).
  assert (HR_nonneg_le: R >= 0 -> R <= w0_value + nl_pre).
  { intro HRn.
    enough (4294967296 * R <= 4294967296 * (w0_value + nl_pre)) by nia.
    rewrite Hformula.
    replace (4294967296 * (w0_value + nl_pre)) with
      (w0_value * 4294967296 + nl_pre * 4294967296) by ring.
    nia. }
  assert (HRneg: R < 0).
  { destruct (Z_lt_ge_dec R 0) as [Hlt | Hge]; [exact Hlt|].
    pose proof (HR_nonneg_le Hge).
    assert (HuR_nonneg: unsigned_last_nbits R 32 = R).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296. lia. }
    rewrite HuR_nonneg in PreH2.
    lia. }
  assert (HuR: unsigned_last_nbits R 32 = R + 4294967296).
  { unfold unsigned_last_nbits.
    change (2 ^ 32) with 4294967296.
    symmetry.
    apply Z.mod_unique with (q := -1); [left; lia | ring]. }
  rewrite HuR.
  assert (HRd_range: 0 <= R + d_pre < 4294967296).
  { split.
    - enough (0 <= 4294967296 * (R + d_pre)) by nia.
      replace (4294967296 * (R + d_pre)) with
        (4294967296 * R + 4294967296 * d_pre) by ring.
      rewrite Hformula. nia.
    - lia. }
  replace (unsigned_last_nbits (R + 4294967296 + d_pre) 32) with
    (R + d_pre).
  2:{ replace (R + 4294967296 + d_pre) with
        ((R + d_pre) + 1 * 4294967296) by ring.
      rewrite unsigned_last_nbits_add_mul_32.
      symmetry.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      exact HRd_range. }
  replace (unsigned_last_nbits (w1_value + (nh_pre + 1) + 4294967295) 32)
    with (w1_value + nh_pre).
  2:{ replace (w1_value + (nh_pre + 1) + 4294967295) with
        ((w1_value + nh_pre) + 1 * 4294967296) by ring.
      rewrite unsigned_last_nbits_add_mul_32.
      symmetry.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      change UINT_MOD with 4294967296 in *.
      pose proof (unsigned_Lastnbits_range (w1_value + (nh_pre + 1)) 32
        ltac:(lia)) as Hqrange.
      rewrite Hqh in Hqrange.
      change (2 ^ 32) with 4294967296 in Hqrange.
      change UINT_MOD with 4294967296 in *.
      lia. }
  subst R. ring.
  }
  assert (Hsplit2 : gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_2).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_2; intros.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (nl_pre -
        unsigned_last_nbits
          (unsigned_last_nbits
             (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 *
           d_pre) 32) 32 + Z.land (-1) d_pre) 32 ltac:(lia)) as Hr.
  lia.
  }
  assert (Hsplit3 : gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_3).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_3; intros.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 +
     unsigned_last_nbits (-1) 32) 32 ltac:(lia)) as Hq.
  change UINT_MAX with 4294967295.
  change (2 ^ 32) with 4294967296 in Hq.
  lia.
  }
  assert (Hsplit4 : gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_4).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_4; intros.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 0) 32 +
     unsigned_last_nbits (-1) 32) 32 ltac:(lia)) as Hq.
  lia.
  }
  aggressive_pre_process.
  - exact (Hsplit1
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit2
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit3
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit4
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
Qed.

Lemma proof_of_gmp_udiv_qrnnd_preinv_return_wit_7 : gmp_udiv_qrnnd_preinv_return_wit_7.
Proof.
  assert (Hsplit1 : gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_1).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_1; intros.
  assert (Hql: unsigned_last_nbits (w0_value + nl_pre) 32 =
               w0_value + nl_pre - 4294967296) by
    (unfold unsigned_last_nbits in PreH3 |- *;
     change (2 ^ 32) with 4294967296 in *;
     assert (Hcond: (nl_pre + w0_value) mod 4294967296 < w0_value) by
       (replace (nl_pre + w0_value) with (w0_value + nl_pre) by ring;
        exact PreH3);
     pose proof (Z_mod_add_carry nl_pre w0_value 4294967296
       ltac:(lia) ltac:(lia) ltac:(lia) Hcond) as Hcarry;
     replace (w0_value + nl_pre) with (nl_pre + w0_value) by ring;
     lia).
  assert (Hqh: unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 =
               w1_value + (nh_pre + 1)) by
    (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296;
     change UINT_MOD with 4294967296 in *;
     change (4294967296 ÷ 2) with 2147483648 in *; nia).
  rewrite Hqh; repeat rewrite unsigned_revolutive by lia.
  replace (Z.land (-0) d_pre) with 0 by reflexivity.
  repeat rewrite Z.add_0_r; repeat rewrite Z.add_0_l.
  rewrite Hqh in *.
  repeat rewrite unsigned_revolutive in * by lia.
  rewrite Hql in PreH2.
  replace (w1_value + (nh_pre + 1) + 1) with
    (w1_value + (nh_pre + 2)) in PreH2 by ring.
  assert (Hqbase_range: 0 <= w1_value + (nh_pre + 1) < 4294967296).
  { pose proof (unsigned_Lastnbits_range (w1_value + (nh_pre + 1)) 32
      ltac:(lia)) as Hr.
    rewrite Hqh in Hr.
    change (2 ^ 32) with 4294967296 in Hr.
    change UINT_MOD with 4294967296 in *.
    lia. }
  assert (Hq0_range: 0 <= w1_value + (nh_pre + 2) < 4294967296).
  { split; [lia|].
    destruct (Z_lt_ge_dec (w1_value + (nh_pre + 2)) 4294967296)
      as [Hlt | Hge]; [lia|].
    assert (Hq0eq: w1_value + (nh_pre + 2) = 4294967296) by lia.
    replace (unsigned_last_nbits (w1_value + (nh_pre + 2)) 32) with
      0 in PreH2.
    2:{ rewrite Hq0eq.
        unfold unsigned_last_nbits.
        change (2 ^ 32) with 4294967296.
        rewrite Z.mod_same by lia.
        reflexivity. }
    replace (unsigned_last_nbits (0 * d_pre) 32) with 0 in PreH2
      by reflexivity.
    replace (unsigned_last_nbits (nl_pre - 0) 32) with nl_pre in PreH2.
    2:{ replace (nl_pre - 0) with nl_pre by ring.
        symmetry.
        apply unsigned_last_nbits_eq.
        change (2 ^ 32) with 4294967296.
        change UINT_MOD with 4294967296 in *.
        lia. }
    change UINT_MOD with 4294967296 in *.
    lia. }
  replace (unsigned_last_nbits (w1_value + (nh_pre + 2)) 32) with
    (w1_value + (nh_pre + 2)) in PreH2 by
    (symmetry; apply unsigned_last_nbits_eq;
     change (2 ^ 32) with 4294967296; exact Hq0_range).
  replace (w1_value + (nh_pre + 2)) with
    (w1_value + (nh_pre + 1) + 1) in PreH2 by ring.
  replace (unsigned_last_nbits (w1_value + (nh_pre + 1) + 1) 32)
    with (w1_value + (nh_pre + 1) + 1) by
    (symmetry; apply unsigned_last_nbits_eq;
     change (2 ^ 32) with 4294967296; lia).
  rewrite unsigned_last_nbits_sub_low_32.
  change UINT_MOD with 4294967296 in *.
  replace (nl_pre - (w1_value + (nh_pre + 1) + 1) * d_pre) with
    ((nh_pre * 4294967296 + nl_pre -
      (w1_value + nh_pre + 1 + 1) * d_pre) +
     (- nh_pre) * 4294967296) by ring.
  rewrite unsigned_last_nbits_add_mul_32.
  set (R := nh_pre * 4294967296 + nl_pre -
            (w1_value + nh_pre + 1 + 1) * d_pre) in *.
  rewrite unsigned_last_nbits_sub_low_32 in PreH2.
  replace (nl_pre - (w1_value + (nh_pre + 1) + 1) * d_pre) with
    (R + (- nh_pre) * 4294967296) in PreH2 by (subst R; ring).
  rewrite unsigned_last_nbits_add_mul_32 in PreH2.
  assert (Hql_range: 0 <= w0_value + nl_pre - 4294967296 < 4294967296) by
    (pose proof (unsigned_Lastnbits_range (w0_value + nl_pre) 32
       ltac:(lia)) as Hr;
     rewrite Hql in Hr; change (2 ^ 32) with 4294967296 in Hr; lia).
  assert (Hdlo: 2147483648 <= d_pre) by
    (change (4294967296 ÷ 2) with 2147483648 in PreH21; lia).
  assert (Hc1: 1 = 0 \/ 1 = 1) by (right; reflexivity).
  assert (Hcarry1: w0_value + nl_pre =
                    1 * 4294967296 + (w0_value + nl_pre - 4294967296))
    by ring.
  pose proof (udiv_preinv_error_range d_pre di_pre nh_pre nl_pre
    w0_value w1_value (w0_value + nl_pre - 4294967296) 1
    Hdlo PreH22 PreH23 PreH24 PreH17 PreH18 PreH19 PreH20
    PreH7 PreH8 PreH4 PreH10 (proj1 Hql_range) (proj2 Hql_range)
    Hc1 Hcarry1 PreH16 PreH25 PreH26) as HRrange.
  fold R in HRrange.
  destruct (Z_lt_ge_dec R 0) as [HRneg | HRnonneg].
  - assert (HuR: unsigned_last_nbits R 32 = R + 4294967296).
    { unfold unsigned_last_nbits.
      change (2 ^ 32) with 4294967296.
      symmetry.
      apply Z.mod_unique with (q := -1); [left; lia | ring]. }
    rewrite HuR in PreH2.
    set (e := 4294967296 ^ 2 - (di_pre + 4294967296) * d_pre).
    pose proof (udiv_preinv_e_bounds d_pre di_pre Hdlo PreH22 PreH23
      PreH24 PreH25 PreH26) as He.
    fold e in He.
    assert (Hformula:
      4294967296 * R =
      w0_value * d_pre + nl_pre * 4294967296 + nh_pre * e -
      2 * d_pre * 4294967296) by (subst R e; nia).
    assert (Hgt: R + 4294967296 > w0_value + nl_pre - 4294967296).
    { enough (0 < 4294967296 *
                 (R + 4294967296 - (w0_value + nl_pre - 4294967296)))
        by nia.
      replace (4294967296 *
                 (R + 4294967296 - (w0_value + nl_pre - 4294967296))) with
        (4294967296 * R +
         4294967296 * (2 * 4294967296 - w0_value - nl_pre)) by ring.
      rewrite Hformula. nia. }
    lia.
  - assert (HuR: unsigned_last_nbits R 32 = R).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296. lia. }
    rewrite HuR.
    subst R. ring.
  }
  assert (Hsplit2 : gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_2).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_2; intros.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (nl_pre -
        unsigned_last_nbits
          (unsigned_last_nbits
             (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 1) 32 *
           d_pre) 32) 32 + Z.land (-0) d_pre) 32 ltac:(lia)) as Hr.
  lia.
  }
  assert (Hsplit3 : gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_3).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_3; intros.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 1) 32
    ltac:(lia)) as Hq.
  change (2 ^ 32) with 4294967296 in Hq.
  change UINT_MAX with 4294967295.
  lia.
  }
  assert (Hsplit4 : gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_4).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_4; intros.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 1) 32
    ltac:(lia)) as Hq.
  change (2 ^ 32) with 4294967296 in Hq.
  lia.
  }
  aggressive_pre_process.
  - exact (Hsplit1
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit2
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit3
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
  - exact (Hsplit4
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
Qed.

Lemma proof_of_gmp_udiv_qrnnd_preinv_return_wit_8 : gmp_udiv_qrnnd_preinv_return_wit_8.
Proof.
  assert (Hsplit1 : gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_1).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_1; intros.
  assert (Hql: unsigned_last_nbits (w0_value + nl_pre) 32 =
               w0_value + nl_pre - 4294967296) by
    (unfold unsigned_last_nbits in PreH3 |- *;
     change (2 ^ 32) with 4294967296 in *;
     assert (Hcond: (nl_pre + w0_value) mod 4294967296 < w0_value) by
       (replace (nl_pre + w0_value) with (w0_value + nl_pre) by ring;
        exact PreH3);
     pose proof (Z_mod_add_carry nl_pre w0_value 4294967296
       ltac:(lia) ltac:(lia) ltac:(lia) Hcond) as Hcarry;
     replace (w0_value + nl_pre) with (nl_pre + w0_value) by ring;
     lia).
  assert (Hqh: unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 =
               w1_value + (nh_pre + 1)) by
    (apply unsigned_last_nbits_eq; change (2 ^ 32) with 4294967296;
     change UINT_MOD with 4294967296 in *;
     change (4294967296 ÷ 2) with 2147483648 in *; nia).
  assert (Hm1: unsigned_last_nbits (-1) 32 = 4294967295) by reflexivity.
  rewrite Hqh; rewrite Hm1.
  repeat rewrite unsigned_revolutive by lia.
  rewrite Z_land_m1_l.
  repeat rewrite Z.add_0_r; repeat rewrite Z.add_0_l.
  rewrite Hqh in *.
  repeat rewrite unsigned_revolutive in * by lia.
  rewrite Hql in PreH2.
  replace (w1_value + (nh_pre + 1) + 1) with
    (w1_value + (nh_pre + 2)) in PreH2 by ring.
  assert (Hqbase_range: 0 <= w1_value + (nh_pre + 1) < 4294967296).
  { pose proof (unsigned_Lastnbits_range (w1_value + (nh_pre + 1)) 32
      ltac:(lia)) as Hr.
    rewrite Hqh in Hr.
    change (2 ^ 32) with 4294967296 in Hr.
    change UINT_MOD with 4294967296 in *.
    lia. }
  change UINT_MOD with 4294967296 in *.
  set (qinc := w1_value + (nh_pre + 1) + 1) in *.
  replace (w1_value + (nh_pre + 2)) with qinc in PreH2 by (subst qinc; ring).
  assert (Hqinc_range: 1 <= qinc <= 4294967296) by (subst qinc; lia).
  assert (Hqout:
    unsigned_last_nbits (unsigned_last_nbits qinc 32 + 4294967295) 32 =
    qinc - 1).
  { destruct (Z_lt_ge_dec qinc 4294967296) as [Hlt | Hge].
    - replace (unsigned_last_nbits qinc 32) with qinc.
      2:{ symmetry; apply unsigned_last_nbits_eq.
          change (2 ^ 32) with 4294967296; lia. }
      replace (qinc + 4294967295) with
        ((qinc - 1) + 1 * 4294967296) by ring.
      rewrite unsigned_last_nbits_add_mul_32.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296; lia.
    - assert (Hqe: qinc = 4294967296) by lia.
      rewrite Hqe.
      replace (unsigned_last_nbits 4294967296 32) with 0.
      2:{ unfold unsigned_last_nbits.
          change (2 ^ 32) with 4294967296.
          rewrite Z.mod_same by lia; reflexivity. }
      change (unsigned_last_nbits (0 + 4294967295) 32) with 4294967295.
      lia. }
  rewrite Hqout.
  set (R := nh_pre * 4294967296 + nl_pre - qinc * d_pre) in *.
  assert (Hrr0:
    unsigned_last_nbits
      (nl_pre - unsigned_last_nbits (unsigned_last_nbits qinc 32 * d_pre) 32)
      32 = unsigned_last_nbits R 32).
  { rewrite unsigned_last_nbits_sub_low_32.
    destruct (Z_lt_ge_dec qinc 4294967296) as [Hlt | Hge].
    - replace (unsigned_last_nbits qinc 32) with qinc.
      2:{ symmetry; apply unsigned_last_nbits_eq.
          change (2 ^ 32) with 4294967296; lia. }
      replace (nl_pre - qinc * d_pre) with
        (R + (- nh_pre) * 4294967296) by (subst R; ring).
      rewrite unsigned_last_nbits_add_mul_32.
      reflexivity.
    - assert (Hqe: qinc = 4294967296) by lia.
      replace (unsigned_last_nbits qinc 32) with 0.
      2:{ rewrite Hqe; unfold unsigned_last_nbits.
          change (2 ^ 32) with 4294967296.
          rewrite Z.mod_same by lia; reflexivity. }
      replace (nl_pre - 0 * d_pre) with
        (R + (d_pre - nh_pre) * 4294967296) by (subst R; rewrite Hqe; ring).
      rewrite unsigned_last_nbits_add_mul_32.
      reflexivity. }
  rewrite Hrr0 in PreH1, PreH2 |- *.
  rewrite Z_land_m1_l in PreH1.
  assert (Hql_range: 0 <= w0_value + nl_pre - 4294967296 < 4294967296) by
    (pose proof (unsigned_Lastnbits_range (w0_value + nl_pre) 32
       ltac:(lia)) as Hr;
     rewrite Hql in Hr; change (2 ^ 32) with 4294967296 in Hr; lia).
  assert (Hdlo: 2147483648 <= d_pre) by
    (change (4294967296 ÷ 2) with 2147483648 in PreH21; lia).
  assert (Hc1: 1 = 0 \/ 1 = 1) by (right; reflexivity).
  assert (Hcarry1: w0_value + nl_pre =
                    1 * 4294967296 + (w0_value + nl_pre - 4294967296))
    by ring.
  pose proof (udiv_preinv_error_range d_pre di_pre nh_pre nl_pre
    w0_value w1_value (w0_value + nl_pre - 4294967296) 1
    Hdlo PreH22 PreH23 PreH24 PreH17 PreH18 PreH19 PreH20
    PreH7 PreH8 PreH4 PreH10 (proj1 Hql_range) (proj2 Hql_range)
    Hc1 Hcarry1 PreH16 PreH25 PreH26) as HRrange.
  replace (nh_pre * 4294967296 + nl_pre -
           (w1_value + nh_pre + 1 + 1) * d_pre) with R in HRrange
    by (subst R qinc; ring).
  set (e := 4294967296 ^ 2 - (di_pre + 4294967296) * d_pre).
  pose proof (udiv_preinv_e_bounds d_pre di_pre Hdlo PreH22 PreH23
    PreH24 PreH25 PreH26) as He.
  fold e in He.
  assert (Hformula:
    4294967296 * R =
    w0_value * d_pre + nl_pre * 4294967296 + nh_pre * e -
    2 * d_pre * 4294967296) by (subst R qinc e; nia).
  assert (Hcarry_low: 4294967296 <= w0_value + nl_pre).
  { pose proof (unsigned_Lastnbits_range (w0_value + nl_pre) 32
      ltac:(lia)) as Hr.
    rewrite Hql in Hr.
    change (2 ^ 32) with 4294967296 in Hr.
    lia. }
  assert (Hbase_nonneg:
    0 <= w0_value * d_pre + nl_pre * 4294967296 - d_pre * 4294967296).
  { replace (w0_value * d_pre + nl_pre * 4294967296 -
             d_pre * 4294967296) with
      ((nl_pre - (4294967296 - w0_value)) * 4294967296 +
       (4294967296 - w0_value) * (4294967296 - d_pre)) by ring.
    apply Z.add_nonneg_nonneg; apply Z.mul_nonneg_nonneg; lia. }
  assert (HRd_nonneg: 0 <= R + d_pre).
  { enough (0 <= 4294967296 * (R + d_pre)) by nia.
    replace (4294967296 * (R + d_pre)) with
      (4294967296 * R + 4294967296 * d_pre) by ring.
    rewrite Hformula.
    replace (w0_value * d_pre + nl_pre * 4294967296 + nh_pre * e -
      2 * d_pre * 4294967296 + 4294967296 * d_pre) with
      ((w0_value * d_pre + nl_pre * 4294967296 - d_pre * 4294967296) +
       nh_pre * e) by ring.
    apply Z.add_nonneg_nonneg.
    - exact Hbase_nonneg.
    - apply Z.mul_nonneg_nonneg; lia. }
  assert (HRneg: R < 0).
  { destruct (Z_lt_ge_dec R 0) as [HRlt | HRge]; [exact HRlt|].
    assert (HuR_nonneg: unsigned_last_nbits R 32 = R).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    rewrite HuR_nonneg in PreH1, PreH2.
    assert (HRd_geB: 4294967296 <= R + d_pre).
    { destruct (Z_lt_ge_dec (R + d_pre) 4294967296) as [Hlt | HgeB];
        [|lia].
      replace (unsigned_last_nbits (R + d_pre) 32) with
        (R + d_pre) in PreH1.
      - lia.
      - symmetry; apply unsigned_last_nbits_eq.
        change (2 ^ 32) with 4294967296.
        lia. }
    exfalso.
    apply (udiv_preinv_wit8_R_nonneg_contra d_pre nh_pre nl_pre w0_value R e);
      try lia; try exact Hformula; try exact Hcarry_low. }
  assert (HuR: unsigned_last_nbits R 32 = R + 4294967296).
  { unfold unsigned_last_nbits.
    change (2 ^ 32) with 4294967296.
    symmetry.
    apply Z.mod_unique with (q := -1); [left; lia | ring]. }
  rewrite HuR.
  assert (HRd_range: 0 <= R + d_pre < 4294967296) by lia.
  replace (unsigned_last_nbits (R + 4294967296 + d_pre) 32) with
    (R + d_pre).
  2:{ replace (R + 4294967296 + d_pre) with
        ((R + d_pre) + 1 * 4294967296) by ring.
      rewrite unsigned_last_nbits_add_mul_32.
      symmetry.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      exact HRd_range. }
  subst R qinc.
  ring.
  }
  assert (Hsplit2 : gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_2).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_2; intros.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (nl_pre -
        unsigned_last_nbits
          (unsigned_last_nbits
             (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 1) 32 *
           d_pre) 32) 32 + Z.land (-1) d_pre) 32 ltac:(lia)) as Hr.
  lia.
  }
  assert (Hsplit3 : gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_3).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_3; intros.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 1) 32 +
     unsigned_last_nbits (-1) 32) 32 ltac:(lia)) as Hq.
  change (2 ^ 32) with 4294967296 in Hq.
  change UINT_MAX with 4294967295.
  lia.
  }
  assert (Hsplit4 : gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_4).
  {
  unfold gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_4; intros.
  pose proof (unsigned_Lastnbits_range
    (unsigned_last_nbits
       (unsigned_last_nbits (w1_value + (nh_pre + 1)) 32 + 1) 32 +
     unsigned_last_nbits (-1) 32) 32 ltac:(lia)) as Hq.
  lia.
  }
  unfold gmp_udiv_qrnnd_preinv_return_wit_8.
  right.
  intros.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    + apply derivable1s_coq_prop_r.
      exact (Hsplit1
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
    + apply derivable1s_coq_prop_r.
      exact (Hsplit2
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
    + apply derivable1s_coq_prop_r.
      exact (Hsplit3
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
    + apply derivable1s_coq_prop_r.
      exact (Hsplit4
        di_pre d_pre nl_pre nh_pre w0_value w1_value
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
        PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26).
Qed.
