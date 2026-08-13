Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
From SumLib Require Import SumLib.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import CommonAssertion Mem SeparationLogic IntLib.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import GmpAux. Import Aux.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import GmpNumber.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.
Import naive_C_Rules.
Local Open Scope sac.
Import SumLib.Sum.

Definition mpz_mul_sign (sign a b: Z) : Prop :=
  (sign = 0 /\ same_sign a b) \/
  (sign = 1 /\ ((a < 0 /\ b > 0) \/ (a > 0 /\ b < 0))).

Definition mpz_mul_fits (a b: Z): Prop :=
  forall size_a size_b,
    is_compact_Z UINT_MOD (Z.abs a) size_a ->
    is_compact_Z UINT_MOD (Z.abs b) size_b ->
    size_a + size_b <= INT_MAX.

Definition mpz_mul_2exp_fits (z bits: Z): Prop :=
  forall size,
    z <> 0 ->
    is_compact_Z UINT_MOD (Z.abs z) size ->
    size + bits ÷ 32 + (if Z.eq_dec (bits % 32) 0 then 0 else 1) <= INT_MAX.

Definition mpz_one_limb_headroom (z: Z): Prop :=
  forall size,
    is_compact_Z UINT_MOD (Z.abs z) size ->
    size + 1 <= INT_MAX.

Lemma compact_size_unique_nonnegative :
  forall n size1 size2,
    0 <= n ->
    is_compact_Z UINT_MOD n size1 ->
    is_compact_Z UINT_MOD n size2 ->
    size1 = size2.
Proof.
  intros n size1 size2 Hn Hc1 Hc2.
  destruct (Z.eq_dec n 0) as [Hn0 | Hnpos].
  - subst n.
    pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos 0 size1 Hc1)
      as [Hs1 Hb1].
    pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos 0 size2 Hc2)
      as [Hs2 Hb2].
    assert (size1 = 0) as Hsize1.
    {
      destruct Hb1 as [[? ?] | [? [? ?]]]; try lia.
      pose proof (Z.pow_pos_nonneg UINT_MOD (size1 - 1) UINT_MOD_pos ltac:(lia)).
      lia.
    }
    assert (size2 = 0) as Hsize2.
    {
      destruct Hb2 as [[? ?] | [? [? ?]]]; try lia.
      pose proof (Z.pow_pos_nonneg UINT_MOD (size2 - 1) UINT_MOD_pos ltac:(lia)).
      lia.
    }
    lia.
  - apply (is_compact_Z_same_value_size_eq n size1 size2); try assumption.
    lia.
Qed.

Lemma two_compact_arrays_total_limb_bound :
  forall p1 p2 n1 n2 s1 s2,
    mpd_store_Z_compact UINT_MOD p1 n1 s1 **
    mpd_store_Z_compact UINT_MOD p2 n2 s2 |--
    “ s1 + s2 <= 1073741824 ”.
Proof.
  intros.
  sep_apply (mpd_store_Z_compact_align4 UINT_MOD p1 n1 s1).
  sep_apply (mpd_store_Z_compact_align4 UINT_MOD p2 n2 s2).
  sep_apply (store_align4_merge s1 s2).
  prop_apply (store_align4_n_valid (s1 + s2)).
  Intros.
  dump_pre_spatial.
  rewrite addr_max_unsigned_eq_int in H.
  change Int.max_unsigned with 4294967295 in H.
  replace (4294967295 / 4 + 1) with 1073741824 in H by reflexivity.
  exact H.
Qed.

Lemma two_store_Z_imply_mpz_mul_fits :
  forall x y a b,
    store_Z x a ** store_Z y b |-- “ mpz_mul_fits a b ”.
Proof.
  intros x y a b.
  unfold store_Z.
  Intros p1 actual1 cap1 p2 actual2 cap2.
  prop_apply (mpd_store_Z_to_is_compact_Z p1 (Zabs a) (Zabs actual1)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z p2 (Zabs b) (Zabs actual2)).
  Intros.
  prop_apply (two_compact_arrays_total_limb_bound
    p1 p2 (Zabs a) (Zabs b) (Zabs actual1) (Zabs actual2)).
  Intros.
  unfold mpz_mul_fits.
  dump_pre_spatial.
  intros size_a size_b Hca Hcb.
  assert (size_a = Zabs actual1).
  { eapply compact_size_unique_nonnegative; eauto; apply Z.abs_nonneg. }
  assert (size_b = Zabs actual2).
  { eapply compact_size_unique_nonnegative; eauto; apply Z.abs_nonneg. }
  subst size_a size_b.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma one_store_Z_implies_headroom :
  forall x z,
    store_Z x z |-- “ mpz_one_limb_headroom z ”.
Proof.
  intros x z.
  unfold store_Z.
  Intros ptr actual cap.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z) (Zabs actual)).
  Intros.
  prop_apply (mpd_store_Z_compact_range UINT_MOD
    ptr (Zabs z) (Zabs actual)).
  Intros.
  unfold mpz_one_limb_headroom.
  dump_pre_spatial.
  intros size Hcompact.
  assert (size = Zabs actual).
  { eapply compact_size_unique_nonnegative; eauto; apply Z.abs_nonneg. }
  subst size.
  change Int.max_unsigned with 4294967295 in H2.
  assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.
  rewrite Hcalc in H2.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma two_store_Z_fields_total_limb_bound :
  forall x1 x2 p1 p2 a b size1 size2 cap1 cap2,
    Zabs size1 <= cap1 ->
    same_sign a size1 ->
    Zabs size2 <= cap2 ->
    same_sign b size2 ->
    &(x1 # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size1 **
    UIntArray.undef_seg p1 (Zabs size1) cap1 **
    mpd_store_Z_compact UINT_MOD p1 (Zabs a) (Zabs size1) **
    &(x1 # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> p1 **
    &(x1 # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap1 **
    &(x2 # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size2 **
    UIntArray.undef_seg p2 (Zabs size2) cap2 **
    mpd_store_Z_compact UINT_MOD p2 (Zabs b) (Zabs size2) **
    &(x2 # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> p2 **
    &(x2 # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap2
    |-- “ Zabs size1 + Zabs size2 <= INT_MAX ”.
Proof.
  intros x1 x2 p1 p2 a b size1 size2 cap1 cap2
    Hcap1 Hsign1 Hcap2 Hsign2.
  prop_apply (mpd_store_Z_to_is_compact_Z p1 (Zabs a) (Zabs size1)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z p2 (Zabs b) (Zabs size2)).
  Intros.
  sep_apply
    (store_Z_from_fields x1 p1 size1 cap1 a Hcap1 Hsign1).
  sep_apply
    (store_Z_from_fields x2 p2 size2 cap2 b Hcap2 Hsign2).
  prop_apply (two_store_Z_imply_mpz_mul_fits x1 x2 a b).
  Intros.
  match goal with
  | Hfit : mpz_mul_fits a b,
    Hcompact1 : is_compact_Z UINT_MOD (Zabs a) (Zabs size1),
    Hcompact2 : is_compact_Z UINT_MOD (Zabs b) (Zabs size2) |- _ =>
      pose proof
        (Hfit (Zabs size1) (Zabs size2) Hcompact1 Hcompact2)
        as Hbound
  end.
  dump_pre_spatial; exact Hbound.
Qed.

Lemma mpz_one_limb_headroom_mul_2exp_fits :
  forall z bits final,
    z > 0 ->
    bits >= 0 ->
    final = 2 ^ bits * z ->
    mpz_one_limb_headroom final ->
    mpz_mul_2exp_fits z bits.
Proof.
  intros z bits final Hz Hbits Hfinal Hhead.
  unfold mpz_mul_2exp_fits.
  intros size _ Hcompact.
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.div_mod bits 32 ltac:(lia)) as Hdivmod.
  set (q := bits / 32) in *.
  set (r := bits mod 32) in *.
  assert (Hqr : bits = q * 32 + r) by lia.
  assert (Hq : q >= 0).
  { subst q. pose proof (Z.div_pos bits 32 ltac:(lia) ltac:(lia)). lia. }
  assert (Hr : 0 <= r < 32).
  { subst r. apply Z.mod_pos_bound. lia. }
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Z.abs z) size Hcompact)
    as [Hsize Hzbounds].
  assert (Hzabs : Z.abs z = z) by lia.
  rewrite Hzabs in Hzbounds, Hcompact.
  destruct Hzbounds as [[Hsize0 Hz0] | [Hsizepos [Hzlo Hzhi]]]; [lia|].
  assert (Hfinal_pos : final > 0).
  { rewrite Hfinal.
    pose proof (Z.pow_pos_nonneg 2 bits ltac:(lia) ltac:(lia)).
    nia. }
  assert (Hfinal_abs : Z.abs final = final) by lia.
  destruct (Z.eq_dec r 0) as [Hr0 | Hrne].
  - assert (Hbitsq : bits = 32 * q) by lia.
    assert (Hpowbits : 2 ^ bits = UINT_MOD ^ q).
    { unfold UINT_MOD. rewrite Hbitsq. rewrite Z.pow_mul_r by lia. reflexivity. }
    assert (Hfinal_compact : is_compact_Z UINT_MOD (Z.abs final) (size + q)).
    { rewrite Hfinal_abs.
      apply (is_compact_Z_from_bounds UINT_MOD UINT_MOD_pos).
      + lia.
      + right. split; [lia|].
        rewrite Hfinal, Hpowbits.
        split.
        * replace (size + q - 1) with ((size - 1) + q) by lia.
          rewrite Z.pow_add_r by lia.
          nia.
        * rewrite Z.pow_add_r by lia.
          nia.
    }
    specialize (Hhead (size + q) Hfinal_compact).
    lia.
  - assert (Hrpos : r > 0) by lia.
    assert (Hbitsqr : bits = 32 * q + r) by lia.
    assert (Hpowbits : 2 ^ bits = UINT_MOD ^ q * 2 ^ r).
    { unfold UINT_MOD. rewrite Hbitsqr.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_mul_r by lia.
      reflexivity. }
    set (alloc := size + q + 1).
    assert (Halloc_pos : alloc > 1) by (subst alloc; lia).
    destruct (Z_lt_ge_dec final (UINT_MOD ^ (alloc - 1))) as [Hsmall | Hlarge].
    + assert (Hcompact_final : is_compact_Z UINT_MOD (Z.abs final) (alloc - 1)).
      { rewrite Hfinal_abs.
        apply (is_compact_Z_from_bounds UINT_MOD UINT_MOD_pos).
        - lia.
        - right. split; [lia|].
          split.
          + subst alloc.
            rewrite Hfinal, Hpowbits.
            replace (size + q + 1 - 1 - 1) with ((size - 1) + q) by lia.
            rewrite Z.pow_add_r by lia.
            assert (1 <= 2 ^ r)
              by (pose proof (Z.pow_pos_nonneg 2 r ltac:(lia) ltac:(lia)); lia).
            nia.
          + exact Hsmall.
      }
      specialize (Hhead (alloc - 1) Hcompact_final).
      subst alloc.
      lia.
    + assert (Hcompact_final : is_compact_Z UINT_MOD (Z.abs final) alloc).
      { rewrite Hfinal_abs.
        apply (is_compact_Z_from_bounds UINT_MOD UINT_MOD_pos).
        - lia.
        - right. split; [lia|].
          split.
          + lia.
          + subst alloc.
            rewrite Hfinal, Hpowbits.
            assert (H2r : 2 ^ r < UINT_MOD).
            { unfold UINT_MOD.
              replace 4294967296 with (2 ^ 32) by reflexivity.
              apply Z.pow_lt_mono_r; lia. }
            assert (H2r_nonneg : 0 <= 2 ^ r).
            { pose proof (Z.pow_pos_nonneg 2 r ltac:(lia) ltac:(lia)); lia. }
            assert (Hsize_pow_nonneg : 0 <= UINT_MOD ^ size).
            { pose proof (Z.pow_pos_nonneg UINT_MOD size UINT_MOD_pos ltac:(lia)); lia. }
            assert (Hq_pow_pos : 0 < UINT_MOD ^ q).
            { apply Z.pow_pos_nonneg; lia. }
            replace (UINT_MOD ^ (size + q + 1))
              with (UINT_MOD ^ size * UINT_MOD ^ q * UINT_MOD).
            2:{
              replace UINT_MOD with (UINT_MOD ^ 1) at 3
                by (rewrite Z.pow_1_r; reflexivity).
              rewrite <- Z.pow_add_r by lia.
              rewrite <- Z.pow_add_r by lia.
              reflexivity.
            }
            replace (UINT_MOD ^ q * 2 ^ r * z)
              with (UINT_MOD ^ q * (2 ^ r * z)) by ring.
            replace (UINT_MOD ^ size * UINT_MOD ^ q * UINT_MOD)
              with (UINT_MOD ^ q * (UINT_MOD * UINT_MOD ^ size)) by ring.
            apply (proj1 (Z.mul_lt_mono_pos_l (UINT_MOD ^ q)
                           (2 ^ r * z)
                           (UINT_MOD * UINT_MOD ^ size) Hq_pow_pos)).
            apply Z.mul_lt_mono_nonneg; lia.
      }
      specialize (Hhead alloc Hcompact_final).
      subst alloc.
      lia.
Qed.

Lemma same_sign_mul_same_abs:
  forall z1 z2 s1 s2 sz,
    same_sign z1 s1 ->
    same_sign z2 s2 ->
    same_sign s1 s2 ->
    0 < Zabs z1 ->
    0 < Zabs z2 ->
    0 < sz ->
    same_sign (z1 * z2) sz.
Proof.
  intros z1 z2 s1 s2 sz Hz1 Hz2 Hs Hz1abs Hz2abs Hsz.
  assert (Hz1nz: z1 <> 0) by (intro Hz; subst; simpl in Hz1abs; lia).
  assert (Hz2nz: z2 <> 0) by (intro Hz; subst; simpl in Hz2abs; lia).
  unfold same_sign in *.
  destruct Hs as [[Hs1 Hs2] | [Hs1 Hs2]];
  destruct Hz1 as [[Hz1s Hs1'] | [Hz1s Hs1']];
  destruct Hz2 as [[Hz2s Hs2'] | [Hz2s Hs2']];
  try lia; left; split; nia.
Qed.

Lemma same_sign_mul_pos_neg_abs:
  forall z1 z2 s1 s2 sz,
    same_sign z1 s1 ->
    same_sign z2 s2 ->
    s1 > 0 ->
    s2 < 0 ->
    0 < Zabs z1 ->
    0 < Zabs z2 ->
    0 < sz ->
    same_sign (z1 * z2) (- sz).
Proof.
  intros z1 z2 s1 s2 sz Hz1 Hz2 Hs1 Hs2 Hz1abs Hz2abs Hsz.
  assert (Hz1nz: z1 <> 0) by (intro Hz; subst; simpl in Hz1abs; lia).
  assert (Hz2nz: z2 <> 0) by (intro Hz; subst; simpl in Hz2abs; lia).
  unfold same_sign in *.
  destruct Hz1 as [[Hz1s Hs1'] | [Hz1s Hs1']];
  destruct Hz2 as [[Hz2s Hs2'] | [Hz2s Hs2']];
  try lia; right; split; nia.
Qed.

Lemma same_sign_mul_neg_pos_abs:
  forall z1 z2 s1 s2 sz,
    same_sign z1 s1 ->
    same_sign z2 s2 ->
    s1 < 0 ->
    s2 > 0 ->
    0 < Zabs z1 ->
    0 < Zabs z2 ->
    0 < sz ->
    same_sign (z1 * z2) (- sz).
Proof.
  intros z1 z2 s1 s2 sz Hz1 Hz2 Hs1 Hs2 Hz1abs Hz2abs Hsz.
  assert (Hz1nz: z1 <> 0) by (intro Hz; subst; simpl in Hz1abs; lia).
  assert (Hz2nz: z2 <> 0) by (intro Hz; subst; simpl in Hz2abs; lia).
  unfold same_sign in *.
  destruct Hz1 as [[Hz1s Hs1'] | [Hz1s Hs1']];
  destruct Hz2 as [[Hz2s Hs2'] | [Hz2s Hs2']];
  try lia; right; split; nia.
Qed.

Lemma is_compact_Z_mul_high_zero:
  forall (l1 l2 l_out: list Z) un vn,
    un > 0 ->
    vn > 0 ->
    Zlength l1 = un ->
    Zlength l2 = vn ->
    Zlength l_out = un + vn ->
    list_within_bound UINT_MOD l1 ->
    list_within_bound UINT_MOD l2 ->
    list_within_bound UINT_MOD l_out ->
    list_to_Z UINT_MOD l_out =
      list_to_Z UINT_MOD l1 * list_to_Z UINT_MOD l2 ->
    last l1 1 >= 1 ->
    last l2 1 >= 1 ->
    Znth (un + vn - 1) l_out 0 = 0 ->
    is_compact_Z UINT_MOD (list_to_Z UINT_MOD l_out) (un + vn - 1).
Proof.
  intros l1 l2 l_out un vn Hun Hvn Hlen1 Hlen2 Hlenout
         Hbound1 Hbound2 Hboundout Hval Hlast1 Hlast2 Hhigh.
  apply is_compact_Z_from_bounds; [unfold UINT_MOD; lia | lia |].
  right.
  split; [lia |].
  pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1 Hbound1 Hlast1)
    as [Hlo1 Hhi1].
  pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2 Hbound2 Hlast2)
    as [Hlo2 Hhi2].
  pose proof (list_within_bound_sublist UINT_MOD l_out 0 (un + vn - 1)
    ltac:(lia) ltac:(lia) Hboundout) as Hprefix_bound.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos
    (sublist 0 (un + vn - 1) l_out) Hprefix_bound) as Hprefix_hi.
  rewrite Zlength_sublist in Hprefix_hi by lia.
  replace (un + vn - 1 - 0) with (un + vn - 1) in Hprefix_hi by lia.
  assert (Hprefix_val:
            list_to_Z UINT_MOD l_out =
            list_to_Z UINT_MOD (sublist 0 (un + vn - 1) l_out)).
  {
    symmetry.
    apply list_to_Z_high_zero_prefix; lia.
  }
  split.
  - rewrite Hval.
    replace (un + vn - 1 - 1) with ((un - 1) + (vn - 1)) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Hlen1 in Hlo1.
    rewrite Hlen2 in Hlo2.
    apply Z.mul_le_mono_nonneg; try (apply Z.pow_nonneg; unfold UINT_MOD; lia); lia.
  - rewrite Hprefix_val.
    destruct Hprefix_hi; lia.
Qed.

Lemma mpz_mul_fits_nonzero_left_headroom_right :
  forall a b,
    a <> 0 ->
    mpz_mul_fits a b ->
    mpz_one_limb_headroom b.
Proof.
  intros a b Ha Hfits.
  unfold mpz_one_limb_headroom.
  intros size_b Hb.
  destruct (is_compact_Z_exists_nonneg (Z.abs a) (Z.abs_nonneg a))
    as [size_a Ha_compact].
  specialize (Hfits size_a size_b Ha_compact Hb).
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Z.abs a) size_a Ha_compact)
    as [_ [[Hsize_zero Habs_zero] | [Hsize_pos _]]].
  - assert (a = 0) by lia. contradiction.
  - lia.
Qed.

Lemma mpz_one_limb_headroom_mono_nonneg :
  forall a b,
    0 <= a <= b ->
    mpz_one_limb_headroom b ->
    mpz_one_limb_headroom a.
Proof.
  intros a b Hab Hhead.
  unfold mpz_one_limb_headroom in *.
  intros size_a Hca.
  assert (Ha_nonneg : 0 <= a) by lia.
  assert (Hb_nonneg : 0 <= b) by lia.
  replace (Z.abs a) with a in Hca by lia.
  destruct (is_compact_Z_exists_nonneg b Hb_nonneg) as [size_b Hcb].
  specialize (Hhead size_b ltac:(replace (Z.abs b) with b by lia; exact Hcb)).
  destruct (Z.eq_dec a 0) as [Ha0 | Ha0].
  - subst a.
    pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos 0 size_a Hca)
      as [_ [[Hsize Hz] | [Hsize [Hlo Hhi]]]].
    + lia.
    + pose proof (Z.pow_pos_nonneg UINT_MOD (size_a - 1) UINT_MOD_pos ltac:(lia)).
      lia.
  - destruct (Z.eq_dec a b) as [Hab_eq | Hab_neq].
    + subst b.
      assert (Hsize_eq : size_a = size_b).
      { eapply is_compact_Z_same_value_size_eq; eauto; lia. }
      lia.
    + assert (Hb_gt : b > a) by lia.
      pose proof (is_compact_Z_mono_size b a size_b size_a Hb_gt Hcb Hca) as Hle.
      lia.
Qed.

Lemma mpz_one_limb_headroom_gcd_l :
  forall a b,
    a <> 0 ->
    mpz_one_limb_headroom a ->
    mpz_one_limb_headroom (Z.gcd a b).
Proof.
  intros a b Ha Hhead.
  apply (mpz_one_limb_headroom_mono_nonneg (Z.gcd a b) (Z.abs a)).
  - split.
    + apply Z.gcd_nonneg.
    + rewrite <- Z.gcd_abs_l.
      apply Z.divide_pos_le.
      * apply Z.abs_pos. exact Ha.
      * apply Z.gcd_divide_l.
  - unfold mpz_one_limb_headroom in *.
    intros size Hcompact.
    rewrite Z.abs_eq in Hcompact by apply Z.abs_nonneg.
    apply Hhead.
    exact Hcompact.
Qed.
