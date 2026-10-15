Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.
Definition Pre (l r : Z) : Prop :=
  (* Stated explicitly in the P055 solver Require, which therefore omits the
     Pre(...) call: 1 <= l <= r /\ r <= Z.pow 10 18. *)
  True.
Definition Spec (l r out : Z) : Prop :=
  max_value_of_subset Z.le (fun v => exists a b, l <= a <= b /\ b <= r /\ v = Z.lxor a b) (fun x => x) out.

Definition HighestBitScan (l r x b : Z) : Prop :=
  x = Z.lxor l r /\
  forall k, b < k <= 63 -> Z.land (Z.shiftr x k) 1 = 0.

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Lemma lxor_u64_bound__bit_scan_transitions :
  forall x y,
    0 <= x < 2 ^ 64 ->
    0 <= y < 2 ^ 64 ->
    Z.lxor x y <= 2 ^ 64 - 1.
Proof.
  intros x y Hx Hy.
  destruct (Z.eq_dec x 0) as [-> | Hxnz].
  { rewrite Z.lxor_0_l. lia. }
  destruct (Z.eq_dec y 0) as [-> | Hynz].
  { rewrite Z.lxor_0_r. lia. }
  assert (Hxor : Z.lxor x y < 2 ^ 64).
  { apply Z.log2_lt_cancel.
    rewrite Z.log2_pow2 by lia.
    eapply Z.le_lt_trans.
    - apply Z.log2_lxor; lia.
    - apply Z.max_lub_lt.
      + apply (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia))); lia.
      + apply (proj1 (Z.log2_lt_pow2 y 64 ltac:(lia))); lia. }
  lia.
Qed.
Lemma highest_bit_scan_zero_step__bit_scan_transitions :
  forall l r x b,
    0 < x < 2 ^ 64 ->
    0 <= b <= 63 ->
    HighestBitScan l r x b ->
    Z.land (Z.shiftr x b) 1 = 0 ->
    0 < b /\ HighestBitScan l r x (b - 1).
Proof.
  intros l r x b Hx Hb Hscan Hbit.
  destruct Hscan as [Hxor Hscan].
  assert (Hbpos : 0 < b).
  { destruct (Z.eq_dec b 0) as [-> | Hbnz]; [|lia].
    assert (Hlog_nonneg : 0 <= Z.log2 x) by (apply Z.log2_nonneg).
    assert (Hlog_lt : Z.log2 x < 64).
    { apply (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia))); lia. }
    assert (Hzero : Z.land (Z.shiftr x (Z.log2 x)) 1 = 0).
    { destruct (Z.eq_dec (Z.log2 x) 0) as [Heq | Hneq].
      - rewrite Heq. exact Hbit.
      - apply Hscan. lia. }
    assert (Hzero_bit := f_equal (fun z => Z.testbit z 0) Hzero).
    change (Z.testbit (Z.land (Z.shiftr x (Z.log2 x)) 1) 0 = false)
      in Hzero_bit.
    rewrite Z.land_spec in Hzero_bit.
    rewrite Z.shiftr_spec in Hzero_bit by lia.
    replace (0 + Z.log2 x) with (Z.log2 x) in Hzero_bit by lia.
    rewrite Z.bit_log2 in Hzero_bit by lia.
    discriminate. }
  split; [exact Hbpos|].
  split; [exact Hxor|].
  intros k Hk.
  destruct (Z.eq_dec k b) as [-> | Hneq].
  - exact Hbit.
  - apply Hscan. lia.
Qed.
Lemma land_shiftr_one_bit__interval_maximum :
  forall x b, 0 <= b ->
    Z.land (Z.shiftr x b) 1 = Z.b2z (Z.testbit x b).
Proof.
  intros x b Hb.
  replace 1 with (Z.ones 1) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  symmetry. apply Z.testbit_spec'; lia.
Qed.
Lemma boundary_xor__interval_maximum :
  forall c b, 0 <= b ->
    Z.lxor (c * 2 ^ (b + 1) + 2 ^ b - 1)
           (c * 2 ^ (b + 1) + 2 ^ b) =
    2 ^ (b + 1) - 1.
Proof.
  intros c b Hb.
  set (h := c * 2 ^ (b + 1)).
  assert (Hhones : Z.land h (Z.ones b) = 0).
  { rewrite Z.land_ones by lia.
    unfold h.
    replace (c * 2 ^ (b + 1)) with ((2 * c) * 2 ^ b).
    2: { rewrite Z.pow_add_r by lia.
         change (2 ^ 1) with 2. ring. }
    apply Z.mod_mul. apply Z.pow_nonzero; lia. }
  assert (Hhpow : Z.land h (2 ^ b) = 0).
  { apply Z.bits_inj'. intros m Hm.
    rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec b m) as [->|Hne].
    - rewrite Z.pow2_bits_true by lia.
      unfold h.
      rewrite Z.mul_pow2_bits_low by lia.
      reflexivity.
    - rewrite Z.pow2_bits_false by lia.
      destruct (Z.testbit h m); reflexivity. }
  assert (Honespow : Z.land (Z.ones b) (2 ^ b) = 0).
  { apply Z.bits_inj'. intros m Hm.
    rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec b m) as [->|Hne].
    - rewrite Z.pow2_bits_true by lia.
      rewrite Z.ones_spec_high by lia.
      reflexivity.
    - rewrite Z.pow2_bits_false by lia.
      destruct (Z.testbit (Z.ones b) m); reflexivity. }
  assert (HA : h + Z.ones b = Z.lxor h (Z.ones b)).
  { apply Z.add_nocarry_lxor; exact Hhones. }
  assert (HB : h + 2 ^ b = Z.lxor h (2 ^ b)).
  { apply Z.add_nocarry_lxor; exact Hhpow. }
  assert (HC : Z.ones b + 2 ^ b = Z.ones (b + 1)).
  { rewrite Z.ones_add with (n := 1) (m := b) by lia.
    change (Z.ones 1) with 1. ring. }
  assert (Hcancel :
    Z.lxor (Z.lxor h (Z.ones b)) (Z.lxor h (2 ^ b)) =
    Z.lxor (Z.ones b) (2 ^ b)).
  { apply Z.bits_inj'. intros m Hm.
    repeat rewrite Z.lxor_spec.
    destruct (Z.testbit h m), (Z.testbit (Z.ones b) m),
             (Z.testbit (2 ^ b) m); reflexivity. }
  fold h.
  replace (h + 2 ^ b - 1) with (h + Z.ones b).
  2: { rewrite Z.ones_equiv. unfold Z.pred. ring. }
  rewrite HA, HB, Hcancel.
  rewrite <- Z.add_nocarry_lxor by exact Honespow.
  rewrite HC, Z.ones_equiv.
  unfold Z.pred. reflexivity.
Qed.
Lemma interval_max_xor_from_scan__interval_maximum :
  forall l r x b,
    0 <= l <= r ->
    0 <= x <= 18446744073709551615 ->
    0 <= b <= 63 ->
    HighestBitScan l r x b ->
    Z.land (Z.shiftr x b) 1 <> 0 ->
    Spec l r (2 ^ (b + 1) - 1).
Proof.
  intros l r x b Hlr Hx Hb Hscan Hbit.
  destruct Hscan as [Hxdef Habove].
  assert (Hxb : Z.testbit x b = true).
  { rewrite land_shiftr_one_bit__interval_maximum in Hbit by lia.
    destruct (Z.testbit x b); simpl in *; congruence. }
  assert (Hxmod : x mod 2 ^ 64 = x).
  { apply Z.mod_small. split.
    - lia.
    - pose proof (Z.pow_pos_nonneg 2 64). lia. }
  assert (Hxshift : Z.shiftr x (b + 1) = 0).
  { apply Z.bits_inj'. intros m Hm.
    rewrite Z.shiftr_spec by lia.
    rewrite Z.bits_0.
    replace (m + (b + 1)) with (b + 1 + m) by lia.
    destruct (Z_le_dec (b + 1 + m) 63) as [Hle|Hgt].
    - specialize (Habove (b + 1 + m) ltac:(lia)).
      rewrite land_shiftr_one_bit__interval_maximum in Habove by lia.
      destruct (Z.testbit x (b + 1 + m)) eqn:Hxm.
      + simpl in Habove. lia.
      + reflexivity.
    - rewrite <- Hxmod.
      apply Z.mod_pow2_bits_high. lia. }
  assert (Hlrshift : Z.shiftr l (b + 1) = Z.shiftr r (b + 1)).
  { apply Z.lxor_eq.
    rewrite <- Z.shiftr_lxor at 1.
    rewrite <- Hxdef. exact Hxshift. }
  set (p := 2 ^ b).
  set (q := 2 ^ (b + 1)).
  set (c := Z.shiftr l (b + 1)).
  assert (Hp : 0 < p) by (unfold p; apply Z.pow_pos_nonneg; lia).
  assert (Hq : 0 < q) by (unfold q; apply Z.pow_pos_nonneg; lia).
  assert (Hqp : q = 2 * p).
  { unfold q, p. rewrite Z.pow_add_r by lia.
    change (2 ^ 1) with 2. ring. }
  assert (Hlc : l / q = c).
  { unfold c, q. symmetry. apply Z.shiftr_div_pow2; lia. }
  assert (Hrc : r / q = c).
  { unfold c, q. rewrite Hlrshift.
    symmetry. apply Z.shiftr_div_pow2; lia. }
  assert (Hbits : xorb (Z.testbit l b) (Z.testbit r b) = true).
  { rewrite Hxdef, Z.lxor_spec in Hxb. exact Hxb. }
  assert (Hldiv : l / p = 2 * c + Z.b2z (Z.testbit l b)).
  { pose proof (Z.div2_odd (Z.shiftr l b)) as Hdec.
    rewrite <- Z.testbit_odd in Hdec.
    rewrite Z.div2_div in Hdec.
    replace 2 with (2 ^ 1) in Hdec by reflexivity.
    rewrite <- Z.shiftr_div_pow2 in Hdec by lia.
    rewrite Z.shiftr_shiftr in Hdec by lia.
    replace (b + 1) with (b + 1) in Hdec by lia.
    fold c in Hdec.
    unfold p. rewrite <- Z.shiftr_div_pow2 by lia. exact Hdec. }
  assert (Hrdiv : r / p = 2 * c + Z.b2z (Z.testbit r b)).
  { pose proof (Z.div2_odd (Z.shiftr r b)) as Hdec.
    rewrite <- Z.testbit_odd in Hdec.
    rewrite Z.div2_div in Hdec.
    replace 2 with (2 ^ 1) in Hdec by reflexivity.
    rewrite <- Z.shiftr_div_pow2 in Hdec by lia.
    rewrite Z.shiftr_shiftr in Hdec by lia.
    rewrite <- Hlrshift in Hdec.
    fold c in Hdec.
    unfold p. rewrite <- Z.shiftr_div_pow2 by lia. exact Hdec. }
  assert (Hbitlr : Z.testbit l b = false /\ Z.testbit r b = true).
  { destruct (Z.testbit l b) eqn:Hlbit;
      destruct (Z.testbit r b) eqn:Hrbit; simpl in Hbits; try discriminate.
    - exfalso.
      pose proof (Z.div_le_mono l r p Hp (proj2 Hlr)) as Hmono.
      rewrite Hldiv, Hrdiv in Hmono. simpl in Hmono. lia.
    - split; reflexivity. }
  destruct Hbitlr as [Hlbit Hrbit].
  rewrite Hlbit in Hldiv.
  replace (Z.b2z false) with 0 in Hldiv by reflexivity.
  rewrite Hrbit in Hrdiv.
  replace (Z.b2z true) with 1 in Hrdiv by reflexivity.
  set (a0 := c * q + p - 1).
  set (b0 := c * q + p).
  assert (Hla0 : l <= a0).
  { pose proof (Z.div_mod l p ltac:(lia)) as Hdecomp.
    pose proof (Z.mod_pos_bound l p Hp) as Hrem.
    rewrite Hldiv in Hdecomp.
    unfold a0. rewrite Hqp.
    nia. }
  assert (Hb0r : b0 <= r).
  { pose proof (Z.div_mod r p ltac:(lia)) as Hdecomp.
    pose proof (Z.mod_pos_bound r p Hp) as Hrem.
    rewrite Hrdiv in Hdecomp.
    unfold b0. rewrite Hqp.
    nia. }
  assert (Ha0b0 : a0 <= b0) by (unfold a0, b0; lia).
  assert (Hxor0 : Z.lxor a0 b0 = q - 1).
  { unfold a0, b0, q.
    apply boundary_xor__interval_maximum; lia. }
  assert (Hbound : forall a d,
    l <= a <= d -> d <= r -> Z.lxor a d <= q - 1).
  { intros a d Had Hdr.
    assert (Ha_nonneg : 0 <= a) by lia.
    assert (Hd_nonneg : 0 <= d) by lia.
    assert (Hac : a / q = c).
    { pose proof (Z.div_le_mono l a q Hq (proj1 Had)).
      pose proof (Z.div_le_mono a r q Hq ltac:(lia)). lia. }
    assert (Hdc : d / q = c).
    { pose proof (Z.div_le_mono l d q Hq ltac:(lia)).
      pose proof (Z.div_le_mono d r q Hq Hdr). lia. }
    assert (Hxor_nonneg : 0 <= Z.lxor a d).
    { apply Z.lxor_nonneg. split; lia. }
    assert (Hxor_shift : Z.shiftr (Z.lxor a d) (b + 1) = 0).
    { rewrite Z.shiftr_lxor.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      fold q. rewrite Hac, Hdc. apply Z.lxor_nilpotent. }
    rewrite Z.shiftr_div_pow2 in Hxor_shift by lia.
    fold q in Hxor_shift.
    apply Z.div_small_iff in Hxor_shift; [|lia].
    destruct Hxor_shift as [[_ Hlt]|Hbad]; lia. }
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists (q - 1). split.
  - split.
    + exists a0, b0. repeat split; try lia.
    + intros v Hv. destruct Hv as [a [d [Had [Hdr Hv]]]].
      subst v. apply Hbound; assumption.
  - reflexivity.
Qed.
