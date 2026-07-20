Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import CommonAssertion Mem SeparationLogic IntLib.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import GmpAux. Import Aux.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import GmpNumber.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma gcd_divexact_pos :
  forall a b,
    0 < a ->
    0 < b ->
    let g := Z.gcd a b in
    g <> 0 /\ a = (a / g) * g /\ b = (b / g) * g.
Proof.
  intros a b Ha Hb.
  set (g := Z.gcd a b).
  assert (Hg_nonzero : g <> 0).
  { intro Hg0. subst g. apply Z.gcd_eq_0_l in Hg0. lia. }
  assert (Hg_pos : 0 < g).
  { subst g. pose proof (Z.gcd_nonneg a b). lia. }
  split; [exact Hg_nonzero |].
  split.
  - assert (Hdiv : (g | a)) by (subst g; apply Z.gcd_divide_l).
    pose proof (Zdivide_Zdiv_eq g a Hg_pos Hdiv) as H.
    replace ((a / g) * g) with (g * (a / g)) by ring.
    exact H.
  - assert (Hdiv : (g | b)) by (subst g; apply Z.gcd_divide_r).
    pose proof (Zdivide_Zdiv_eq g b Hg_pos Hdiv) as H.
    replace ((b / g) * g) with (g * (b / g)) by ring.
    exact H.
Qed.

Lemma gmp_land_1_even : forall x,
  0 <= x -> Z.land x 1 = 0 -> Z.even x = true.
Proof.
  intros x Hx Hland.
  replace 1 with (Z.ones 1) in Hland by reflexivity.
  rewrite Z.land_ones in Hland by lia.
  rewrite Z.pow_1_r in Hland.
  apply Z.even_spec.
  unfold Z.Even.
  exists (x / 2).
  pose proof (Z.div_mod x 2 ltac:(lia)) as Hdiv.
  rewrite Hland in Hdiv.
  lia.
Qed.

Lemma gmp_land_1_odd : forall x,
  0 <= x -> Z.land x 1 <> 0 -> Z.odd x = true.
Proof.
  intros x Hx Hland.
  replace 1 with (Z.ones 1) in Hland by reflexivity.
  rewrite Z.land_ones in Hland by lia.
  rewrite Z.pow_1_r in Hland.
  rewrite Zodd_mod.
  assert (x mod 2 = 1) by (pose proof (Z.mod_pos_bound x 2 ltac:(lia)); lia).
  rewrite H.
  reflexivity.
Qed.

Lemma list_to_Z_limb0_land_even_mod2 :
  forall data z,
    z > 0 ->
    list_to_Z UINT_MOD data = z ->
    list_within_bound UINT_MOD data ->
    Z.land (Znth 0 (sublist 0 1 (mpd_read0_data data)) 0) 1 = 0 ->
    z mod 2 = 0.
Proof.
  intros data z Hz Hval Hbound Hland.
  destruct data as [|a l].
  - rewrite list_to_Z_nil in Hval. lia.
  - simpl in Hbound.
    destruct Hbound as [Ha Hbound].
    change (mpd_read0_data (a :: l)) with (a :: l) in Hland.
    rewrite Znth_sublist in Hland by (cbn; pose proof (Zlength_nonneg l); lia).
    change (0 + 0) with 0 in Hland.
    change (Znth 0 (a :: l) 0) with a in Hland.
    pose proof (gmp_land_1_even a ltac:(lia) Hland) as Heven.
    apply Z.even_spec in Heven.
    destruct Heven as [k Hk].
    assert (Ha_mod : a mod 2 = 0).
    { subst a. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
    rewrite <- Hval.
    rewrite list_to_Z_cons.
    rewrite Z.add_mod by lia.
    rewrite Z.mul_mod by lia.
    change (UINT_MOD mod 2) with 0.
    rewrite Z.mul_0_l, Z.add_0_r.
    rewrite Z.mod_mod by lia.
    exact Ha_mod.
Qed.

Lemma list_to_Z_limb0_land_odd_mod2 :
  forall data z,
    z > 0 ->
    list_to_Z UINT_MOD data = z ->
    list_within_bound UINT_MOD data ->
    Z.land (Znth 0 (sublist 0 1 (mpd_read0_data data)) 0) 1 <> 0 ->
    z mod 2 = 1.
Proof.
  intros data z Hz Hval Hbound Hland.
  destruct data as [|a l].
  - rewrite list_to_Z_nil in Hval. lia.
  - simpl in Hbound.
    destruct Hbound as [Ha Hbound].
    change (mpd_read0_data (a :: l)) with (a :: l) in Hland.
    rewrite Znth_sublist in Hland by (cbn; pose proof (Zlength_nonneg l); lia).
    change (0 + 0) with 0 in Hland.
    change (Znth 0 (a :: l) 0) with a in Hland.
    pose proof (gmp_land_1_odd a ltac:(lia) Hland) as Hodd.
    rewrite Zodd_mod in Hodd.
    apply Zeq_bool_eq in Hodd.
    rewrite <- Hval.
    rewrite list_to_Z_cons.
    rewrite Z.add_mod by lia.
    rewrite Z.mul_mod by lia.
    change (UINT_MOD mod 2) with 0.
    rewrite Z.mul_0_l, Z.add_0_r.
    rewrite Z.mod_mod by lia.
    exact Hodd.
Qed.

Lemma gmp_land_1_odd_div2 : forall x,
  0 < x -> Z.land x 1 <> 0 -> exists k, x = 2 * k + 1.
Proof.
  intros x Hx Hland.
  pose proof (gmp_land_1_odd x ltac:(lia) Hland) as Hodd.
  apply Z.odd_spec in Hodd.
  destruct Hodd as [k Hk].
  exists k.
  lia.
Qed.

Lemma gmp_land_1_even_div2 : forall x,
  0 < x -> Z.land x 1 = 0 -> exists k, x = 2 * k.
Proof.
  intros x Hx Hland.
  pose proof (gmp_land_1_even x ltac:(lia) Hland) as Heven.
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  exists k.
  lia.
Qed.

Lemma gmp_odd_not_div2 : forall u, Z.odd u = true -> ~ (2 | u).
Proof.
  intros u Hodd [k Hk].
  subst u.
  rewrite Z.odd_mul in Hodd.
  destruct (Z.odd k); simpl in Hodd; discriminate.
Qed.

Lemma gmp_rel_prime_odd_2 : forall u, Z.odd u = true -> rel_prime u 2.
Proof.
  intros u Hodd.
  apply rel_prime_sym.
  apply prime_rel_prime; [apply prime_2 |].
  apply gmp_odd_not_div2; exact Hodd.
Qed.

Lemma gmp_gcd_odd_even_div2_r : forall u w,
  0 < u -> 0 <= w -> Z.odd u = true ->
  Z.gcd u (2 * w) = Z.gcd u w.
Proof.
  intros u w Hu Hw Hodd.
  apply Z.divide_antisym_nonneg.
  - apply Z.gcd_nonneg.
  - apply Z.gcd_nonneg.
  - apply Z.gcd_greatest.
    + apply Z.gcd_divide_l.
    + pose proof (Z.gcd_divide_l u (2*w)) as Hdu.
      pose proof (Z.gcd_divide_r u (2*w)) as Hd2w.
      eapply Gauss.
      * exact Hd2w.
      * eapply rel_prime_div.
        -- apply gmp_rel_prime_odd_2; exact Hodd.
        -- exact Hdu.
  - apply Z.gcd_greatest.
    + apply Z.gcd_divide_l.
    + replace (2 * w) with (w * 2) by ring.
      apply Z.divide_mul_l. apply Z.gcd_divide_r.
Qed.

Lemma gmp_gcd_even_odd_div2_l : forall w v,
  0 <= w -> 0 < v -> Z.odd v = true ->
  Z.gcd (2 * w) v = Z.gcd w v.
Proof.
  intros.
  rewrite Z.gcd_comm.
  rewrite (Z.gcd_comm w v).
  apply gmp_gcd_odd_even_div2_r; assumption.
Qed.

Lemma gmp_gcd_mul_pow2_odd_l : forall w v k,
  0 <= w -> 0 < v -> v % 2 = 1 -> 0 <= k ->
  Z.gcd (w * 2 ^ k) v = Z.gcd w v.
Proof.
  intros w v k Hw Hv Hrem Hk.
  assert (Hmod : v mod 2 = 1).
  { rewrite <- (Z.rem_mod_nonneg v 2) by lia. exact Hrem. }
  assert (Hodd : Z.odd v = true).
  { rewrite Zodd_mod, Hmod. reflexivity. }
  assert (Hkid : k = Z.of_nat (Z.to_nat k)).
  { rewrite Z2Nat.id; lia. }
  rewrite Hkid.
  remember (Z.to_nat k) as n.
  clear Heqn Hk Hkid.
  induction n as [|n IH].
  - simpl. rewrite Z.mul_1_r. reflexivity.
  - rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    replace (w * (2 * 2 ^ Z.of_nat n)) with (2 * (w * 2 ^ Z.of_nat n)) by ring.
    rewrite gmp_gcd_even_odd_div2_l; try lia; try exact Hodd.
Qed.

Lemma gmp_gcd_mul_pow2_odd_r : forall u w k,
  0 < u -> 0 <= w -> u % 2 = 1 -> 0 <= k ->
  Z.gcd u (w * 2 ^ k) = Z.gcd u w.
Proof.
  intros u w k Hu Hw Hrem Hk.
  assert (Hmod : u mod 2 = 1).
  { rewrite <- (Z.rem_mod_nonneg u 2) by lia. exact Hrem. }
  assert (Hodd : Z.odd u = true).
  { rewrite Zodd_mod, Hmod. reflexivity. }
  assert (Hkid : k = Z.of_nat (Z.to_nat k)).
  { rewrite Z2Nat.id; lia. }
  rewrite Hkid.
  remember (Z.to_nat k) as n.
  clear Heqn Hk Hkid.
  induction n as [|n IH].
  - simpl. rewrite Z.mul_1_r. reflexivity.
  - rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    replace (w * (2 * 2 ^ Z.of_nat n)) with (2 * (w * 2 ^ Z.of_nat n)) by ring.
    rewrite gmp_gcd_odd_even_div2_r; try lia; try exact Hodd.
Qed.

Lemma gmp_gcd_make_odd_tdiv_left_ge : forall zu zv a b q r su sv,
  0 <= sv -> sv <= su -> 0 < a -> 0 < b -> b % 2 = 1 ->
  Z.abs zu = a * 2 ^ su -> Z.abs zv = b * 2 ^ sv ->
  a = q * b + r -> 0 <= r -> r < b ->
  Z.gcd zu zv = 2 ^ sv * Z.gcd r b.
Proof.
  intros zu zv a b q r su sv Hsv Hle Ha Hb Hbodd Hzu Hzv Haqr Hr0 Hrb.
  rewrite <- (Z.gcd_abs_l zu zv).
  rewrite <- (Z.gcd_abs_r (Z.abs zu) zv).
  rewrite Hzu, Hzv.
  replace su with (sv + (su - sv)) by lia.
  rewrite Z.pow_add_r by lia.
  replace (a * (2 ^ sv * 2 ^ (su - sv))) with (2 ^ sv * (a * 2 ^ (su - sv))) by ring.
  replace (b * 2 ^ sv) with (2 ^ sv * b) by ring.
  rewrite Z.gcd_mul_mono_l_nonneg by (apply Z.pow_nonneg; lia).
  f_equal.
  rewrite gmp_gcd_mul_pow2_odd_l; try lia; try exact Hbodd.
  rewrite Z.gcd_comm.
  rewrite <- (Z.gcd_mod a b) by lia.
  assert (Hrmod : a mod b = r).
  { rewrite Haqr.
    replace (q * b + r) with (r + q * b) by ring.
    rewrite Z.mod_add by lia.
    apply Z.mod_small; lia.
  }
  rewrite Hrmod.
  reflexivity.
Qed.

Lemma gmp_gcd_make_odd_tdiv_right_ge : forall zu zv a b q r su sv,
  0 <= su -> su <= sv -> 0 < a -> a % 2 = 1 -> 0 < b ->
  Z.abs zu = a * 2 ^ su -> Z.abs zv = b * 2 ^ sv ->
  a = q * b + r -> 0 <= r -> r < b ->
  Z.gcd zu zv = 2 ^ su * Z.gcd r b.
Proof.
  intros zu zv a b q r su sv Hsu Hle Ha Haodd Hb Hzu Hzv Haqr Hr0 Hrb.
  rewrite <- (Z.gcd_abs_l zu zv).
  rewrite <- (Z.gcd_abs_r (Z.abs zu) zv).
  rewrite Hzu, Hzv.
  replace sv with (su + (sv - su)) by lia.
  rewrite Z.pow_add_r by lia.
  replace (a * 2 ^ su) with (2 ^ su * a) by ring.
  replace (b * (2 ^ su * 2 ^ (sv - su))) with (2 ^ su * (b * 2 ^ (sv - su))) by ring.
  rewrite Z.gcd_mul_mono_l_nonneg by (apply Z.pow_nonneg; lia).
  f_equal.
  rewrite gmp_gcd_mul_pow2_odd_r; try lia; try exact Haodd.
  rewrite Z.gcd_comm.
  rewrite <- (Z.gcd_mod a b) by lia.
  assert (Hrmod : a mod b = r).
  { rewrite Haqr.
    replace (q * b + r) with (r + q * b) by ring.
    rewrite Z.mod_add by lia.
    apply Z.mod_small; lia.
  }
  rewrite Hrmod.
  reflexivity.
Qed.

Lemma gmp_gcd_shiftr1_even_r : forall u v,
  0 < u -> 0 < v -> Z.land u 1 <> 0 -> Z.land v 1 = 0 ->
  Z.gcd u (Z.shiftr v 1) = Z.gcd u v.
Proof.
  intros u v Hu Hv Huodd Hveven.
  pose proof (gmp_land_1_odd u ltac:(lia) Huodd) as Hodd.
  pose proof (gmp_land_1_even_div2 v Hv Hveven) as [w Hw].
  assert (Hw_nonneg : 0 <= w) by lia.
  rewrite Hw at 2.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Hw.
  replace (2 * w / 2 ^ 1) with w
    by (rewrite Z.pow_1_r; replace (2*w) with (w*2) by ring;
        symmetry; apply Z.div_mul; lia).
  symmetry.
  apply gmp_gcd_odd_even_div2_r; assumption.
Qed.

Lemma gmp_gcd_shiftr1_even_l : forall u v,
  0 < u -> 0 < v -> Z.land u 1 = 0 -> Z.land v 1 <> 0 ->
  Z.gcd (Z.shiftr u 1) v = Z.gcd u v.
Proof.
  intros u v Hu Hv Hueven Hvodd.
  rewrite Z.gcd_comm.
  rewrite (Z.gcd_comm u v).
  apply gmp_gcd_shiftr1_even_r; assumption.
Qed.

Lemma gmp_even_land_1_0 : forall x,
  0 <= x -> Z.even x = true -> Z.land x 1 = 0.
Proof.
  intros x Hx Heven.
  replace 1 with (Z.ones 1) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.pow_1_r.
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  rewrite Hk.
  replace (2 * k) with (k * 2) by ring.
  apply Z.mod_mul; lia.
Qed.

Lemma gmp_odd_land_1_nonzero : forall x,
  0 <= x -> Z.odd x = true -> Z.land x 1 <> 0.
Proof.
  intros x Hx Hodd Hland.
  pose proof (gmp_land_1_even x Hx Hland) as Heven.
  rewrite <- Z.negb_odd in Heven.
  rewrite Hodd in Heven.
  discriminate.
Qed.

Lemma gmp_gcd_sub_odd_shiftr_l : forall u v,
  u > v -> 0 < v -> Z.land u 1 <> 0 -> Z.land v 1 <> 0 ->
  Z.gcd (Z.shiftr (u - v) 1) v = Z.gcd u v.
Proof.
  intros u v Hgt Hv Huodd Hvodd.
  assert (Hu_pos : 0 < u) by lia.
  pose proof (gmp_land_1_odd u ltac:(lia) Huodd) as Hu_odd.
  pose proof (gmp_land_1_odd v ltac:(lia) Hvodd) as Hv_odd.
  assert (Hdiff_even : Z.land (u - v) 1 = 0).
  { apply gmp_even_land_1_0; [lia|].
    rewrite Z.even_sub.
    rewrite !Zeven.Zeven_odd_bool.
    rewrite Hu_odd, Hv_odd. reflexivity. }
  rewrite gmp_gcd_shiftr1_even_l; try lia; try exact Hdiff_even; try exact Hvodd.
  rewrite Z.gcd_comm.
  rewrite Z.gcd_sub_diag_r.
  rewrite Z.gcd_comm.
  reflexivity.
Qed.

Lemma gmp_gcd_sub_odd_shiftr_r : forall u v,
  v > u -> 0 < u -> Z.land u 1 <> 0 -> Z.land v 1 <> 0 ->
  Z.gcd u (Z.shiftr (v - u) 1) = Z.gcd u v.
Proof.
  intros u v Hgt Hu Huodd Hvodd.
  rewrite Z.gcd_comm.
  rewrite (gmp_gcd_sub_odd_shiftr_l v u Hgt Hu Hvodd Huodd).
  rewrite Z.gcd_comm.
  reflexivity.
Qed.

Lemma gmp_land_odd_odd : forall a b,
  Z.land (2 * a + 1) (2 * b + 1) = 2 * Z.land a b + 1.
Proof.
  intros a b.
  apply Z.bits_inj.
  intros n.
  destruct (Z_lt_ge_dec n 0) as [Hnneg | Hnnonneg].
  - rewrite !Z.testbit_neg_r by lia. reflexivity.
  - destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
    + subst n.
      rewrite Z.land_spec.
      rewrite !Z.testbit_odd_0.
      reflexivity.
    + replace n with (Z.succ (n - 1)) by lia.
      rewrite Z.land_spec.
      rewrite !Z.testbit_odd_succ by lia.
      rewrite Z.land_spec.
      reflexivity.
Qed.

Lemma gmp_lowbit_odd : forall x,
  0 < x -> Z.odd x = true -> Z.land x (-x) = 1.
Proof.
  intros x Hx Hodd.
  apply Z.odd_spec in Hodd.
  destruct Hodd as [k Hk].
  rewrite Hk.
  replace (-(2 * k + 1)) with (2 * (-k - 1) + 1) by ring.
  rewrite gmp_land_odd_odd.
  replace (- k - 1) with (Z.lnot k) by (rewrite Z.lnot_eq_pred_opp; ring).
  rewrite Z.land_lnot_diag.
  ring.
Qed.

Lemma gmp_lowbit_double : forall x,
  Z.land (2 * x) (-(2 * x)) = 2 * Z.land x (-x).
Proof.
  intros x.
  replace (2 * x) with (Z.shiftl x 1)
    by (rewrite Z.shiftl_mul_pow2 by lia; ring).
  replace (- Z.shiftl x 1) with (Z.shiftl (-x) 1)
    by (rewrite !Z.shiftl_mul_pow2 by lia; ring).
  rewrite <- Z.shiftl_land.
  rewrite Z.shiftl_mul_pow2 by lia.
  ring.
Qed.

Lemma gmp_lowbit_decompose : forall x,
  0 < x ->
  exists odd k,
    0 <= k /\ odd > 0 /\ odd mod 2 = 1 /\
    x = odd * 2 ^ k /\ Z.land x (-x) = 2 ^ k.
Proof.
  set (P := fun x => 0 < x ->
      exists odd k,
        0 <= k /\ odd > 0 /\ odd mod 2 = 1 /\
        x = odd * 2 ^ k /\ Z.land x (-x) = 2 ^ k).
  assert (Hstep : forall x, (forall y, 0 <= y < x -> P y) -> P x).
  { subst P.
    intros x IH Hx.
    destruct (Z.odd x) eqn:Hodd.
    - exists x, 0.
      rewrite Z.pow_0_r.
      repeat split; try lia.
      + rewrite Zmod_odd, Hodd. reflexivity.
      + apply gmp_lowbit_odd; assumption.
    - assert (Heven : Z.even x = true).
      { rewrite <- Z.negb_odd. rewrite Hodd. reflexivity. }
      apply Z.even_spec in Heven.
      destruct Heven as [y Hy].
      assert (Hypos : 0 < y) by lia.
      destruct (IH y ltac:(lia) Hypos) as [odd [k [Hk0 [Hoddpos [Hoddmod [Hy_eq Hlow]]]]]].
      exists odd, (k + 1).
      repeat split.
      + lia.
      + exact Hoddpos.
      + exact Hoddmod.
      + rewrite Hy, Hy_eq.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        ring.
      + rewrite Hy.
        rewrite gmp_lowbit_double.
        rewrite Hlow.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        ring. }
  intros x Hx.
  exact (Z_lt_induction P Hstep x ltac:(lia) Hx).
Qed.

Lemma gmp_ctz_from_lowbit_clz : forall x retval,
  0 < x ->
  0 <= retval -> retval < 32 ->
  2 ^ 31 <= Z.land x (-x) * 2 ^ retval ->
  Z.land x (-x) * 2 ^ retval < 2 ^ 32 ->
  exists odd,
    0 <= 31 - retval /\ 31 - retval < 32 /\
    odd > 0 /\ odd mod 2 = 1 /\ x = odd * 2 ^ (31 - retval).
Proof.
  intros x retval Hx Hr0 Hr32 Hlo Hhi.
  destruct (gmp_lowbit_decompose x Hx)
    as [odd [k [Hk0 [Hoddpos [Hoddmod [Hxdec Hlow]]]]]].
  rewrite Hlow in Hlo, Hhi.
  rewrite <- Z.pow_add_r in Hlo by lia.
  rewrite <- Z.pow_add_r in Hhi by lia.
  assert (Hge : 31 <= k + retval).
  { apply (proj2 (Z.pow_le_mono_r_iff 2 31 (k + retval) ltac:(lia) ltac:(lia))).
    exact Hlo. }
  assert (Hlt : k + retval < 32).
  { apply (proj2 (Z.pow_lt_mono_r_iff 2 (k + retval) 32 ltac:(lia) ltac:(lia))).
    exact Hhi. }
  assert (Hk : k = 31 - retval) by lia.
  exists odd.
  repeat split; try lia.
  rewrite Hk in Hxdec.
  exact Hxdec.
Qed.

Lemma gmp_lor_lowbits_zero_l : forall a b k,
  0 <= k ->
  Z.land (Z.lor a b) (Z.ones k) = 0 ->
  Z.land a (Z.ones k) = 0.
Proof.
  intros a b k Hk Hlor.
  apply Z.bits_inj_0.
  intros n.
  destruct (Z_lt_ge_dec n 0) as [Hnneg | Hnnonneg].
  - rewrite Z.testbit_neg_r by lia. reflexivity.
  - rewrite Z.land_spec.
    destruct (Z_lt_ge_dec n k) as [Hnlt | Hnge].
    + assert (Hzero: Z.testbit (Z.land (Z.lor a b) (Z.ones k)) n = false).
      { rewrite Hlor. apply Z.testbit_0_l. }
      rewrite Z.land_spec in Hzero.
      rewrite Z.ones_spec_low in Hzero by lia.
      rewrite Z.lor_spec in Hzero.
      rewrite Z.ones_spec_low by lia.
      destruct (Z.testbit a n), (Z.testbit b n); simpl in *; try discriminate; reflexivity.
    + rewrite Z.ones_spec_high by lia.
      destruct (Z.testbit a n); reflexivity.
Qed.

Lemma gmp_lor_lowbits_zero_r : forall a b k,
  0 <= k ->
  Z.land (Z.lor a b) (Z.ones k) = 0 ->
  Z.land b (Z.ones k) = 0.
Proof.
  intros a b k Hk Hlor.
  rewrite Z.lor_comm in Hlor.
  apply (gmp_lor_lowbits_zero_l b a k Hk Hlor).
Qed.

Lemma gmp_lor_factor_shiftr : forall a b odd k,
  0 <= a -> 0 <= b -> 0 <= k -> odd mod 2 = 1 ->
  Z.lor a b = odd * 2 ^ k ->
  a = 2 ^ k * Z.shiftr a k /\ b = 2 ^ k * Z.shiftr b k.
Proof.
  intros a b odd k Ha Hb Hk Hodd Hlor.
  assert (Hlor_low : Z.land (Z.lor a b) (Z.ones k) = 0).
  { rewrite Hlor.
    rewrite Z.land_ones by lia.
    rewrite Z.mod_mul by (apply Z.pow_nonzero; lia).
    reflexivity. }
  assert (Ha_low : Z.land a (Z.ones k) = 0)
    by (apply (gmp_lor_lowbits_zero_l a b k Hk Hlor_low)).
  assert (Hb_low : Z.land b (Z.ones k) = 0)
    by (apply (gmp_lor_lowbits_zero_r a b k Hk Hlor_low)).
  rewrite Z.land_ones in Ha_low by lia.
  rewrite Z.land_ones in Hb_low by lia.
  split.
  - rewrite Z.shiftr_div_pow2 by lia.
    pose proof (Z.div_mod a (2 ^ k) ltac:(apply Z.pow_nonzero; lia)) as Hdiv.
    rewrite Ha_low in Hdiv.
    lia.
  - rewrite Z.shiftr_div_pow2 by lia.
    pose proof (Z.div_mod b (2 ^ k) ltac:(apply Z.pow_nonzero; lia)) as Hdiv.
    rewrite Hb_low in Hdiv.
    lia.
Qed.

Lemma gmp_lor_shifted_odd_r : forall a b odd k,
  0 <= k -> odd mod 2 = 1 ->
  Z.lor a b = odd * 2 ^ k ->
  Z.land (Z.shiftr a k) 1 = 0 ->
  Z.land (Z.shiftr b k) 1 <> 0.
Proof.
  intros a b odd k Hk Hodd Hlor Ha0 Hb0.
  assert (Hodd_bool : Z.odd odd = true).
  { rewrite Zodd_mod. rewrite Hodd. reflexivity. }
  assert (Hbit_lor : Z.testbit (Z.lor a b) k = true).
  { rewrite Hlor.
    replace (odd * 2 ^ k) with (Z.shiftl odd k)
      by (rewrite Z.shiftl_mul_pow2 by lia; ring).
    rewrite Z.shiftl_spec_high by lia.
    replace (k - k) with 0 by lia.
    rewrite Z.bit0_odd.
    exact Hodd_bool. }
  assert (Ha_bit : Z.testbit a k = false).
  { assert (Hzero : Z.testbit (Z.land (Z.shiftr a k) 1) 0 = false).
    { rewrite Ha0. apply Z.testbit_0_l. }
    rewrite Z.land_spec in Hzero.
    replace (Z.testbit 1 0) with true in Hzero by reflexivity.
    rewrite Z.shiftr_spec in Hzero by lia.
    replace (0 + k) with k in Hzero by lia.
    destruct (Z.testbit a k); simpl in Hzero; try discriminate; reflexivity. }
  assert (Hb_bit : Z.testbit b k = true).
  { rewrite Z.lor_spec in Hbit_lor.
    rewrite Ha_bit in Hbit_lor.
    simpl in Hbit_lor.
    exact Hbit_lor. }
  assert (Hb_bit0 : Z.testbit (Z.shiftr b k) 0 = true).
  { rewrite Z.shiftr_spec by lia.
    replace (0 + k) with k by lia.
    exact Hb_bit. }
  assert (Hzero : Z.testbit (Z.land (Z.shiftr b k) 1) 0 = false).
  { rewrite Hb0. apply Z.testbit_0_l. }
  rewrite Z.land_spec in Hzero.
  replace (Z.testbit 1 0) with true in Hzero by reflexivity.
  rewrite Hb_bit0 in Hzero.
  simpl in Hzero.
  discriminate.
Qed.

Lemma gmp_lor_ctz_prepare : forall u v odd k cap,
  0 <= u -> u <= cap -> 0 <= v -> v <= cap ->
  u <> 0 -> v <> 0 ->
  0 <= k -> odd mod 2 = 1 -> Z.lor u v = odd * 2 ^ k ->
  0 < Z.shiftr u k /\ Z.shiftr u k <= cap /\
  0 < Z.shiftr v k /\ Z.shiftr v k <= cap /\
  Z.gcd u v = 2 ^ k * Z.gcd (Z.shiftr u k) (Z.shiftr v k).
Proof.
  intros u v odd k cap Hu0 Hucap Hv0 Hvcap Hune Hvne Hk Hodd Hlor.
  destruct (gmp_lor_factor_shiftr u v odd k Hu0 Hv0 Hk Hodd Hlor) as [Hu_fact Hv_fact].
  assert (Hpow_pos : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow_ge1 : 1 <= 2 ^ k) by lia.
  assert (Hsu_nonneg : 0 <= Z.shiftr u k) by (apply Z.shiftr_nonneg; lia).
  assert (Hsv_nonneg : 0 <= Z.shiftr v k) by (apply Z.shiftr_nonneg; lia).
  assert (Hsu_pos : 0 < Z.shiftr u k).
  { destruct (Z.eq_dec (Z.shiftr u k) 0); subst; nia. }
  assert (Hsv_pos : 0 < Z.shiftr v k).
  { destruct (Z.eq_dec (Z.shiftr v k) 0); subst; nia. }
  repeat split; try nia.
  rewrite Hu_fact at 1.
  rewrite Hv_fact at 1.
  apply Z.gcd_mul_mono_l_nonneg.
  lia.
Qed.

Lemma gmp_lowbit_pos_bound : forall x,
  0 < x ->
  0 < Z.land x (-x) /\ Z.land x (-x) <= x.
Proof.
  intros x Hx.
  destruct (gmp_lowbit_decompose x Hx)
    as [odd [k [Hk0 [Hoddpos [Hoddmod [Hxdec Hlow]]]]]].
  rewrite Hlow.
  split.
  - apply Z.pow_pos_nonneg; lia.
  - rewrite Hxdec.
    assert (Hpow_pos : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    nia.
Qed.

Lemma gmp_lor_pos_bound_32 : forall u v,
  0 <= u -> u <= 4294967295 ->
  0 <= v -> v <= 4294967295 ->
  u <> 0 -> v <> 0 ->
  0 < Z.lor u v /\ Z.lor u v <= 4294967295.
Proof.
  intros u v Hu0 HuB Hv0 HvB HuNe HvNe.
  split.
  - assert (Hnonneg : 0 <= Z.lor u v).
    { apply Z.lor_nonneg. split; lia. }
    destruct (Z.eq_dec (Z.lor u v) 0) as [Hz|Hz]; [|lia].
    apply Z.lor_eq_0_iff in Hz.
    tauto.
  - pose proof (IntLib.unsigned_last_nbits_lor_distr_missing u v 32 ltac:(lia) ltac:(lia) ltac:(lia)) as Hmask.
    pose proof (IntLib.unsigned_Lastnbits_range (Z.lor u v) 32 ltac:(lia)) as Hrange.
    rewrite Hmask in Hrange.
    lia.
Qed.

Lemma gmp_rem1_to_mod1 : forall x,
  0 < x -> Z.rem x 2 = 1 -> x mod 2 = 1.
Proof.
  intros x Hx Hrem.
  rewrite Z.rem_mod in Hrem by lia.
  rewrite Z.abs_eq in Hrem by lia.
  replace (Z.abs 2) with 2 in Hrem by reflexivity.
  replace (Z.sgn x) with 1 in Hrem by (symmetry; apply Z.sgn_pos; lia).
  lia.
Qed.

Lemma gmp_mod1_to_rem1 : forall x,
  0 < x -> x mod 2 = 1 -> Z.rem x 2 = 1.
Proof.
  intros x Hx Hmod.
  rewrite Z.rem_mod by lia.
  rewrite Z.abs_eq by lia.
  replace (Z.abs 2) with 2 by reflexivity.
  replace (Z.sgn x) with 1 by (symmetry; apply Z.sgn_pos; lia).
  lia.
Qed.

Lemma gmp_shiftr1_even_pos_bound : forall x cap,
  0 < x -> x <= cap -> Z.land x 1 = 0 ->
  0 < Z.shiftr x 1 /\ Z.shiftr x 1 <= cap.
Proof.
  intros x cap Hx Hcap Heven.
  pose proof (gmp_land_1_even_div2 x Hx Heven) as [k Hk].
  assert (Hkpos : 0 < k) by lia.
  rewrite Hk.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.pow_1_r.
  assert (Hdiv : 2 * k / 2 = k).
  { replace (2 * k) with (k * 2) by ring.
    apply Z.div_mul; lia. }
  rewrite Hdiv.
  split; lia.
Qed.

Lemma gmp_odd_sub_even_land : forall u v,
  u >= v -> 0 < u -> 0 < v ->
  Z.land u 1 <> 0 -> Z.land v 1 <> 0 ->
  Z.land (u - v) 1 = 0.
Proof.
  intros u v Hge Hu Hv Huodd Hvodd.
  apply gmp_even_land_1_0; [lia|].
  pose proof (gmp_land_1_odd u ltac:(lia) Huodd) as Hu_odd.
  pose proof (gmp_land_1_odd v ltac:(lia) Hvodd) as Hv_odd.
  rewrite Z.even_sub.
  rewrite !Zeven.Zeven_odd_bool.
  rewrite Hu_odd, Hv_odd.
  reflexivity.
Qed.

Lemma gmp_gcd_bound_32 : forall a b,
  0 <= a -> a <= 4294967295 ->
  0 <= b -> b <= 4294967295 ->
  Z.gcd a b <= 4294967295.
Proof.
  intros a b Ha0 HaB Hb0 HbB.
  destruct (Z.eq_dec a 0) as [Ha|Ha].
  - subst a. rewrite Z.gcd_0_l. rewrite Z.abs_eq; lia.
  - assert (Ha_pos : 0 < a) by lia.
    eapply Z.le_trans.
    + apply Z.divide_pos_le; [exact Ha_pos | apply Z.gcd_divide_l].
    + exact HaB.
Qed.

Lemma gmp_gcd_final_shift_return_32 : forall u_pre v_pre u v shift,
  u = v ->
  0 <= shift -> shift < 32 ->
  0 <= u_pre -> u_pre <= 4294967295 ->
  0 <= v_pre -> v_pre <= 4294967295 ->
  0 < u -> u <= 4294967295 ->
  0 < v -> v <= 4294967295 ->
  Z.gcd u_pre v_pre = 2 ^ shift * Z.gcd u v ->
  IntLib.unsigned_last_nbits (Z.shiftl u shift) 32 = Z.gcd u_pre v_pre.
Proof.
  intros u_pre v_pre u v shift Heq Hs0 Hs32 Hu0 HuB Hv0 HvB Hupos HuB2 Hvpos HvB2 Hgcd.
  rewrite Z.shiftl_mul_pow2 by lia.
  subst v.
  rewrite Z.gcd_diag in Hgcd.
  rewrite Z.abs_eq in Hgcd by lia.
  rewrite Hgcd.
  replace (u * 2 ^ shift) with (2 ^ shift * u) by ring.
  apply IntLib.unsigned_last_nbits_eq.
  split.
  - rewrite <- Hgcd. apply Z.gcd_nonneg.
  - rewrite <- Hgcd.
    pose proof (gmp_gcd_bound_32 u_pre v_pre Hu0 HuB Hv0 HvB) as Hbound.
    lia.
Qed.

Definition gmp_scan_limb (ux x: Z): Z :=
  Z.lxor ux x.

Definition gmp_scan1_mask (bit: Z): Z :=
  unsigned_last_nbits (Z.shiftl UINT_MAX (bit mod 32)) 32.

Definition gmp_scan1_limb (l: list Z) (bit: Z): Z :=
  Z.land (Znth (bit / 32) l 0) (gmp_scan1_mask bit).

Definition mpn_common_scan_found
  (l: list Z) (limb i un ux pos cnt odd: Z): Prop :=
  (ux = 0 \/ ux = UINT_MAX) /\
  0 <= limb <= UINT_MAX /\
  0 <= i /\
  i <= pos /\
  pos < Zlength l /\
  (un = i \/ pos < un) /\
  0 <= cnt < 32 /\
  odd > 0 /\
  odd mod 2 = 1 /\
  ((pos = i /\ limb = odd * 2 ^ cnt) \/
   (i < pos /\
    limb = 0 /\
    (forall k, i < k < pos ->
      gmp_scan_limb ux (Znth k l 0) = 0) /\
    gmp_scan_limb ux (Znth pos l 0) = odd * 2 ^ cnt)).

Definition mpn_scan1_found
  (l: list Z) (bit pos cnt odd: Z): Prop :=
  0 <= bit /\
  mpn_common_scan_found l (gmp_scan1_limb l bit) (bit / 32) (bit / 32)
    0 pos cnt odd.

Definition mpn_common_scan_target
  (l: list Z) (limb i un ux pos: Z): Prop :=
  (ux = 0 \/ ux = UINT_MAX) /\
  0 <= limb <= UINT_MAX /\
  0 <= i <= pos /\
  pos < Zlength l /\
  ((pos = i /\ limb <> 0) \/
   (i < pos /\
    limb = 0 /\
    (forall k, i < k < pos ->
      gmp_scan_limb ux (Znth k l 0) = 0) /\
    (forall k, i < k <= pos -> k <> un) /\
    gmp_scan_limb ux (Znth pos l 0) <> 0)).

Definition mpn_common_scan_result
  (l: list Z) (limb i un ux pos ret: Z): Prop :=
  mpn_common_scan_target l limb i un ux pos /\
  exists cnt odd,
    ret = pos * 32 + cnt /\
    0 <= cnt < 32 /\
    odd > 0 /\
    odd mod 2 = 1 /\
    ((pos = i /\ limb = odd * 2 ^ cnt) \/
     (i < pos /\
      gmp_scan_limb ux (Znth pos l 0) = odd * 2 ^ cnt)).

Definition mpn_scan1_target (l: list Z) (bit: Z): Prop :=
  0 <= bit /\
  exists pos,
    mpn_common_scan_target l (gmp_scan1_limb l bit) (bit / 32) (bit / 32) 0 pos.

Definition mpn_scan1_result (l: list Z) (bit ret: Z): Prop :=
  bit <= ret < 32 * Zlength l /\
  Z.testbit (list_to_Z UINT_MOD l) ret = true /\
  (forall k, bit <= k < ret -> Z.testbit (list_to_Z UINT_MOD l) k = false).

Lemma list_to_Z_testbit_limb :
  forall l k,
    list_within_bound UINT_MOD l ->
    0 <= k < 32 * Zlength l ->
    Z.testbit (list_to_Z UINT_MOD l) k =
    Z.testbit (Znth (k / 32) l 0) (k mod 32).
Proof.
  intros l k Hbound Hk.
  set (idx := k / 32).
  set (off := k mod 32).
  assert (Hoff : 0 <= off < 32) by (subst off; apply Z.mod_pos_bound; lia).
  assert (Hidx : 0 <= idx < Zlength l).
  {
    subst idx.
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  }
  pose proof (list_to_Z_nth UINT_MOD UINT_MOD_pos l (list_to_Z UINT_MOD l) idx
                Hidx Hbound) as Hnth.
  rewrite Hnth.
  change UINT_MOD with (2 ^ 32).
  replace ((2 ^ 32) ^ idx) with (2 ^ (32 * idx))
    by (rewrite <- Z.pow_mul_r by lia; reflexivity).
  rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.div_pow2_bits by lia.
  assert (Hk_decomp : k = idx * 32 + off).
  {
    subst idx off.
    rewrite (Z.div_mod k 32) at 1 by lia.
    ring.
  }
  rewrite Hk_decomp.
  replace (idx * 32 + off) with (off + 32 * idx) by ring.
  reflexivity.
Qed.

Lemma scan1_mask_bit :
  forall b m,
    0 <= b < 32 ->
    0 <= m < 32 ->
    Z.testbit (unsigned_last_nbits (Z.shiftl UINT_MAX b) 32) m =
    Z.leb b m.
Proof.
  intros b m Hb Hm.
  rewrite Ztestbits_unsigned_eq by lia.
  destruct (Z.leb_spec b m) as [Hle | Hgt].
  - rewrite Z.shiftl_spec_high by lia.
    replace UINT_MAX with (Z.ones 32) by reflexivity.
    rewrite Z.ones_spec_low by lia.
    reflexivity.
  - rewrite Z.shiftl_spec_low by lia.
    reflexivity.
Qed.

Lemma odd_mul_pow2_testbit_true :
  forall odd cnt,
    0 <= cnt ->
    odd > 0 ->
    odd mod 2 = 1 ->
    Z.testbit (odd * 2 ^ cnt) cnt = true.
Proof.
  intros odd cnt Hcnt Hodd Hmod.
  replace (Z.testbit (odd * 2 ^ cnt) cnt)
    with (Z.testbit (odd * 2 ^ cnt) (cnt + 0))
    by (f_equal; lia).
  rewrite (Z.mul_pow2_bits_add odd cnt 0) by lia.
  apply (proj2 (Z.testbit_true odd 0 ltac:(lia))).
  change (2 ^ 0) with 1.
  rewrite Z.div_1_r.
  exact Hmod.
Qed.

Lemma odd_mul_pow2_testbit_low_false :
  forall odd cnt m,
    m < cnt ->
    Z.testbit (odd * 2 ^ cnt) m = false.
Proof.
  intros odd cnt m Hlt.
  apply Z.mul_pow2_bits_low.
  lia.
Qed.

Lemma scan1_common_result_implies_scan1_result :
  forall l bit i pos ret,
    bit >= 0 ->
    i = bit ÷ 32 ->
    list_within_bound UINT_MOD l ->
    mpn_common_scan_result l
      (Z.land (Znth i l 0)
         (unsigned_last_nbits (Z.shiftl UINT_MAX (bit % 32)) 32))
      i i 0 pos ret ->
    mpn_scan1_result l bit ret.
Proof.
  intros l bit i pos ret Hbit Hi Hbound Hres.
  unfold mpn_common_scan_result in Hres.
  destruct Hres as [Htarget [cnt [odd [Hret [Hcnt [Hodd_pos [Hodd_mod Hfound]]]]]]].
  unfold mpn_common_scan_target in Htarget.
  destruct Htarget as [Hux [Hlimb_rng [Hi_pos [Hpos Hcase]]]].
  assert (Hquot : bit ÷ 32 = bit / 32) by (apply Z.quot_div_nonneg; lia).
  assert (Hrem : bit % 32 = bit mod 32) by (apply Z.rem_mod_nonneg; lia).
  assert (Hbrem : 0 <= bit mod 32 < 32) by (apply Z.mod_pos_bound; lia).
  assert (Hi_div : i = bit / 32) by (subst i; exact Hquot).
  assert (Hbit_decomp : bit = i * 32 + bit mod 32).
  {
    rewrite Hi_div.
    rewrite (Z.div_mod bit 32) at 1 by lia.
    ring.
  }
  rewrite Hrem in Hfound.
  rewrite Hrem in Hcase.
  assert (Hpos_bound : 0 <= pos < Zlength l) by lia.
  assert (Hret_eq : ret = pos * 32 + cnt) by exact Hret.
  assert (Hret_bound : 0 <= ret < 32 * Zlength l).
  {
    subst ret.
    destruct Hcnt as [Hcnt0 Hcnt32].
    nia.
  }
  assert (Hbit_le_ret : bit <= ret).
  {
    subst ret.
    destruct Hcnt as [Hcnt0 Hcnt32].
    destruct Hfound as [[Hpos_i Hlimb] | [Hi_lt_pos Hscan]].
    - subst pos.
      assert (Hcnt_ge : bit mod 32 <= cnt).
      {
        destruct (Z_le_gt_dec (bit mod 32) cnt) as [|Hlt]; [lia|].
        assert (Hmask_false :
          Z.testbit (unsigned_last_nbits (Z.shiftl UINT_MAX (bit mod 32)) 32) cnt = false).
        {
          rewrite scan1_mask_bit by lia.
          apply Z.leb_gt. lia.
        }
        assert (Hland_true :
          Z.testbit
            (Z.land (Znth i l 0)
               (unsigned_last_nbits (Z.shiftl UINT_MAX (bit mod 32)) 32)) cnt = true).
        {
          rewrite Hlimb.
          apply odd_mul_pow2_testbit_true; lia.
        }
        rewrite Z.land_spec in Hland_true.
        rewrite Hmask_false in Hland_true.
        rewrite Bool.andb_false_r in Hland_true.
        discriminate.
      }
      rewrite Hbit_decomp.
      lia.
    - rewrite Hbit_decomp.
      lia.
  }
  unfold mpn_scan1_result.
  repeat split; try lia.
  - rewrite (list_to_Z_testbit_limb l ret) by (try exact Hbound; lia).
    subst ret.
    replace ((pos * 32 + cnt) / 32) with pos by (apply Z.div_unique with (r:=cnt); lia).
    replace ((pos * 32 + cnt) mod 32) with cnt by (apply Z.mod_unique with (q:=pos); lia).
    destruct Hfound as [[Hpos_i Hlimb] | [Hi_lt_pos Hscan]].
    + subst pos.
      assert (Hland_true :
        Z.testbit
          (Z.land (Znth i l 0)
             (unsigned_last_nbits (Z.shiftl UINT_MAX (bit mod 32)) 32)) cnt = true).
      {
        rewrite Hlimb.
        apply odd_mul_pow2_testbit_true; lia.
      }
      rewrite Z.land_spec in Hland_true.
      destruct (Z.testbit (Znth i l 0) cnt); simpl in Hland_true; [reflexivity|discriminate].
    + unfold gmp_scan_limb in Hscan.
      rewrite Z.lxor_0_l in Hscan.
      rewrite Hscan.
      apply odd_mul_pow2_testbit_true; lia.
  - intros k Hk.
    assert (Hk_bound : 0 <= k < 32 * Zlength l) by lia.
    rewrite (list_to_Z_testbit_limb l k) by (try exact Hbound; lia).
    set (idx := k / 32).
    set (off := k mod 32).
    assert (Hoff : 0 <= off < 32) by (subst off; apply Z.mod_pos_bound; lia).
    assert (Hidx : 0 <= idx < Zlength l).
    {
      subst idx.
      split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia.
    }
    assert (Hk_decomp : k = idx * 32 + off).
    {
      subst idx off.
      rewrite (Z.div_mod k 32) at 1 by lia.
      ring.
    }
    assert (Hi_le_idx : i <= idx).
    {
      rewrite Hbit_decomp in Hk.
      rewrite Hk_decomp in Hk.
      nia.
    }
    assert (Hidx_le_pos : idx <= pos).
    {
      subst ret.
      rewrite Hk_decomp in Hk.
      destruct Hcnt as [Hcnt0 Hcnt32].
      nia.
    }
    destruct (Z.eq_dec idx i) as [Hidx_i | Hidx_ne_i].
    + subst idx.
      destruct Hfound as [[Hpos_i Hlimb] | [Hi_lt_pos Hscan]].
      * subst pos.
        assert (Hoff_lt_cnt : off < cnt).
        {
          rewrite Hk_decomp in Hk.
          nia.
        }
        assert (Hoff_ge_bit : bit mod 32 <= off).
        {
          rewrite Hbit_decomp in Hk.
          rewrite Hk_decomp in Hk.
          nia.
        }
        assert (Hland_false :
          Z.testbit
            (Z.land (Znth i l 0)
               (unsigned_last_nbits (Z.shiftl UINT_MAX (bit mod 32)) 32)) off = false).
        {
          rewrite Hlimb.
          apply odd_mul_pow2_testbit_low_false.
          lia.
        }
        rewrite Z.land_spec in Hland_false.
        rewrite scan1_mask_bit in Hland_false by lia.
        rewrite (proj2 (Z.leb_le (bit mod 32) off) Hoff_ge_bit) in Hland_false.
        rewrite Hidx_i.
        destruct (Z.testbit (Znth i l 0) off) eqn:Hbitoff; simpl in Hland_false.
        -- discriminate.
        -- reflexivity.
      * assert (Hoff_ge_bit : bit mod 32 <= off).
        {
          rewrite Hbit_decomp in Hk.
          rewrite Hk_decomp in Hk.
          nia.
        }
        assert (Hland_zero :
          Z.land (Znth i l 0)
            (unsigned_last_nbits (Z.shiftl UINT_MAX (bit mod 32)) 32) = 0).
        {
          destruct Hcase as [[Hpos_i Hnz] | [_ [Hzero _]]].
          - lia.
          - exact Hzero.
        }
        assert (Hland_false :
          Z.testbit
            (Z.land (Znth i l 0)
               (unsigned_last_nbits (Z.shiftl UINT_MAX (bit mod 32)) 32)) off = false).
        { rewrite Hland_zero. apply Z.testbit_0_l. }
        rewrite Z.land_spec in Hland_false.
        rewrite scan1_mask_bit in Hland_false by lia.
        rewrite (proj2 (Z.leb_le (bit mod 32) off) Hoff_ge_bit) in Hland_false.
        rewrite Hidx_i.
        destruct (Z.testbit (Znth i l 0) off) eqn:Hbitoff; simpl in Hland_false.
        -- discriminate.
        -- reflexivity.
    + assert (Hi_lt_idx : i < idx) by lia.
      destruct (Z.eq_dec idx pos) as [Hidx_pos | Hidx_ne_pos].
      * rewrite Hidx_pos.
        assert (Hoff_lt_cnt : off < cnt).
        {
          rewrite Hk_decomp in Hk.
          subst ret.
          nia.
        }
        destruct Hfound as [[Hpos_i Hlimb] | [Hi_lt_pos Hscan]].
        -- lia.
        -- unfold gmp_scan_limb in Hscan.
           rewrite Z.lxor_0_l in Hscan.
           rewrite Hscan.
           apply odd_mul_pow2_testbit_low_false.
           lia.
      * assert (Hi_lt_idx_pos : i < idx < pos) by lia.
        destruct Hcase as [[Hpos_i Hnz] | [Hi_lt_pos [Hlimb0 [Hzero [Hneq Hscan]]]]].
        -- lia.
        -- specialize (Hzero idx Hi_lt_idx_pos).
           unfold gmp_scan_limb in Hzero.
           rewrite Z.lxor_0_l in Hzero.
           rewrite Hzero.
           apply Z.testbit_0_l.
Qed.

Lemma same_sign_pos_nonneg_r :
  forall z size,
    z > 0 ->
    same_sign z size ->
    size >= 0.
Proof.
  intros z size Hz Hsign.
  unfold same_sign in Hsign.
  destruct Hsign as [[_ Hsize] | [Hzneg _]]; lia.
Qed.

Lemma list_to_Z_positive_length :
  forall l,
    list_to_Z UINT_MOD l > 0 ->
    Zlength l > 0.
Proof.
  intros l Hpos.
  destruct l as [|a tl].
  - rewrite list_to_Z_nil in Hpos. lia.
  - pose proof (Zlength_nonneg tl).
    rewrite Zlength_cons. lia.
Qed.

Lemma list_first_nonzero :
  forall l,
    list_within_bound UINT_MOD l ->
    list_to_Z UINT_MOD l > 0 ->
    exists pos,
      0 <= pos < Zlength l /\
      Znth pos l 0 <> 0 /\
      (forall k, 0 <= k < pos -> Znth k l 0 = 0).
Proof.
  induction l as [|a tl IH].
  - intros _ Hpos.
    rewrite list_to_Z_nil in Hpos.
    lia.
  - intros Hbound Hpos.
    rewrite list_to_Z_cons in Hpos.
    simpl in Hbound.
    destruct Hbound as [Ha Htl].
    destruct (Z.eq_dec a 0) as [Ha0 | Ha0].
    + subst a.
      assert (Htl_pos : list_to_Z UINT_MOD tl > 0) by nia.
      specialize (IH Htl Htl_pos) as [pos [Hpos_rng [Hpos_nz Hprev]]].
      exists (pos + 1).
      split.
      * rewrite Zlength_cons. lia.
      * split.
        -- rewrite Znth_cons by lia.
           replace (pos + 1 - 1) with pos by lia.
           exact Hpos_nz.
        -- intros k Hk.
           destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
           ++ subst k. rewrite Znth0_cons. reflexivity.
           ++ rewrite Znth_cons by lia.
              apply Hprev.
              lia.
    + exists 0.
      split.
      * pose proof (Zlength_nonneg tl).
        rewrite Zlength_cons. lia.
      * split.
        -- rewrite Znth0_cons. exact Ha0.
        -- intros k Hk. lia.
Qed.

Lemma land_uint_max_id :
  forall x,
    0 <= x <= 4294967295 ->
    Z.land x 4294967295 = x.
Proof.
  intros x Hx.
  replace 4294967295 with (Z.ones 32) by reflexivity.
  rewrite Z.land_ones by lia.
  apply Z.mod_small.
  unfold UINT_MOD in Hx.
  lia.
Qed.

Lemma gmp_scan1_limb_zero :
  forall l,
    list_within_bound UINT_MOD l ->
    Zlength l > 0 ->
    gmp_scan1_limb l 0 = Znth 0 l 0.
Proof.
  intros l Hbound Hlen.
  unfold gmp_scan1_limb, gmp_scan1_mask.
  change (0 / 32) with 0.
  change (0 mod 32) with 0.
  change (Z.shiftl 4294967295 0) with 4294967295.
  assert (Hmask : unsigned_last_nbits 4294967295 32 = 4294967295).
  {
    unfold unsigned_last_nbits, UINT_MOD.
    vm_compute. reflexivity.
  }
  rewrite Hmask.
  apply land_uint_max_id.
  pose proof (list_within_bound_Znth_bound UINT_MOD l 0 ltac:(lia) Hbound) as Hnth.
  change UINT_MOD with 4294967296 in Hnth.
  lia.
Qed.

Lemma mpn_scan1_target_0_of_positive :
  forall l z,
    z > 0 ->
    list_to_Z UINT_MOD l = z ->
    list_within_bound UINT_MOD l ->
    mpn_scan1_target l 0.
Proof.
  intros l z Hz Hval Hbound.
  pose proof (list_first_nonzero l Hbound ltac:(lia)) as [pos [Hpos_rng [Hpos_nz Hprev]]].
  unfold mpn_scan1_target.
  split; [lia|].
  exists pos.
  unfold mpn_common_scan_target.
  assert (Hlen_pos : Zlength l > 0) by lia.
  rewrite gmp_scan1_limb_zero by assumption.
  pose proof (list_within_bound_Znth_bound UINT_MOD l 0 ltac:(lia) Hbound) as H0bound.
  change UINT_MOD with 4294967296 in H0bound.
  split; [left; reflexivity|].
  split.
  { lia. }
  split.
  { change (0 / 32) with 0. lia. }
  split.
  { lia. }
  change (0 / 32) with 0.
  destruct (Z.eq_dec pos 0) as [Hpos0 | Hpos0].
  { left.
    split; [lia|].
    subst pos.
    exact Hpos_nz. }
  { right.
    split; [lia|].
    split.
    { apply Hprev. lia. }
    split.
    { intros k Hk.
      unfold gmp_scan_limb.
      rewrite Z.lxor_0_l.
      apply Hprev.
      lia. }
    split.
    { intros k Hk. lia. }
    unfold gmp_scan_limb.
    rewrite Z.lxor_0_l.
    exact Hpos_nz. }
Qed.

Lemma mpn_scan1_result_mod_pow2_zero :
  forall l z shift,
    list_to_Z UINT_MOD l = z ->
    mpn_scan1_result l 0 shift ->
    z mod 2 ^ shift = 0.
Proof.
  intros l z shift Hval Hres.
  unfold mpn_scan1_result in Hres.
  destruct Hres as [[Hshift0 Hshift_bound] [Hbit Hlow]].
  rewrite <- Hval.
  apply Z.bits_inj_0.
  intros n.
  destruct (Z_lt_ge_dec n 0) as [Hnneg | Hnnonneg].
  - rewrite Z.testbit_neg_r by lia. reflexivity.
  - destruct (Z_lt_ge_dec n shift) as [Hnlt | Hnge].
    + rewrite Z.mod_pow2_bits_low by lia.
      apply Hlow. lia.
    + rewrite Z.mod_pow2_bits_high; lia.
Qed.

Lemma mpn_scan1_result_make_odd :
  forall l z shift,
    z > 0 ->
    list_to_Z UINT_MOD l = z ->
    mpn_scan1_result l 0 shift ->
    z = Z.quot z (2 ^ shift) * 2 ^ shift /\
    Z.quot z (2 ^ shift) mod 2 = 1 /\
    Z.quot z (2 ^ shift) > 0.
Proof.
  intros l z shift Hz Hval Hres.
  unfold mpn_scan1_result in Hres.
  destruct Hres as [[Hshift0 Hshift_bound] [Hbit Hlow]].
  assert (Hpowpos : 0 < 2 ^ shift) by (apply Z.pow_pos_nonneg; lia).
  assert (Hquotdiv : Z.quot z (2 ^ shift) = z / 2 ^ shift).
  { apply Z.quot_div_nonneg; lia. }
  assert (Hmodzero : z mod 2 ^ shift = 0).
  {
    apply (mpn_scan1_result_mod_pow2_zero l z shift); auto.
    unfold mpn_scan1_result. repeat split; try lia; auto.
  }
  assert (Hdecomp : z = (z / 2 ^ shift) * 2 ^ shift).
  {
    pose proof (Z.div_mod z (2 ^ shift) ltac:(lia)) as Hdiv.
    rewrite Hmodzero in Hdiv.
    lia.
  }
  assert (Hodd : (z / 2 ^ shift) mod 2 = 1).
  {
    apply (proj1 (Z.testbit_true z shift ltac:(lia))).
    rewrite <- Hval. exact Hbit.
  }
  assert (Hdivpos : z / 2 ^ shift > 0).
  {
    pose proof (Z.div_pos z (2 ^ shift) ltac:(lia) ltac:(lia)) as Hnonneg.
    destruct (Z.eq_dec (z / 2 ^ shift) 0) as [Hzero | Hnz].
    - rewrite Hzero in Hodd. lia.
    - lia.
  }
  rewrite Hquotdiv.
  repeat split; assumption.
Qed.
