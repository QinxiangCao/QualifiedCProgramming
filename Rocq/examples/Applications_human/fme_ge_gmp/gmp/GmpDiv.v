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

Definition GMP_DIV_FLOOR : Z := 0.
Definition GMP_DIV_CEIL : Z := 1.
Definition GMP_DIV_TRUNC : Z := 2.

Definition valid_mpz_div_round_mode (mode: Z): Prop :=
  mode = GMP_DIV_TRUNC \/ mode = GMP_DIV_FLOOR \/ mode = GMP_DIV_CEIL.

Definition mpz_div_qr_math_trunc (mode zn zd qv rv: Z): Prop :=
  zd <> 0 /\
  mode = GMP_DIV_TRUNC /\
  zn = qv * zd + rv /\
  Z.abs rv < Z.abs zd /\
  (rv = 0 \/ same_sign rv zn).

Definition mpz_div_qr_math_floor (mode zn zd qv rv: Z): Prop :=
  zd <> 0 /\
  mode = GMP_DIV_FLOOR /\
  zn = qv * zd + rv /\
  Z.abs rv < Z.abs zd /\
  (rv = 0 \/ same_sign rv zd).

Definition mpz_div_qr_math_ceil (mode zn zd qv rv: Z): Prop :=
  zd <> 0 /\
  mode = GMP_DIV_CEIL /\
  zn = qv * zd + rv /\
  Z.abs rv < Z.abs zd /\
  (rv = 0 \/ same_sign rv (- zd)).

Definition mpz_div_qr_math (mode zn zd qv rv: Z): Prop :=
  mpz_div_qr_math_trunc mode zn zd qv rv \/
  mpz_div_qr_math_floor mode zn zd qv rv \/
  mpz_div_qr_math_ceil mode zn zd qv rv.

Definition mpz_div_qr_small_q0_case (mode qs: Z): Prop :=
  mode = GMP_DIV_TRUNC \/
  (mode = GMP_DIV_FLOOR /\ 0 <= qs) \/
  (mode = GMP_DIV_CEIL /\ qs < 0).

Lemma mpz_div_qr_math_zero_all_modes : forall mode zd,
  valid_mpz_div_round_mode mode ->
  zd <> 0 ->
  mpz_div_qr_math mode 0 zd 0 0.
Proof.
  intros mode zd Hmode Hzd.
  unfold valid_mpz_div_round_mode in Hmode.
  destruct Hmode as [Hmode | [Hmode | Hmode]]; subst mode.
  - unfold mpz_div_qr_math; left.
    unfold mpz_div_qr_math_trunc, GMP_DIV_TRUNC; repeat split; try lia; try ring.
  - unfold mpz_div_qr_math; right; left.
    unfold mpz_div_qr_math_floor, GMP_DIV_FLOOR; repeat split; try lia; try ring.
  - unfold mpz_div_qr_math; right; right.
    unfold mpz_div_qr_math_ceil, GMP_DIV_CEIL; repeat split; try lia; try ring.
Qed.

Lemma mpz_div_qr_math_small_remainder : forall mode zn zd ns ds,
  valid_mpz_div_round_mode mode ->
  mpz_div_qr_small_q0_case mode (Z.lxor ds ns) ->
  zn <> 0 ->
  zd <> 0 ->
  same_sign zn ns ->
  same_sign zd ds ->
  Z.abs zn < Z.abs zd ->
  mpz_div_qr_math mode zn zd 0 zn.
Proof.
  intros mode zn zd ns ds Hvalid Hcase Hzn Hzd Hzn_sign Hzd_sign Hlt.
  unfold mpz_div_qr_small_q0_case in Hcase.
  destruct Hcase as [Hmode | [[Hmode Hxor] | [Hmode Hxor]]]; subst mode.
  - unfold mpz_div_qr_math; left.
    unfold mpz_div_qr_math_trunc, GMP_DIV_TRUNC.
    repeat split; try lia; try ring.
    right. apply same_sign_refl.
  - unfold mpz_div_qr_math; right; left.
    unfold mpz_div_qr_math_floor, GMP_DIV_FLOOR.
    repeat split; try lia; try ring.
    right.
    pose proof (proj1 (Z.lxor_nonneg ds ns) Hxor) as Hsame_ds_ns.
    unfold same_sign in *.
    destruct Hzn_sign as [[Hzn0 Hns0] | [Hzn0 Hns0]];
    destruct Hzd_sign as [[Hzd0 Hds0] | [Hzd0 Hds0]]; try lia;
    specialize (Hsame_ds_ns ltac:(lia)); lia.
  - unfold mpz_div_qr_math; right; right.
    unfold mpz_div_qr_math_ceil, GMP_DIV_CEIL.
    repeat split; try lia; try ring.
    right.
    destruct (Z_lt_ge_dec (Z.lxor ds ns) 0) as [_ | Hnonneg]; [|lia].
    destruct (Z_lt_ge_dec ds 0); destruct (Z_lt_ge_dec ns 0);
      try (pose proof (proj2 (Z.lxor_nonneg ds ns) ltac:(split; intro; lia)) as Hnonneg; lia);
      unfold same_sign in *;
      destruct Hzn_sign as [[Hzn0 Hns0] | [Hzn0 Hns0]];
      destruct Hzd_sign as [[Hzd0 Hds0] | [Hzd0 Hds0]]; lia.
Qed.

Definition mpz_div_qr_ret_ok (rn rv: Z): Prop :=
  (rn = 0 -> rv = 0) /\ (rn <> 0 -> rv <> 0).

Lemma mpd_store_Z_compact_read0_ret_ok : forall ptr n size r,
  Zabs r = n ->
  mpd_store_Z_compact_read0 ptr n size |-- “ mpz_div_qr_ret_ok size r ”.
Proof.
  intros ptr n size r Habs.
  unfold mpd_store_Z_compact_read0.
  Intros data.
  destruct H as [Hval [Hlast [Hbound Hsize]]].
  normalize; try cancel; try dump_pre_spatial; try lia.
  unfold mpz_div_qr_ret_ok.
  split; intros Hs.
  - assert (Hlen0 : Zlength data = 0) by lia.
    apply Zlength_nil_inv in Hlen0.
    subst data.
    rewrite list_to_Z_nil in Hval.
    lia.
  - intro Hr.
    subst r.
    rewrite Z.abs_0 in Habs.
    subst n.
    destruct data as [|a data].
    + rewrite Zlength_nil in Hsize. lia.
    + assert (Hpos : 0 < list_to_Z UINT_MOD (a :: data)).
      { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos (a :: data) Hbound Hlast) as Hcompact.
        pose proof (Zlength_nonneg data) as Hlen.
        rewrite Zlength_cons in Hcompact.
        replace (Z.succ (Zlength data) - 1) with (Zlength data) in Hcompact by lia.
        pose proof (Z.pow_pos_nonneg UINT_MOD (Zlength data) UINT_MOD_pos ltac:(lia)).
        lia. }
      lia.
Qed.

Lemma mpd_store_Z_compact_ret_ok : forall ptr n size r,
  Zabs r = n ->
  mpd_store_Z_compact UINT_MOD ptr n size |--
    “ mpz_div_qr_ret_ok size r ”.
Proof.
  intros ptr n size r Habs.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr n size).
  Intros.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos n size H)
    as [Hsize Hshape].
  normalize; try cancel; try dump_pre_spatial; try lia.
  unfold mpz_div_qr_ret_ok.
  split.
  - intro Hzero.
    destruct Hshape as [[_ Hnzero] | [Hpositive _]]; [|lia].
    rewrite <- Habs in Hnzero.
    destruct r; simpl in Hnzero; lia.
  - intros Hnonzero Hrzero.
    subst r; rewrite Z.abs_0 in Habs.
    destruct Hshape as [[Hsz _] | [Hpositive [Hlower _]]].
    + contradiction.
    + pose proof (Z.pow_pos_nonneg UINT_MOD (size - 1)
                    UINT_MOD_pos ltac:(lia)); lia.
Qed.

Lemma same_sign_same_abs_eq : forall n s1 s2,
  n <> 0 ->
  same_sign n s1 ->
  same_sign n s2 ->
  Zabs s1 = Zabs s2 ->
  s1 = s2.
Proof.
  intros n s1 s2 Hn Hs1 Hs2 Habs.
  unfold same_sign in Hs1, Hs2.
  destruct Hs1 as [[Hn1 Hs1] | [Hn1 Hs1]];
    destruct Hs2 as [[Hn2 Hs2] | [Hn2 Hs2]]; lia.
Qed.

Lemma mpd_store_Z_compact_view : forall ptr n size,
  mpd_store_Z_compact UINT_MOD ptr n size |--
    EX data,
      “ list_to_Z UINT_MOD data = n /\
        last data 1 >= 1 /\
        list_within_bound UINT_MOD data ” &&
      “ size = Zlength data ” &&
      UIntArray.full ptr size data.
Proof.
  intros ptr n size.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  subst size.
  Exists data.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + exact H.
    + reflexivity.
Qed.

Lemma mpz_div_qr_pack_remainder_store :
  forall tr ptr n signed_size used mid high cap l_tail r,
    Zabs r = n ->
    Zabs signed_size = used ->
    same_sign r signed_size ->
    used <= mid ->
    mid <= high ->
    high <= cap ->
    mpd_store_Z_compact UINT_MOD ptr n used **
    UIntArray.undef_seg ptr used mid **
    UIntArray.seg ptr mid high l_tail **
    UIntArray.undef_seg ptr high cap **
    &(tr # "__mpz_struct" ->ₛ "_mp_size") # Int |-> signed_size **
    &(tr # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap **
    &(tr # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr
    |-- store_Z tr r.
Proof.
  intros tr ptr n signed_size used mid high cap l_tail r
    Hr Hsize Hsign Hused_mid Hmid_high Hhigh_cap.
  subst n used.
  sep_apply_l_atomic (UIntArray.seg_to_undef_seg ptr mid high l_tail).
  sep_apply
    (UIntArray.undef_seg_merge_to_undef_seg
      ptr (Zabs signed_size) mid high ltac:(lia)).
  sep_apply
    (UIntArray.undef_seg_merge_to_undef_seg
      ptr (Zabs signed_size) high cap ltac:(lia)).
  sep_apply (store_Z_from_fields tr ptr signed_size cap r ltac:(lia) Hsign).
  cancel.
Qed.

Lemma same_sign_or_zero_abs_nonneg : forall x s a,
  same_sign_or_zero x s -> Zabs x = a -> s >= 0 -> x = a.
Proof.
  intros x s a Hsign Habs Hs.
  unfold same_sign_or_zero, same_sign in Hsign.
  destruct Hsign as [Hx0 | [[Hx Hs'] | [Hx Hs']]]; lia.
Qed.

Lemma same_sign_or_zero_abs_neg : forall x s a,
  same_sign_or_zero x s -> Zabs x = a -> s < 0 -> x = - a.
Proof.
  intros x s a Hsign Habs Hs.
  unfold same_sign_or_zero, same_sign in Hsign.
  destruct Hsign as [Hx0 | [[Hx Hs'] | [Hx Hs']]]; lia.
Qed.

Lemma mpz_div_qr_math_from_abs_trunc_signs : forall mode zn zd qv rv qout rout ns ds qs,
  mode = GMP_DIV_TRUNC ->
  zd <> 0 ->
  zn <> 0 ->
  same_sign zn ns ->
  same_sign zd ds ->
  qs = Z.lxor ds ns ->
  same_sign_or_zero qout qs ->
  Zabs qout = qv ->
  same_sign_or_zero rout ns ->
  Zabs rout = rv ->
  Zabs zn = qv * Zabs zd + rv ->
  0 <= rv ->
  rv < Zabs zd ->
  mpz_div_qr_math_trunc mode zn zd qout rout.
Proof.
  intros mode zn zd qv rv qout rout ns ds qs Hmode Hzd Hzn Hzn_ns Hzd_ds Hqs Hqsign Hqabs Hrsign Hrabs Habsdiv Hrv0 Hrvlt.
  unfold mpz_div_qr_math_trunc.
  subst mode.
  repeat split; try lia.
  - unfold same_sign in Hzn_ns, Hzd_ds.
    destruct Hzn_ns as [[Hzn_nonneg Hns_nonneg] | [Hzn_neg Hns_neg]];
    destruct Hzd_ds as [[Hzd_nonneg Hds_nonneg] | [Hzd_neg Hds_neg]].
    + assert (Hqs_nonneg : qs >= 0).
      { subst qs.
        assert (0 <= Z.lxor ds ns) by (apply (proj2 (Z.lxor_nonneg ds ns)); split; intro; lia).
        lia. }
      assert (Hqout : qout = qv) by (eapply same_sign_or_zero_abs_nonneg; eauto).
      assert (Hrout : rout = rv) by (eapply same_sign_or_zero_abs_nonneg; eauto).
      rewrite Hqout, Hrout.
      rewrite Z.abs_eq in Habsdiv by lia.
      rewrite Z.abs_eq in Habsdiv by lia.
      lia.
    + assert (Hqs_neg : qs < 0).
      { subst qs.
        destruct (Z_lt_ge_dec (Z.lxor ds ns) 0); [lia|].
        pose proof (proj1 (Z.lxor_nonneg ds ns) ltac:(lia)) as Hsame.
        lia. }
      assert (Hqout : qout = - qv) by (eapply same_sign_or_zero_abs_neg; eauto).
      assert (Hrout : rout = rv) by (eapply same_sign_or_zero_abs_nonneg; eauto).
      rewrite Hqout, Hrout.
      rewrite Z.abs_eq in Habsdiv by lia.
      rewrite Z.abs_neq in Habsdiv by lia.
      lia.
    + assert (Hqs_neg : qs < 0).
      { subst qs.
        destruct (Z_lt_ge_dec (Z.lxor ds ns) 0); [lia|].
        pose proof (proj1 (Z.lxor_nonneg ds ns) ltac:(lia)) as Hsame.
        lia. }
      assert (Hqout : qout = - qv) by (eapply same_sign_or_zero_abs_neg; eauto).
      assert (Hrout : rout = - rv) by (eapply same_sign_or_zero_abs_neg; eauto).
      rewrite Hqout, Hrout.
      rewrite Z.abs_neq in Habsdiv by lia.
      rewrite Z.abs_eq in Habsdiv by lia.
      lia.
    + assert (Hqs_nonneg : qs >= 0).
      { subst qs.
        assert (0 <= Z.lxor ds ns) by (apply (proj2 (Z.lxor_nonneg ds ns)); split; intro; lia).
        lia. }
      assert (Hqout : qout = qv) by (eapply same_sign_or_zero_abs_nonneg; eauto).
      assert (Hrout : rout = - rv) by (eapply same_sign_or_zero_abs_neg; eauto).
      rewrite Hqout, Hrout.
      rewrite Z.abs_neq in Habsdiv by lia.
      rewrite Z.abs_neq in Habsdiv by lia.
      lia.
  - destruct (Z.eq_dec rv 0) as [Hr0 | Hrneq].
    + left. assert (rout = 0) by lia. lia.
    + right.
      unfold same_sign_or_zero, same_sign in Hrsign.
      destruct Hrsign as [Hrout0 | Hrsign]; [lia |].
      unfold same_sign in *.
      destruct Hzn_ns as [[Hzn_nonneg Hns_nonneg] | [Hzn_neg Hns_neg]];
      destruct Hrsign as [[Hr_nonneg Hns_nonneg'] | [Hr_neg Hns_neg']]; lia.
Qed.

Lemma mpz_div_qr_math_exact_quotient : forall mode zn zd qv rv,
  mpz_div_qr_math mode zn zd qv rv ->
  zn = Z.quot zn zd * zd ->
  qv = Z.quot zn zd /\ rv = 0.
Proof.
  intros mode zn zd qv rv Hmath Hexact.
  assert (Hcommon :
    zd <> 0 /\ zn = qv * zd + rv /\ Z.abs rv < Z.abs zd).
  {
    unfold mpz_div_qr_math in Hmath.
    destruct Hmath as [Hmath | [Hmath | Hmath]];
      unfold mpz_div_qr_math_trunc, mpz_div_qr_math_floor, mpz_div_qr_math_ceil in Hmath;
      tauto.
  }
  destruct Hcommon as [Hzd [Hzn Hrv]].
  assert (Hrv_eq : rv = (Z.quot zn zd - qv) * zd) by lia.
  destruct (Z.eq_dec rv 0) as [Hrv0 | Hrvnz].
  - split.
    + apply Z.mul_reg_r with (p := zd); [lia |].
      rewrite <- Hexact.
      lia.
    + exact Hrv0.
  - assert (Hfactor : Z.quot zn zd - qv <> 0).
    { intro Hzero. apply Hrvnz. rewrite Hrv_eq, Hzero. ring. }
    rewrite Hrv_eq in Hrv.
    rewrite Z.abs_mul in Hrv.
    assert (0 < Z.abs zd) by (apply Z.abs_pos; lia).
    assert (0 <= Z.abs (Z.quot zn zd - qv)) by apply Z.abs_nonneg.
    assert (Z.abs (Z.quot zn zd - qv) <> 0).
    { intro Habs0.
      apply Hfactor.
      destruct (Z.quot zn zd - qv); simpl in Habs0; lia. }
    assert (1 <= Z.abs (Z.quot zn zd - qv)) by lia.
    nia.
Qed.

Lemma div_quotient_high_zero_compact :
  forall l_q qv rv n d nn dn qn,
    qn = nn - dn + 1 ->
    nn >= dn ->
    dn > 0 ->
    Zlength l_q = qn ->
    list_within_bound UINT_MOD l_q ->
    list_to_Z UINT_MOD l_q = qv ->
    Znth (qn - 1) l_q 0 = 0 ->
    is_compact_Z UINT_MOD n nn ->
    is_compact_Z UINT_MOD d dn ->
    n = qv * d + rv ->
    0 <= rv ->
    rv < d ->
    0 < d ->
    is_compact_Z UINT_MOD qv (qn - 1).
Proof.
  intros l_q qv rv n d nn dn qn Hqn Hnn Hdn Hqlen Hqbound
         Hqval Hqhigh Hncompact Hdcompact Hdiv Hrv_nonneg Hrv_lt Hdpos.
  assert (Hqn_pos : qn > 0) by lia.
  assert (Hq_nonneg : 0 <= qv).
  {
    rewrite <- Hqval.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_q Hqbound) as Hb.
    lia.
  }
  assert (Hq_upper : qv < UINT_MOD ^ (qn - 1)).
  {
    assert (Hprefix_val :
      list_to_Z UINT_MOD (sublist 0 (qn - 1) l_q) = qv).
    { rewrite <- Hqval. apply list_to_Z_high_zero_prefix; try lia. }
    rewrite <- Hprefix_val.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos
      (sublist 0 (qn - 1) l_q)) as Hb.
    specialize (Hb (list_within_bound_sublist UINT_MOD l_q 0 (qn - 1)
      ltac:(lia) ltac:(lia) Hqbound)).
    rewrite Zlength_sublist in Hb by lia.
    replace (qn - 1 - 0) with (qn - 1) in Hb by lia.
    lia.
  }
  apply is_compact_Z_from_bounds; [unfold UINT_MOD; lia | lia |].
  destruct (Z.eq_dec (qn - 1) 0) as [Hsize0 | Hsize_nonzero].
  - left. split; [lia |].
    assert (Hprefix_val :
      list_to_Z UINT_MOD (sublist 0 (qn - 1) l_q) = qv).
    { rewrite <- Hqval. apply list_to_Z_high_zero_prefix; try lia. }
    rewrite <- Hprefix_val.
    rewrite Hsize0.
    rewrite Zsublist_nil by lia.
    rewrite list_to_Z_nil.
    reflexivity.
  - right. split; [lia |].
    split; [| exact Hq_upper].
    pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos n nn Hncompact)
      as [_ Hn_bounds].
    pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos d dn Hdcompact)
      as [_ Hd_bounds].
    assert (Hn_low : UINT_MOD ^ (nn - 1) <= n).
    { destruct Hn_bounds as [[Hn0 Hz0] | [Hnpos [Hlo _]]]; lia. }
    assert (Hd_upper : d < UINT_MOD ^ dn).
    { destruct Hd_bounds as [[Hd0 Hdz0] | [Hdnpos [_ Hdhi]]]; lia. }
    destruct (Z_lt_ge_dec qv (UINT_MOD ^ (qn - 2))) as [Hbad | Hgood].
    2: { replace (qn - 1 - 1) with (qn - 2) by lia. lia. }
    set (P := UINT_MOD ^ (qn - 2)).
    set (D := UINT_MOD ^ dn).
    assert (HPpos : 0 < P).
    { subst P. apply Z.pow_pos_nonneg; unfold UINT_MOD; lia. }
    assert (HDpos : 0 < D).
    { subst D. apply Z.pow_pos_nonneg; unfold UINT_MOD; lia. }
    assert (Hpow : P * D = UINT_MOD ^ (nn - 1)).
    {
      assert (Hexp : qn - 2 + dn = nn - 1).
      { rewrite Hqn. ring. }
      subst P D.
      rewrite <- Z.pow_add_r by (unfold UINT_MOD; lia).
      rewrite Hexp.
      reflexivity.
    }
    assert (Hrv_le : rv <= d - 1) by lia.
    assert (Hq_le : qv <= P - 1) by (subst P; lia).
    assert (Hn_bad : n <= P * D - 1).
    {
      rewrite Hdiv.
      assert (Hq_mul_le : qv * d <= (P - 1) * d).
      { apply Z.mul_le_mono_nonneg_r; lia. }
      assert (Hstep1 : qv * d + rv <= P * d - 1).
      {
        assert (Hsum_le : qv * d + rv <= (P - 1) * d + (d - 1)).
        { apply Z.add_le_mono; assumption. }
        assert (Hrhs_eq : (P - 1) * d + (d - 1) = P * d - 1) by ring.
        rewrite <- Hrhs_eq.
        exact Hsum_le.
      }
      assert (Hstep2 : P * d <= P * D).
      {
        assert (Hd_le_D : d <= D) by (subst D; lia).
        assert (HP_nonneg : 0 <= P) by lia.
        apply Z.mul_le_mono_nonneg_l; assumption.
      }
      assert (Hstep3 : P * d - 1 <= P * D - 1) by lia.
      eapply Z.le_trans; [exact Hstep1 | exact Hstep3].
    }
    rewrite <- Hpow in Hn_low.
    exfalso.
    apply (Z.lt_irrefl (P * D)).
    eapply Z.le_lt_trans; [exact Hn_low |].
    assert (Hbad_lt : n < P * D) by lia.
    exact Hbad_lt.
Qed.

Definition optional_store_Z (x: addr) (z: Z): Assertion :=
  “ x = NULL ” && emp ||
  “ x <> NULL ” && store_Z x z.

Lemma optional_store_Z_nonzero : forall x z,
  x <> NULL -> optional_store_Z x z |-- store_Z x z.
Proof.
  intros.
  unfold optional_store_Z.
  Split.
  - Intros_p Hnull.
    assert (False) by (unfold NULL in *; lia). contradiction.
  - Intros_p Hnonnull. cancel.
Qed.

Lemma store_Z_to_optional_store_Z_nonzero : forall x z,
  x <> NULL -> store_Z x z |-- optional_store_Z x z.
Proof.
  intros.
  unfold optional_store_Z.
  Right.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial; auto.
Qed.

Lemma emp_to_optional_store_Z_null : forall x z,
  x = NULL -> emp |-- optional_store_Z x z.
Proof.
  intros.
  subst x.
  unfold optional_store_Z.
  Left.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial; auto.
Qed.

Lemma optional_store_Z_null_change : forall x a b,
  x = NULL -> optional_store_Z x a |-- optional_store_Z x b.
Proof.
  intros.
  unfold optional_store_Z.
  Split.
  - Intros_p Hnull. Left.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial; auto.
  - Intros_p Hnonnull.
    assert (False) by (unfold NULL in *; lia). contradiction.
Qed.

Definition div_inverse_den (dn d1 d0: Z): Z :=
  if Z.eq_dec dn 1 then UINT_MOD * d1 else UINT_MOD * d1 + d0.

Definition gmp_div_inverse_valid
  (dn d shift d1 d0 di: Z): Prop :=
  1 <= dn <= INT_MAX /\
  0 < d /\
  0 <= shift < 32 /\
  0 <= d1 <= UINT_MAX /\
  0 <= d0 <= UINT_MAX /\
  0 <= di <= UINT_MAX /\
  d * 2 ^ shift < UINT_MOD ^ dn /\
  ((dn = 1 /\ d1 = d * 2 ^ shift) \/
   (dn > 1 /\
    d1 * UINT_MOD + d0 = (d * 2 ^ shift) / UINT_MOD ^ (dn - 2))) /\
  UINT_MOD / 2 <= d1 /\
  (di + UINT_MOD) * div_inverse_den dn d1 d0 <= UINT_MOD ^ 3 - 1 /\
  UINT_MOD ^ 3 - 1 <
    (di + UINT_MOD + 1) * div_inverse_den dn d1 d0.

Definition div_inverse_fields
  (inv: addr) (shift d1 d0 di: Z): Assertion :=
  &(inv # "gmp_div_inverse" ->ₛ "shift") # UInt |-> shift **
  &(inv # "gmp_div_inverse" ->ₛ "d1") # UInt |-> d1 **
  &(inv # "gmp_div_inverse" ->ₛ "d0") # UInt |-> d0 **
  &(inv # "gmp_div_inverse" ->ₛ "di") # UInt |-> di.

Definition div_inverse_store
  (inv: addr) (dn shift d1 d0 di: Z): Assertion :=
  &(inv # "gmp_div_inverse" ->ₛ "shift") # UInt |-> shift **
  &(inv # "gmp_div_inverse" ->ₛ "d1") # UInt |-> d1 **
  (if Z.eq_dec dn 1
   then &(inv # "gmp_div_inverse" ->ₛ "d0") # UInt |->_
   else &(inv # "gmp_div_inverse" ->ₛ "d0") # UInt |-> d0) **
  &(inv # "gmp_div_inverse" ->ₛ "di") # UInt |-> di.

Definition div_inverse_slot (inv: addr): Assertion :=
  &(inv # "gmp_div_inverse" ->ₛ "shift") # UInt |->_ **
  &(inv # "gmp_div_inverse" ->ₛ "d1") # UInt |->_ **
  &(inv # "gmp_div_inverse" ->ₛ "d0") # UInt |->_ **
  &(inv # "gmp_div_inverse" ->ₛ "di") # UInt |->_.

Definition store_div_inverse (inv: addr) (dn d: Z): Assertion :=
  EX shift d1 d0 di,
    “ gmp_div_inverse_valid dn d shift d1 d0 di ” &&
    div_inverse_store inv dn shift d1 d0 di.

Lemma store_div_inverse_to_slot : forall inv dn d,
  store_div_inverse inv dn d |-- div_inverse_slot inv.
Proof.
  intros inv dn d.
  unfold store_div_inverse, div_inverse_slot, div_inverse_store.
  Intros shift d1 d0 di.
  sep_apply (store_uint_undef_store_uint (&(inv # "gmp_div_inverse" ->ₛ "shift")) shift).
  sep_apply (store_uint_undef_store_uint (&(inv # "gmp_div_inverse" ->ₛ "d1")) d1).
  destruct (Z.eq_dec dn 1).
  - sep_apply (store_uint_undef_store_uint (&(inv # "gmp_div_inverse" ->ₛ "di")) di).
    normalize; try cancel; try dump_pre_spatial; try lia.
  - sep_apply (store_uint_undef_store_uint (&(inv # "gmp_div_inverse" ->ₛ "d0")) d0).
    sep_apply (store_uint_undef_store_uint (&(inv # "gmp_div_inverse" ->ₛ "di")) di).
    normalize; try cancel; try dump_pre_spatial; try lia.
Qed.

Definition preinv_dp_value (dn d shift: Z): Z :=
  if Z.gtb dn 2 then d * 2 ^ shift else d.

Definition store_preinv_divisor (dp inv: addr) (dn d: Z): Assertion :=
  EX l_dp shift d1 d0 di,
    “ gmp_div_inverse_valid dn d shift d1 d0 di ” &&
    “ Zlength l_dp = dn ” &&
    “ list_within_bound UINT_MOD l_dp ” &&
    “ list_to_Z UINT_MOD l_dp = preinv_dp_value dn d shift ” &&
    UIntArray.full dp dn l_dp **
    div_inverse_store inv dn shift d1 d0 di.

Definition optional_q_undef (qp qn: Z): Assertion :=
  “ qp = NULL ” && emp ||
  “ qp <> NULL ” && UIntArray.undef_full qp qn.

Definition optional_q_full (qp qn: Z) (l_q: list Z): Assertion :=
  “ qp = NULL ” && emp ||
  “ qp <> NULL ” && UIntArray.full qp qn l_q.

Lemma list_to_Z_high_limb_quot_uint_for_div :
  forall (l : list Z) n,
    Zlength l = n ->
    1 <= n ->
    list_within_bound UINT_MOD l ->
    list_to_Z UINT_MOD l / UINT_MOD ^ (n - 1) = Znth (n - 1) l 0.
Proof.
  intros l n Hlen Hn Hbound.
  pose proof (list_to_Z_nth UINT_MOD UINT_MOD_pos l n (n - 1)
                ltac:(rewrite Hlen; lia) Hbound) as Hnth.
  rewrite Hnth.
  symmetry.
  apply Z.mod_small.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l Hbound) as Hval.
  split.
  - apply Z.div_pos.
    + lia.
    + apply Z.pow_pos_nonneg; unfold UINT_MOD; lia.
  - apply Z.div_lt_upper_bound.
    + apply Z.pow_pos_nonneg; unfold UINT_MOD; lia.
    + rewrite Hlen in Hval.
      replace (UINT_MOD ^ (n - 1) * UINT_MOD)
        with (UINT_MOD ^ n).
      * lia.
      * assert (Hpow_eq : UINT_MOD ^ n = UINT_MOD ^ (n - 1) * UINT_MOD).
        {
          replace UINT_MOD with (UINT_MOD ^ 1) at 3
            by (rewrite Z.pow_1_r; reflexivity).
          rewrite <- Z.pow_add_r by lia.
          f_equal.
          lia.
        }
        exact Hpow_eq.
Qed.

Lemma list_to_Z_high2_quot_uint_for_div :
  forall (l : list Z) n,
    Zlength l = n ->
    2 <= n ->
    list_within_bound UINT_MOD l ->
    list_to_Z UINT_MOD l / UINT_MOD ^ (n - 2) =
      Znth (n - 2) l 0 + Znth (n - 1) l 0 * UINT_MOD.
Proof.
  intros l n Hlen Hn Hbound.
  pose proof (sublist_split 0 n (n - 2) l ltac:(lia) ltac:(lia)) as Hsplit.
  rewrite (sublist_self l n ltac:(lia)) in Hsplit.
  assert (Htail_bound:
            list_within_bound UINT_MOD
              (sublist 0 (n - 2) l ++ sublist (n - 2) n l)).
  {
    rewrite <- Hsplit.
    exact Hbound.
  }
  pose proof (list_to_Z_split UINT_MOD UINT_MOD_pos
    (sublist 0 (n - 2) l) (sublist (n - 2) n l) Htail_bound) as [_ Hquot].
  rewrite Zlength_sublist in Hquot by lia.
  replace (n - 2 - 0) with (n - 2) in Hquot by lia.
  rewrite <- Hsplit in Hquot.
  rewrite <- Hquot.
  rewrite (sublist_split (n - 2) n (n - 1) l) by lia.
  replace (sublist (n - 2) (n - 1) l)
    with (sublist (n - 2) ((n - 2) + 1) l) by (f_equal; lia).
  rewrite (sublist_single 0 (n - 2) l) by lia.
  replace (sublist (n - 1) n l)
    with (sublist (n - 1) ((n - 1) + 1) l) by (f_equal; lia).
  rewrite (sublist_single 0 (n - 1) l) by lia.
  change (((Znth (n - 2) l 0 :: nil) ++ (Znth (n - 1) l 0 :: nil))%list)
    with (Znth (n - 2) l 0 :: Znth (n - 1) l 0 :: nil).
  rewrite !list_to_Z_cons, list_to_Z_nil.
  ring.
Qed.

Lemma Z_unit_interval_multiple_zero :
  forall k p r x,
    0 < p ->
    0 <= r < p ->
    0 <= x < p ->
    x = r + k * p ->
    k = 0.
Proof.
  intros k p r x Hp Hr Hx Hrel.
  assert (- p < k * p < p) by lia.
  destruct (Z_lt_dec k 0) as [Hk | Hk_nonneg].
  - assert (k <= -1) by lia.
    assert (k * p <= -1 * p).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    lia.
  - destruct (Z.eq_dec k 0) as [Hk | Hk].
    + exact Hk.
    + assert (1 <= k) by lia.
      assert (1 * p <= k * p).
      { apply Z.mul_le_mono_nonneg_r; lia. }
      lia.
Qed.

Lemma mpn_div_qr_pi1_qmax_window_nonneg :
  forall (l_mid l_dp : list Z) (dn0 n1 dval : Z),
    dn0 > 2 ->
    Zlength l_mid = dn0 ->
    Zlength l_dp = dn0 ->
    list_within_bound UINT_MOD l_mid ->
    list_within_bound UINT_MOD l_dp ->
    list_to_Z UINT_MOD l_dp = dval ->
    n1 = Znth (dn0 - 1) l_dp 0 ->
    Znth (dn0 - 1) l_mid 0 = Znth (dn0 - 2) l_dp 0 ->
    UINT_MOD / 2 <= n1 ->
    (UINT_MOD - 1) * dval <= n1 * UINT_MOD ^ dn0 + list_to_Z UINT_MOD l_mid.
Proof.
  intros l_mid l_dp dn0 n1 dval Hdn Hmid_len Hdp_len
         Hmid_bound Hdp_bound Hdval Hn1 Htop Hn1_norm.
  set (B := UINT_MOD).
  assert (HBpos : 0 < B) by (subst B; unfold UINT_MOD; lia).
  assert (HP2pos : 0 < B ^ (dn0 - 2)).
  { apply Z.pow_pos_nonneg; lia. }
  pose proof (list_to_Z_high2_quot_uint_for_div l_dp dn0
    Hdp_len ltac:(lia) Hdp_bound) as Hdp_high2.
  pose proof (list_to_Z_high_limb_quot_uint_for_div l_mid dn0
    Hmid_len ltac:(lia) Hmid_bound) as Hmid_high.
  rewrite Hdval in Hdp_high2.
  rewrite <- Hn1 in Hdp_high2.
  rewrite <- Htop in Hdp_high2.
  set (d0 := Znth (dn0 - 1) l_mid 0).
  fold B in Hdp_high2.
  fold d0 in Hdp_high2.
  fold B in Hmid_high.
  fold d0 in Hmid_high.
  set (P := B ^ (dn0 - 2)).
  assert (HPpos : 0 < P) by (subst P; exact HP2pos).
  assert (Hd_decomp :
    dval = (d0 + n1 * B) * P + dval mod P).
  {
    pose proof (Z.div_mod dval P ltac:(lia)) as Hdm.
    assert (Hdiv : dval / P = d0 + n1 * B).
    { subst P. exact Hdp_high2. }
    rewrite Hdiv in Hdm.
    subst P B d0.
    ring_simplify in Hdm.
    lia.
  }
  assert (Hd_mod_bound : 0 <= dval mod P < P).
  { apply Z.mod_pos_bound; lia. }
  assert (Hmid_decomp :
    list_to_Z UINT_MOD l_mid =
      d0 * B * P + list_to_Z UINT_MOD l_mid mod (B * P)).
  {
    pose proof (Z.div_mod (list_to_Z UINT_MOD l_mid) (B * P) ltac:(nia)) as Hdm.
    assert (B * P = B ^ (dn0 - 1)).
    {
      subst P B.
      replace (dn0 - 1) with (1 + (dn0 - 2)) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      ring.
    }
    assert (Hmiddiv : list_to_Z UINT_MOD l_mid / (B * P) = d0).
    {
      rewrite H.
      subst B.
      exact Hmid_high.
    }
    rewrite Hmiddiv in Hdm.
    ring_simplify in Hdm.
    replace (B * P * d0) with (d0 * B * P) in Hdm by ring.
    exact Hdm.
  }
  assert (Hmid_mod_bound : 0 <= list_to_Z UINT_MOD l_mid mod (B * P) < B * P).
  { apply Z.mod_pos_bound; nia. }
  fold B.
  fold B in Hmid_decomp.
  fold B in Hn1_norm.
  rewrite Hd_decomp, Hmid_decomp.
  assert (Hpowdn : B ^ dn0 = B * B * P).
  {
    subst P.
    replace dn0 with (2 + (dn0 - 2)) by lia.
    rewrite Z.pow_add_r by lia.
    change (B ^ 2) with (B * B).
    replace (2 + (dn0 - 2) - 2) with (dn0 - 2) by lia.
    reflexivity.
  }
  rewrite Hpowdn.
  assert (Hd0_bound : 0 <= d0 < B).
  {
    subst d0 B.
    apply (list_within_bound_Znth_bound UINT_MOD l_mid (dn0 - 1));
      try exact Hmid_bound.
    rewrite Hmid_len; lia.
  }
  assert (Hn1_ge1 : 1 <= n1).
  {
    subst B.
    unfold UINT_MOD in Hn1_norm.
    change (4294967296 / 2) with 2147483648 in Hn1_norm.
    lia.
  }
  destruct Hd_mod_bound as [Hr_nonneg Hr_lt].
  destruct Hmid_mod_bound as [Hm_nonneg Hm_lt].
  change (list_to_Z UINT_MOD l_mid) with (list_to_Z B l_mid) in Hm_nonneg.
  change (list_to_Z UINT_MOD l_mid) with (list_to_Z B l_mid) in Hm_lt.
  assert (Hr_le_pred : dval mod P <= P - 1) by lia.
  assert (Hmul_r_bound :
    (B - 1) * (dval mod P) <= (B - 1) * (P - 1)).
  {
    apply Z.mul_le_mono_nonneg_l; lia.
  }
  assert (Hcoeff : B - 1 <= n1 * B + d0) by nia.
  assert (Hmul_coeff_bound : (B - 1) * (P - 1) <= (n1 * B + d0) * P) by nia.
  nia.
Qed.

Lemma mpn_div_qr_pi1_qmax_transition :
  forall (l_cur l_low l_mid l_high l_out l_dp : list Z)
         (dn0 nn0 i n1 dval val_out retval remv_2 : Z),
    dn0 > 2 ->
    0 <= i ->
    i <= nn0 - dn0 ->
    Zlength l_cur = nn0 ->
    Zlength l_low = i ->
    Zlength l_mid = dn0 ->
    Zlength l_high = nn0 - (i + dn0) ->
    Zlength l_out = dn0 ->
    Zlength l_dp = dn0 ->
    l_low = sublist 0 i l_cur ->
    l_mid = sublist i (i + dn0) l_cur ->
    l_high = sublist (i + dn0) nn0 l_cur ->
    list_within_bound UINT_MOD l_cur ->
    list_within_bound UINT_MOD l_low ->
    list_within_bound UINT_MOD l_mid ->
    list_within_bound UINT_MOD l_high ->
    list_within_bound UINT_MOD l_out ->
    list_within_bound UINT_MOD l_dp ->
    list_to_Z UINT_MOD l_out = val_out ->
    val_out - retval * UINT_MOD ^ dn0 =
      list_to_Z UINT_MOD l_mid - list_to_Z UINT_MOD l_dp * 4294967295 ->
    list_to_Z UINT_MOD l_dp = dval ->
    0 < dval ->
    n1 = Znth (dn0 - 1) l_dp 0 ->
    Znth (dn0 - 1) l_mid 0 = Znth (dn0 - 2) l_dp 0 ->
    UINT_MOD / 2 <= n1 ->
    n1 <= UINT_MAX ->
    remv_2 =
      n1 * UINT_MOD ^ (dn0 + i) +
      list_to_Z UINT_MOD (sublist 0 (dn0 + i) l_cur) ->
    0 <= remv_2 ->
    remv_2 < dval * UINT_MOD ^ (i + 1) ->
    let l_new := l_low ++ l_out ++ l_high in
    let remv_new :=
      Znth (dn0 - 1) l_out 0 * UINT_MOD ^ (dn0 + (i - 1)) +
      list_to_Z UINT_MOD (sublist 0 (dn0 + (i - 1)) l_new) in
    remv_new = remv_2 - 4294967295 * dval * UINT_MOD ^ i /\
    0 <= remv_new /\
    remv_new < dval * UINT_MOD ^ i.
Proof.
  intros l_cur l_low l_mid l_high l_out l_dp
         dn0 nn0 i n1 dval val_out retval remv_2
         Hdn Hi Hirange Hcur_len Hlow_len Hmid_len Hhigh_len Hout_len Hdp_len
         Hlow Hmid Hhigh Hcur_bound Hlow_bound Hmid_bound Hhigh_bound
         Hout_bound Hdp_bound Hout_val Hsubmul Hdval Hdpos Hn1 Htop
         Hn1_norm Hn1_max Hrem Hrem_nonneg Hrem_lt.
  assert (Hold_prefix :
    list_to_Z UINT_MOD (sublist 0 (dn0 + i) l_cur) =
    list_to_Z UINT_MOD l_low + list_to_Z UINT_MOD l_mid * UINT_MOD ^ i).
  {
    rewrite (sublist_split 0 (dn0 + i) i l_cur) by (split; try lia; rewrite Hcur_len; lia).
    rewrite <- Hlow.
    replace (sublist i (dn0 + i) l_cur) with l_mid
      by (rewrite Hmid; f_equal; lia).
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hlow_len.
    reflexivity.
  }
  assert (Hout_decomp :
    val_out =
    list_to_Z UINT_MOD (sublist 0 (dn0 - 1) l_out) +
    Znth (dn0 - 1) l_out 0 * UINT_MOD ^ (dn0 - 1)).
  {
    rewrite <- Hout_val.
    rewrite <- (sublist_self l_out dn0) at 1 by (symmetry; exact Hout_len).
    rewrite (sublist_split 0 dn0 (dn0 - 1) l_out) by (try rewrite Hout_len; lia).
    replace (sublist (dn0 - 1) dn0 l_out)
      with (sublist (dn0 - 1) ((dn0 - 1) + 1) l_out) by (f_equal; lia).
    rewrite (sublist_single 0 (dn0 - 1) l_out) by (try rewrite Hout_len; lia).
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite list_to_Z_cons.
    replace (list_to_Z UINT_MOD nil) with 0 by (rewrite list_to_Z_nil; reflexivity).
    rewrite Zlength_sublist by (try rewrite Hout_len; lia).
    replace (dn0 - 1 - 0) with (dn0 - 1) by lia.
    replace (Znth (dn0 - 1) l_out 0 + UINT_MOD * 0)
      with (Znth (dn0 - 1) l_out 0) by ring.
    ring.
  }
  assert (Hnew_sub :
    sublist 0 (dn0 + (i - 1)) (l_low ++ l_out ++ l_high) =
    l_low ++ sublist 0 (dn0 - 1) l_out).
  {
    replace (dn0 + (i - 1)) with (i + (dn0 - 1)) by lia.
    rewrite (sublist_split 0 (i + (dn0 - 1)) i (l_low ++ l_out ++ l_high)).
    - replace i with (Zlength l_low) by lia.
      rewrite sublist_app_exact1.
      replace (Zlength l_low) with i by lia.
      rewrite sublist_split_app_r with (len := i).
      + rewrite sublist_split_app_l.
        * replace (i - i) with 0 by lia.
          replace (i + (dn0 - 1) - i) with (dn0 - 1) by lia.
          reflexivity.
        * lia.
        * rewrite Hout_len; lia.
      + rewrite Hlow_len; reflexivity.
      + lia.
    - lia.
    - rewrite !Zlength_app, Hlow_len, Hout_len, Hhigh_len; lia.
  }
  assert (Hnew_value :
    Znth (dn0 - 1) l_out 0 * UINT_MOD ^ (dn0 + (i - 1)) +
    list_to_Z UINT_MOD (sublist 0 (dn0 + (i - 1)) (l_low ++ l_out ++ l_high)) =
    list_to_Z UINT_MOD l_low + val_out * UINT_MOD ^ i).
  {
    rewrite Hnew_sub.
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hlow_len.
    rewrite Hout_decomp.
    replace (dn0 + (i - 1)) with ((dn0 - 1) + i) by lia.
    rewrite Z.pow_add_r by lia.
    ring.
  }
  assert (Hpow_dni :
    UINT_MOD ^ (dn0 + i) = UINT_MOD ^ dn0 * UINT_MOD ^ i).
  {
    rewrite Z.pow_add_r by (unfold UINT_MOD; lia).
    reflexivity.
  }
  assert (Hold_value :
    remv_2 =
    list_to_Z UINT_MOD l_low +
      (list_to_Z UINT_MOD l_mid + n1 * UINT_MOD ^ dn0) * UINT_MOD ^ i).
  {
    rewrite Hrem, Hold_prefix, Hpow_dni.
    ring.
  }
  assert (Hval_out_expr :
    val_out =
      list_to_Z UINT_MOD l_mid - dval * 4294967295 +
      retval * UINT_MOD ^ dn0).
  {
    rewrite <- Hdval.
    rewrite <- Hsubmul.
    ring.
  }
  set (remv_new :=
    Znth (dn0 - 1) l_out 0 * UINT_MOD ^ (dn0 + (i - 1)) +
    list_to_Z UINT_MOD (sublist 0 (dn0 + (i - 1)) (l_low ++ l_out ++ l_high))).
  set (R := remv_2 - 4294967295 * dval * UINT_MOD ^ i).
  assert (Hnew_relation :
    remv_new = R + (retval - n1) * UINT_MOD ^ (dn0 + i)).
  {
    subst remv_new R.
    rewrite Hnew_value, Hold_value, Hval_out_expr.
    rewrite Hpow_dni.
    ring.
  }
  assert (Hlow_nonneg : 0 <= list_to_Z UINT_MOD l_low).
  {
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_low Hlow_bound) as Hlow_b.
    lia.
  }
  assert (Hwindow_nonneg :
    0 <= n1 * UINT_MOD ^ dn0 + list_to_Z UINT_MOD l_mid - 4294967295 * dval).
  {
    pose proof (mpn_div_qr_pi1_qmax_window_nonneg l_mid l_dp dn0 n1 dval
      Hdn Hmid_len Hdp_len Hmid_bound Hdp_bound Hdval Hn1 Htop Hn1_norm) as Hwin.
    unfold UINT_MOD in Hwin.
    change (4294967296 - 1) with 4294967295 in Hwin.
    change UINT_MOD with 4294967296.
    lia.
  }
  assert (HR_nonneg : 0 <= R).
  {
    subst R.
    rewrite Hold_value.
    replace (list_to_Z UINT_MOD l_low +
      (list_to_Z UINT_MOD l_mid + n1 * UINT_MOD ^ dn0) * UINT_MOD ^ i -
      4294967295 * dval * UINT_MOD ^ i)
      with (list_to_Z UINT_MOD l_low +
        (n1 * UINT_MOD ^ dn0 + list_to_Z UINT_MOD l_mid -
          4294967295 * dval) * UINT_MOD ^ i) by ring.
    assert (Hpow_i_nonneg : 0 <= UINT_MOD ^ i).
    { apply Z.pow_nonneg; unfold UINT_MOD; lia. }
    apply Z.add_nonneg_nonneg; [exact Hlow_nonneg |].
    apply Z.mul_nonneg_nonneg; assumption.
  }
  assert (Hpow_i1 :
    UINT_MOD ^ (i + 1) = UINT_MOD * UINT_MOD ^ i).
  {
    replace (i + 1) with (1 + i) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    ring.
  }
  assert (HR_lt_d : R < dval * UINT_MOD ^ i).
  {
    subst R.
    rewrite Hpow_i1 in Hrem_lt.
    unfold UINT_MOD in *.
    change (4294967296 - 1) with 4294967295.
    nia.
  }
  assert (Hdval_bound : 0 <= dval < UINT_MOD ^ dn0).
  {
    rewrite <- Hdval.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_dp Hdp_bound) as Hdp_b.
    rewrite Hdp_len in Hdp_b.
    exact Hdp_b.
  }
  assert (HR_lt_pow : R < UINT_MOD ^ (dn0 + i)).
  {
    apply Z.lt_trans with (m := dval * UINT_MOD ^ i).
    - exact HR_lt_d.
    - rewrite Hpow_dni.
      apply Z.mul_lt_mono_pos_r.
      + apply Z.pow_pos_nonneg; unfold UINT_MOD; lia.
      + exact (proj2 Hdval_bound).
  }
  assert (Hnew_full :
    remv_new = list_to_Z UINT_MOD (l_low ++ l_out)).
  {
    subst remv_new.
    rewrite Hnew_value.
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hlow_len, Hout_val.
    reflexivity.
  }
  assert (Hnew_bound : 0 <= remv_new < UINT_MOD ^ (dn0 + i)).
  {
    rewrite Hnew_full.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos (l_low ++ l_out)) as Hbound.
    assert (Hjoin_bound : list_within_bound UINT_MOD (l_low ++ l_out)).
    { apply list_within_bound_concat; [exact Hlow_bound | exact Hout_bound]. }
    specialize (Hbound Hjoin_bound).
    rewrite Zlength_app, Hlow_len, Hout_len in Hbound.
    replace (i + dn0) with (dn0 + i) in Hbound by lia.
    exact Hbound.
  }
  assert (Hpow_exp_nonneg : 0 <= dn0 + i).
  {
    apply Z.add_nonneg_nonneg; [| exact Hi].
    destruct dn0; simpl in *; try discriminate; lia.
  }
  pose proof (Z.pow_pos_nonneg UINT_MOD (dn0 + i) UINT_MOD_pos Hpow_exp_nonneg)
    as Hpow_pos.
  assert (Hcoeff_zero : retval - n1 = 0).
  {
    eapply Z_unit_interval_multiple_zero.
    - exact Hpow_pos.
    - split; [exact HR_nonneg | exact HR_lt_pow].
    - exact Hnew_bound.
    - exact Hnew_relation.
  }
  assert (Hrem_eq : remv_new = R).
  {
    rewrite Hnew_relation, Hcoeff_zero.
    ring.
  }
  subst remv_new R.
  split.
  - rewrite Hrem_eq.
    reflexivity.
  - split.
    + rewrite Hrem_eq.
      exact HR_nonneg.
    + rewrite Hrem_eq.
      exact HR_lt_d.
Qed.

Lemma sublist_app_prefix_two_plus_one :
  forall (l1 l2 l3 l4 : list Z),
    1 <= Zlength l3 ->
    sublist 0 (Zlength l1 + Zlength l2 + 1) (l1 ++ l2 ++ l3 ++ l4) =
      l1 ++ l2 ++ sublist 0 1 l3.
Proof.
  intros l1 l2 l3 l4 Hlen3.
  rewrite (sublist_split 0 (Zlength l1 + Zlength l2 + 1) (Zlength l1)
    (l1 ++ l2 ++ l3 ++ l4)).
  - rewrite sublist_app_exact1.
    rewrite sublist_split_app_r with (len := Zlength l1).
    + replace (Zlength l1 - Zlength l1) with 0 by lia.
      replace (Zlength l1 + Zlength l2 + 1 - Zlength l1)
        with (Zlength l2 + 1) by lia.
      rewrite (sublist_split 0 (Zlength l2 + 1) (Zlength l2)
        (l2 ++ l3 ++ l4)).
      * rewrite sublist_app_exact1.
        rewrite sublist_split_app_r with (len := Zlength l2).
        -- replace (Zlength l2 - Zlength l2) with 0 by lia.
           replace (Zlength l2 + 1 - Zlength l2) with 1 by lia.
           rewrite sublist_split_app_l.
           ++ reflexivity.
           ++ lia.
           ++ exact Hlen3.
        -- reflexivity.
        -- lia.
      * pose proof (Zlength_nonneg l2). lia.
      * pose proof (Zlength_nonneg l2);
        pose proof (Zlength_nonneg l3);
        pose proof (Zlength_nonneg l4).
        rewrite !Zlength_app.
        split; nia.
    + reflexivity.
    + pose proof (Zlength_nonneg l2). lia.
  - pose proof (Zlength_nonneg l1). lia.
  - pose proof (Zlength_nonneg l1);
    pose proof (Zlength_nonneg l2);
    pose proof (Zlength_nonneg l3);
    pose proof (Zlength_nonneg l4).
    rewrite !Zlength_app.
    split; nia.
Qed.

Lemma mpn_div_qr_pi1_submul_no_borrow_transition :
  forall (l_cur l_low l_mid l_high l_mid_low l_mid_high l_out
          l_dp l_dp_low l_dp_high : list Z)
         (dn0 nn0 i q n1 n0 n1_in d1 d0 dval val_out retval remv_2 : Z),
    dn0 > 2 ->
    0 <= i ->
    i <= nn0 - dn0 ->
    Zlength l_cur = nn0 ->
    Zlength l_low = i ->
    Zlength l_mid = dn0 ->
    Zlength l_high = nn0 - (i + dn0) ->
    Zlength l_mid_low = dn0 - 2 ->
    Zlength l_mid_high = 2 ->
    Zlength l_out = dn0 - 2 ->
    Zlength l_dp = dn0 ->
    Zlength l_dp_low = dn0 - 2 ->
    Zlength l_dp_high = 2 ->
    l_low = sublist 0 i l_cur ->
    l_mid = sublist i (i + dn0) l_cur ->
    l_high = sublist (i + dn0) nn0 l_cur ->
    l_mid_low = sublist 0 (dn0 - 2) l_mid ->
    l_mid_high = sublist (dn0 - 2) dn0 l_mid ->
    l_dp_low = sublist 0 (dn0 - 2) l_dp ->
    l_dp_high = sublist (dn0 - 2) dn0 l_dp ->
    list_within_bound UINT_MOD l_low ->
    list_within_bound UINT_MOD l_mid ->
    list_within_bound UINT_MOD l_high ->
    list_within_bound UINT_MOD l_mid_low ->
    list_within_bound UINT_MOD l_mid_high ->
    list_within_bound UINT_MOD l_out ->
    list_within_bound UINT_MOD l_dp ->
    list_within_bound UINT_MOD l_dp_low ->
    list_within_bound UINT_MOD l_dp_high ->
    list_to_Z UINT_MOD l_out = val_out ->
    val_out - retval * UINT_MOD ^ (dn0 - 2) =
      list_to_Z UINT_MOD l_mid_low - list_to_Z UINT_MOD l_dp_low * q ->
    list_to_Z UINT_MOD l_dp = dval ->
    d1 = Znth (dn0 - 1) l_dp 0 ->
    d0 = Znth (dn0 - 2) l_dp 0 ->
    0 <= n1 ->
    0 <= retval ->
    n0 >= retval ->
    n1_in * UINT_MOD ^ 2 + Znth (dn0 - 1) l_mid 0 * UINT_MOD +
      Znth (dn0 - 2) l_mid 0 =
      q * (d1 * UINT_MOD + d0) + n1 * UINT_MOD + n0 ->
    n1 * UINT_MOD + n0 < d1 * UINT_MOD + d0 ->
    remv_2 =
      n1_in * UINT_MOD ^ (dn0 + i) +
      list_to_Z UINT_MOD (sublist 0 (dn0 + i) l_cur) ->
    let l_repl := replace_Znth 0 (n0 - retval) l_mid_high in
    let l_new := l_low ++ l_out ++ l_repl ++ l_high in
    let remv_new :=
      n1 * UINT_MOD ^ (dn0 + (i - 1)) +
      list_to_Z UINT_MOD (sublist 0 (dn0 + (i - 1)) l_new) in
    remv_new = remv_2 - q * dval * UINT_MOD ^ i /\
    0 <= remv_new /\
    remv_new < dval * UINT_MOD ^ i.
Proof.
  intros l_cur l_low l_mid l_high l_mid_low l_mid_high l_out
         l_dp l_dp_low l_dp_high
         dn0 nn0 i q n1 n0 n1_in d1 d0 dval val_out retval remv_2
         Hdn Hi Hirange Hcur_len Hlow_len Hmid_len Hhigh_len
         Hmidlow_len Hmidhigh_len Hout_len Hdp_len Hdplow_len Hdphigh_len
         Hlow Hmid Hhigh Hmidlow Hmidhigh Hdplow Hdphigh
         Hlow_bound Hmid_bound Hhigh_bound Hmidlow_bound Hmidhigh_bound
         Hout_bound Hdp_bound Hdplow_bound Hdphigh_bound Hout_val Hsubmul
         Hdval Hd1 Hd0 Hn1_nonneg Hretval_nonneg Hn0_ge_retval
         Hwindow_eq Hpair_lt Hrem.
  set (B := UINT_MOD).
  assert (HBpos : 0 < B) by (subst B; unfold UINT_MOD; lia).
  assert (Hold_prefix :
    list_to_Z B (sublist 0 (dn0 + i) l_cur) =
    list_to_Z B l_low + list_to_Z B l_mid * B ^ i).
  {
    subst B.
    rewrite (sublist_split 0 (dn0 + i) i l_cur)
      by (split; try lia; rewrite Hcur_len; lia).
    rewrite <- Hlow.
    replace (sublist i (dn0 + i) l_cur) with l_mid
      by (rewrite Hmid; f_equal; lia).
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hlow_len.
    reflexivity.
  }
  assert (Hmid_split : l_mid = l_mid_low ++ l_mid_high).
  {
    rewrite Hmidlow, Hmidhigh.
    rewrite <- (sublist_split 0 dn0 (dn0 - 2) l_mid) by lia.
    rewrite sublist_self by (symmetry; exact Hmid_len).
    reflexivity.
  }
  assert (Hdp_split : l_dp = l_dp_low ++ l_dp_high).
  {
    rewrite Hdplow, Hdphigh.
    rewrite <- (sublist_split 0 dn0 (dn0 - 2) l_dp) by lia.
    rewrite sublist_self by (symmetry; exact Hdp_len).
    reflexivity.
  }
  assert (Hmid_high_val :
    list_to_Z B l_mid_high =
      Znth (dn0 - 2) l_mid 0 + Znth (dn0 - 1) l_mid 0 * B).
  {
    subst B.
    rewrite Hmidhigh.
    replace (sublist (dn0 - 2) dn0 l_mid)
      with (sublist (dn0 - 2) (dn0 - 1) l_mid ++
            sublist (dn0 - 1) dn0 l_mid).
    - replace (sublist (dn0 - 2) (dn0 - 1) l_mid)
        with (sublist (dn0 - 2) ((dn0 - 2) + 1) l_mid) by (f_equal; lia).
      replace (sublist (dn0 - 1) dn0 l_mid)
        with (sublist (dn0 - 1) ((dn0 - 1) + 1) l_mid) by (f_equal; lia).
      rewrite !(sublist_single 0) by (rewrite Hmid_len; lia).
      change (((Znth (dn0 - 2) l_mid 0 :: nil) ++
               (Znth (dn0 - 1) l_mid 0 :: nil))%list)
        with (Znth (dn0 - 2) l_mid 0 :: Znth (dn0 - 1) l_mid 0 :: nil).
      rewrite list_to_Z_cons, list_to_Z_cons, list_to_Z_nil.
      ring.
    - rewrite (sublist_split (dn0 - 2) dn0 (dn0 - 1) l_mid) by lia.
      reflexivity.
  }
  assert (Hdp_high_val :
    list_to_Z B l_dp_high = d0 + d1 * B).
  {
    subst B.
    rewrite Hdphigh.
    replace (sublist (dn0 - 2) dn0 l_dp)
      with (sublist (dn0 - 2) (dn0 - 1) l_dp ++
            sublist (dn0 - 1) dn0 l_dp).
    - replace (sublist (dn0 - 2) (dn0 - 1) l_dp)
        with (sublist (dn0 - 2) ((dn0 - 2) + 1) l_dp) by (f_equal; lia).
      replace (sublist (dn0 - 1) dn0 l_dp)
        with (sublist (dn0 - 1) ((dn0 - 1) + 1) l_dp) by (f_equal; lia).
      rewrite !(sublist_single 0) by (rewrite Hdp_len; lia).
      change (((Znth (dn0 - 2) l_dp 0 :: nil) ++
               (Znth (dn0 - 1) l_dp 0 :: nil))%list)
        with (Znth (dn0 - 2) l_dp 0 :: Znth (dn0 - 1) l_dp 0 :: nil).
      rewrite list_to_Z_cons, list_to_Z_cons, list_to_Z_nil.
      rewrite <- Hd1, <- Hd0.
      ring.
    - rewrite (sublist_split (dn0 - 2) dn0 (dn0 - 1) l_dp) by lia.
      reflexivity.
  }
  assert (Hmid_decomp :
    list_to_Z B l_mid =
      list_to_Z B l_mid_low + list_to_Z B l_mid_high * B ^ (dn0 - 2)).
  {
    subst B.
    rewrite Hmid_split.
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hmidlow_len.
    reflexivity.
  }
  assert (Hdp_decomp :
    dval =
      list_to_Z B l_dp_low + list_to_Z B l_dp_high * B ^ (dn0 - 2)).
  {
    subst B.
    rewrite <- Hdval.
    rewrite Hdp_split.
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hdplow_len.
    reflexivity.
  }
  set (l_repl := replace_Znth 0 (n0 - retval) l_mid_high).
  assert (Hlrepl_len : Zlength l_repl = 2).
  { subst l_repl. rewrite Zlength_replace_Znth. exact Hmidhigh_len. }
  assert (Hlrepl_head : Znth 0 l_repl 0 = n0 - retval).
  {
    subst l_repl.
    rewrite Znth_replace_Znth_Same by (rewrite Hmidhigh_len; lia).
    reflexivity.
  }
  assert (Hnew_prefix :
    sublist 0 (dn0 + (i - 1)) (l_low ++ l_out ++ l_repl ++ l_high) =
      l_low ++ l_out ++ sublist 0 1 l_repl).
  {
    replace (dn0 + (i - 1)) with
      (Zlength l_low + Zlength l_out + 1)
      by (rewrite Hlow_len, Hout_len; lia).
    apply sublist_app_prefix_two_plus_one.
    rewrite Hlrepl_len; lia.
  }
  assert (Hnew_value :
    n1 * B ^ (dn0 + (i - 1)) +
    list_to_Z B (sublist 0 (dn0 + (i - 1))
      (l_low ++ l_out ++ l_repl ++ l_high)) =
    list_to_Z B l_low +
      (list_to_Z B l_out + (n0 - retval) * B ^ (dn0 - 2) +
       n1 * B ^ (dn0 - 1)) * B ^ i).
  {
    rewrite Hnew_prefix.
    rewrite list_to_Z_app by exact HBpos.
    rewrite Hlow_len.
    rewrite list_to_Z_app by exact HBpos.
    rewrite Hout_len.
    replace (sublist 0 1 l_repl) with (sublist 0 (0 + 1) l_repl) by (f_equal; lia).
    rewrite (sublist_single 0) by (rewrite Hlrepl_len; lia).
    rewrite list_to_Z_cons, list_to_Z_nil, Hlrepl_head.
    replace (dn0 + (i - 1)) with ((dn0 - 1) + i) by lia.
    rewrite Z.pow_add_r by lia.
    ring.
  }
  assert (Hpow_dni : B ^ (dn0 + i) = B ^ dn0 * B ^ i).
  { rewrite Z.pow_add_r by lia; reflexivity. }
  assert (Hpow_dn : B ^ dn0 = B ^ 2 * B ^ (dn0 - 2)).
  {
    replace dn0 with (2 + (dn0 - 2)) by lia.
    rewrite Z.pow_add_r by lia.
    replace (2 + (dn0 - 2) - 2) with (dn0 - 2) by lia.
    reflexivity.
  }
  assert (Hold_value :
    remv_2 =
    list_to_Z B l_low +
      (list_to_Z B l_mid + n1_in * B ^ dn0) * B ^ i).
  {
    rewrite Hrem.
    fold B.
    rewrite Hold_prefix, Hpow_dni.
    ring.
  }
  assert (Hwindow_relation :
    list_to_Z B l_out + (n0 - retval) * B ^ (dn0 - 2) +
      n1 * B ^ (dn0 - 1) =
    list_to_Z B l_mid + n1_in * B ^ dn0 - q * dval).
  {
    assert (HsubmulB :
      list_to_Z B l_mid_low =
        list_to_Z B l_out - retval * B ^ (dn0 - 2) +
        list_to_Z B l_dp_low * q).
    {
      subst B.
      rewrite Hout_val.
      lia.
    }
    assert (HwindowB :
      n1_in * B ^ 2 +
        (Znth (dn0 - 2) l_mid 0 + Znth (dn0 - 1) l_mid 0 * B) =
      q * (d1 * B + d0) + n1 * B + n0).
    {
      subst B.
      replace (n1_in * UINT_MOD ^ 2 +
        (Znth (dn0 - 2) l_mid 0 + Znth (dn0 - 1) l_mid 0 * UINT_MOD))
        with (n1_in * UINT_MOD ^ 2 +
          Znth (dn0 - 1) l_mid 0 * UINT_MOD + Znth (dn0 - 2) l_mid 0)
        by ring.
      rewrite Hwindow_eq.
      ring.
    }
    assert (Hpow_dn1 : B ^ (dn0 - 1) = B * B ^ (dn0 - 2)).
    {
      replace (dn0 - 1) with (1 + (dn0 - 2)) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      ring.
    }
    rewrite Hmid_decomp, Hdp_decomp, Hmid_high_val, Hdp_high_val.
    rewrite Hpow_dn, Hpow_dn1.
    nia.
  }
  assert (Hrem_eq :
    n1 * B ^ (dn0 + (i - 1)) +
    list_to_Z B (sublist 0 (dn0 + (i - 1))
      (l_low ++ l_out ++ l_repl ++ l_high)) =
    remv_2 - q * dval * B ^ i).
  {
    rewrite Hnew_value, Hold_value, Hwindow_relation.
    ring.
  }
  assert (Hout_bound_val :
    0 <= val_out < B ^ (dn0 - 2)).
  {
    subst B.
    rewrite <- Hout_val.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out Hout_bound) as Hbound.
    rewrite Hout_len in Hbound.
    exact Hbound.
  }
  assert (Hdplow_nonneg : 0 <= list_to_Z B l_dp_low).
  {
    subst B.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_dp_low Hdplow_bound) as Hbound.
    lia.
  }
  assert (Hpow_dn2_pos : 0 < B ^ (dn0 - 2)).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hout_nonnegB : 0 <= list_to_Z B l_out).
  {
    subst B.
    rewrite Hout_val.
    exact (proj1 Hout_bound_val).
  }
  assert (Hwindow_nonneg :
    0 <= list_to_Z B l_out + (n0 - retval) * B ^ (dn0 - 2) +
      n1 * B ^ (dn0 - 1)).
  {
    apply Z.add_nonneg_nonneg.
    - apply Z.add_nonneg_nonneg.
      + exact Hout_nonnegB.
      + apply Z.mul_nonneg_nonneg; [lia | lia].
    - apply Z.mul_nonneg_nonneg.
      + exact Hn1_nonneg.
      + apply Z.pow_nonneg; lia.
  }
  assert (Hwindow_new_lt :
    list_to_Z B l_out + (n0 - retval) * B ^ (dn0 - 2) +
      n1 * B ^ (dn0 - 1) < dval).
  {
    assert (Hpow_dn1 : B ^ (dn0 - 1) = B * B ^ (dn0 - 2)).
    {
      replace (dn0 - 1) with (1 + (dn0 - 2)) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      ring.
    }
    rewrite Hpow_dn1.
    assert (Htop_le : n1 * B + n0 - retval <= d1 * B + d0 - 1).
    { clear -Hpair_lt Hretval_nonneg. fold B in Hpair_lt. lia. }
    assert (Hout_leB : list_to_Z B l_out <= B ^ (dn0 - 2) - 1).
    {
      subst B.
      rewrite Hout_val.
      lia.
    }
    rewrite Hdp_decomp, Hdp_high_val.
    replace (list_to_Z B l_out + (n0 - retval) * B ^ (dn0 - 2) +
             n1 * (B * B ^ (dn0 - 2)))
      with (list_to_Z B l_out + (n1 * B + n0 - retval) * B ^ (dn0 - 2))
      by ring.
    replace (d0 + d1 * B) with (d1 * B + d0) by ring.
    assert (Hcoef :
      (n1 * B + n0 - retval) * B ^ (dn0 - 2) <=
      (d1 * B + d0 - 1) * B ^ (dn0 - 2)).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hleft_le :
      list_to_Z B l_out + (n1 * B + n0 - retval) * B ^ (dn0 - 2) <=
      (d1 * B + d0) * B ^ (dn0 - 2) - 1).
    {
      replace ((d1 * B + d0) * B ^ (dn0 - 2) - 1)
        with ((B ^ (dn0 - 2) - 1) +
              (d1 * B + d0 - 1) * B ^ (dn0 - 2)) by ring.
      apply Z.add_le_mono; assumption.
    }
    assert (Hright_ge :
      (d1 * B + d0) * B ^ (dn0 - 2) <=
      list_to_Z B l_dp_low + (d1 * B + d0) * B ^ (dn0 - 2)).
    { lia. }
    lia.
  }
  subst l_repl.
  assert (Hrem_value :
    remv_2 - q * dval * B ^ i =
    list_to_Z B l_low +
      (list_to_Z B l_out + (n0 - retval) * B ^ (dn0 - 2) +
       n1 * B ^ (dn0 - 1)) * B ^ i).
  {
    rewrite Hold_value.
    replace (list_to_Z B l_low +
             (list_to_Z B l_mid + n1_in * B ^ dn0) * B ^ i -
             q * dval * B ^ i)
      with (list_to_Z B l_low +
            (list_to_Z B l_mid + n1_in * B ^ dn0 - q * dval) * B ^ i)
      by ring.
    rewrite <- Hwindow_relation.
    reflexivity.
  }
  split.
  - rewrite Hrem_eq. reflexivity.
  - split.
    + rewrite Hrem_eq, Hrem_value.
      apply Z.add_nonneg_nonneg.
      * pose proof (list_to_Z_bound B HBpos l_low Hlow_bound) as Hlow_bound_val.
        lia.
      * apply Z.mul_nonneg_nonneg; [exact Hwindow_nonneg | apply Z.pow_nonneg; lia].
    + rewrite Hrem_eq, Hrem_value.
      replace (list_to_Z B l_low +
               (list_to_Z B l_out + (n0 - retval) * B ^ (dn0 - 2) +
                n1 * B ^ (dn0 - 1)) * B ^ i)
        with (list_to_Z B l_low +
              (list_to_Z B l_out + (n0 - retval) * B ^ (dn0 - 2) +
               n1 * B ^ (dn0 - 1)) * B ^ i) by ring.
      assert (Hlow_bound_val :
        0 <= list_to_Z B l_low < B ^ i).
      {
        pose proof (list_to_Z_bound B HBpos l_low Hlow_bound) as Hbound.
        rewrite Hlow_len in Hbound.
        exact Hbound.
      }
      assert (Hpow_i_pos : 0 < B ^ i).
      { apply Z.pow_pos_nonneg; lia. }
      nia.
Qed.

Lemma list_within_bound_replace_Znth : forall Base (l: list Z) i v,
  0 <= i < Zlength l ->
  0 <= v < Base ->
  list_within_bound Base l ->
  list_within_bound Base (replace_Znth i v l).
Proof.
  intros Base l.
  induction l as [|a tl IH]; intros i v Hi Hv Hbound.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    simpl in Hbound.
    destruct Hbound as [Ha Htl].
    destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
    + subst i.
      unfold replace_Znth. simpl.
      simpl. split; [lia | exact Htl].
    + rewrite replace_Znth_cons by lia.
      simpl. split; [exact Ha | apply IH; try lia; assumption].
Qed.

Lemma store_preinv_divisor_dn1_project : forall dp inv d,
  store_preinv_divisor dp inv 1 d |--
  store_div_inverse inv 1 d ** mpd_store_Z_compact UINT_MOD dp d 1.
Proof.
  intros dp inv d.
  unfold store_preinv_divisor, store_div_inverse.
  Intros l_dp shift d1 d0 di.
  assert (Hcompact: is_compact_Z UINT_MOD d 1).
  {
    apply (is_compact_Z_from_bounds UINT_MOD UINT_MOD_pos); [lia |].
    right.
    unfold gmp_div_inverse_valid in H.
    repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
    unfold preinv_dp_value in H2; simpl in H2.
    split; [lia |].
    split.
    - rewrite <- H2.
      pose proof (list_to_Z_pos UINT_MOD UINT_MOD_pos l_dp H1).
      lia.
    - change (UINT_MOD ^ 1) with UINT_MOD in *.
      assert (0 < 2 ^ shift) by (apply Z.pow_pos_nonneg; lia).
      assert (1 <= 2 ^ shift) by lia.
      unfold UINT_MOD in *. nia.
  }
  sep_apply (UIntArray_full_to_mpd_store_Z_compact
    dp 1 l_dp d H0 H2 H1 Hcompact).
  Exists shift d1 d0 di.
  split_pure_spatial.
  - cancel (div_inverse_store inv 1 shift d1 d0 di).
    cancel (mpd_store_Z_compact UINT_MOD dp d 1).
  - dump_pre_spatial. exact H.
Qed.

Lemma store_preinv_divisor_dn2_project : forall dp inv d,
  store_preinv_divisor dp inv 2 d |--
  store_div_inverse inv 2 d ** mpd_store_Z_compact UINT_MOD dp d 2.
Proof.
  intros dp inv d.
  unfold store_preinv_divisor, store_div_inverse.
  Intros l_dp shift d1 d0 di.
  assert (Hcompact: is_compact_Z UINT_MOD d 2).
  {
    apply (is_compact_Z_from_bounds UINT_MOD UINT_MOD_pos); [lia |].
    right.
    unfold gmp_div_inverse_valid in H.
    repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
    unfold preinv_dp_value in H2; simpl in H2.
    split; [lia |].
    split.
    - destruct H9 as [[Hbad _] | [Hdn Hnorm]]; [lia |].
      replace (2 - 2) with 0 in Hnorm by lia.
      rewrite Z.pow_0_r in Hnorm.
      rewrite Z.div_1_r in Hnorm.
      assert (0 < 2 ^ shift) by (apply Z.pow_pos_nonneg; lia).
      assert (2 ^ shift <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
      change (UINT_MOD ^ (2 - 1)) with UINT_MOD.
      assert (Hdshift_ge: (UINT_MOD / 2) * UINT_MOD <= d * 2 ^ shift).
      { rewrite <- Hnorm. unfold UINT_MOD in *. nia. }
      assert (Hdshift_le: d * 2 ^ shift <= d * 2 ^ 31).
      { apply Z.mul_le_mono_nonneg_l; lia. }
      replace (UINT_MOD / 2) with (2 ^ 31) in Hdshift_ge by (unfold UINT_MOD; reflexivity).
      change (2 ^ 31) with 2147483648 in *.
      unfold UINT_MOD in *. lia.
    - change (UINT_MOD ^ 2) with (UINT_MOD * UINT_MOD) in *.
      assert (0 < 2 ^ shift) by (apply Z.pow_pos_nonneg; lia).
      assert (1 <= 2 ^ shift) by lia.
      unfold UINT_MOD in *. nia.
  }
  sep_apply (UIntArray_full_to_mpd_store_Z_compact
    dp 2 l_dp d H0 H2 H1 Hcompact).
  Exists shift d1 d0 di.
  split_pure_spatial.
  - cancel (div_inverse_store inv 2 shift d1 d0 di).
    cancel (mpd_store_Z_compact UINT_MOD dp d 2).
  - dump_pre_spatial. exact H.
Qed.

Lemma store_preinv_divisor_dn1_intro : forall dp inv d,
  store_div_inverse inv 1 d ** mpd_store_Z_compact UINT_MOD dp d 1 |--
  store_preinv_divisor dp inv 1 d.
Proof.
  intros dp inv d.
  unfold store_preinv_divisor, store_div_inverse, mpd_store_Z_compact, mpd_store_list.
  Intros shift d1 d0 di data.
  Exists data shift d1 d0 di.
  replace (Zlength data) with 1 by lia.
  split_pure_spatial.
  - cancel (UIntArray.full dp 1 data).
    cancel (div_inverse_store inv 1 shift d1 d0 di).
  - split_pures; dump_pre_spatial.
    + exact H.
    + reflexivity.
    + exact (proj2 (proj2 H0)).
    + unfold preinv_dp_value; simpl. exact (proj1 H0).
Qed.

Lemma store_preinv_divisor_dn2_intro : forall dp inv d,
  store_div_inverse inv 2 d ** mpd_store_Z_compact UINT_MOD dp d 2 |--
  store_preinv_divisor dp inv 2 d.
Proof.
  intros dp inv d.
  unfold store_preinv_divisor, store_div_inverse, mpd_store_Z_compact, mpd_store_list.
  Intros shift d1 d0 di data.
  Exists data shift d1 d0 di.
  replace (Zlength data) with 2 by lia.
  split_pure_spatial.
  - cancel (UIntArray.full dp 2 data).
    cancel (div_inverse_store inv 2 shift d1 d0 di).
  - split_pures; dump_pre_spatial.
    + exact H.
    + reflexivity.
    + exact (proj2 (proj2 H0)).
    + unfold preinv_dp_value; simpl. exact (proj1 H0).
Qed.

Lemma store_preinv_divisor_gt2_project : forall dp inv dn d,
  dn > 2 ->
  store_preinv_divisor dp inv dn d |--
  EX di, EX l_dp, EX shift,
    “ 0 < d ” && “ 0 <= shift ” && “ shift < 32 ” &&
    “ Zlength l_dp = dn ” && “ list_within_bound UINT_MOD l_dp ” &&
    “ list_to_Z UINT_MOD l_dp = d * 2 ^ shift ” &&
    “ UINT_MOD / 2 <= Znth (dn - 1) l_dp 0 ” &&
    “ Znth (dn - 1) l_dp 0 <= UINT_MAX ” &&
    “ 0 <= Znth (dn - 2) l_dp 0 ” &&
    “ Znth (dn - 2) l_dp 0 <= UINT_MAX ” &&
    “ 0 <= di ” && “ di <= UINT_MAX ” &&
    “ (di + UINT_MOD) *
        (UINT_MOD * Znth (dn - 1) l_dp 0 + Znth (dn - 2) l_dp 0) <=
      UINT_MOD ^ 3 - 1 ” &&
    “ UINT_MOD ^ 3 - 1 <
      (di + UINT_MOD + 1) *
        (UINT_MOD * Znth (dn - 1) l_dp 0 + Znth (dn - 2) l_dp 0) ” &&
    UIntArray.full dp dn l_dp **
    div_inverse_fields
      inv shift (Znth (dn - 1) l_dp 0) (Znth (dn - 2) l_dp 0) di.
Proof.
  intros dp inv dn d Hdn.
  unfold store_preinv_divisor.
  Intros l_dp shift d1 d0 di.
  unfold gmp_div_inverse_valid in H.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  unfold preinv_dp_value in H2.
  destruct (Z.gtb_spec dn 2) as [Hgtb | Hle]; [| lia].
  simpl in H2.
  assert (Hbranch: d1 * UINT_MOD + d0 = d * 2 ^ shift / UINT_MOD ^ (dn - 2)).
  {
    destruct H9 as [[Hbad _] | [Hgt Hnorm]]; [lia | exact Hnorm].
  }
  pose proof (list_to_Z_high2_quot_uint_for_div l_dp dn H0 ltac:(lia) H1) as Hhigh.
  rewrite H2 in Hhigh.
  rewrite <- Hbranch in Hhigh.
  assert (Hz2: 0 <= Znth (dn - 2) l_dp 0 < UINT_MOD).
  { apply list_within_bound_Znth_bound; [rewrite H0; lia | exact H1]. }
  assert (Hz1: 0 <= Znth (dn - 1) l_dp 0 < UINT_MOD).
  { apply list_within_bound_Znth_bound; [rewrite H0; lia | exact H1]. }
  assert (Hsum:
    d0 + d1 * UINT_MOD =
    Znth (dn - 2) l_dp 0 + Znth (dn - 1) l_dp 0 * UINT_MOD).
  { rewrite <- Hhigh. ring. }
  assert (Hlist_eq:
    (d0 :: d1 :: nil)%list =
    (Znth (dn - 2) l_dp 0 :: Znth (dn - 1) l_dp 0 :: nil)%list).
  {
    apply (list_to_Z_reverse_same_length_injection UINT_MOD UINT_MOD_pos).
    - rewrite !list_to_Z_cons, !list_to_Z_nil.
      replace (d0 + UINT_MOD * (d1 + UINT_MOD * 0)) with (d0 + d1 * UINT_MOD) by ring.
      replace (Znth (dn - 2) l_dp 0 +
                 UINT_MOD * (Znth (dn - 1) l_dp 0 + UINT_MOD * 0))
        with (Znth (dn - 2) l_dp 0 +
                Znth (dn - 1) l_dp 0 * UINT_MOD) by ring.
      rewrite Hsum.
      ring.
    - simpl. repeat split; try lia.
      + unfold UINT_MOD in *; lia.
      + unfold UINT_MOD in *; lia.
    - simpl. repeat split; try lia.
    - rewrite !Zlength_cons, !Zlength_nil.
      reflexivity.
  }
  injection Hlist_eq as Hd0 Hd1.
  rewrite Hd0, Hd1 in *.
  Exists di l_dp shift.
  assert (Hden:
    div_inverse_den dn (Znth (dn - 1) l_dp 0) (Znth (dn - 2) l_dp 0) =
    UINT_MOD * Znth (dn - 1) l_dp 0 + Znth (dn - 2) l_dp 0).
  { unfold div_inverse_den. destruct (Z.eq_dec dn 1); [lia | reflexivity]. }
  rewrite Hden in H11, H12.
  repeat split_pure_spatial.
  - unfold div_inverse_store, div_inverse_fields.
    destruct (Z.eq_dec dn 1); [lia |].
    normalize; try cancel; try dump_pre_spatial; try lia.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity.
Qed.

Lemma Z_le_div_mul_pos : forall a b q,
  0 < b -> q <= a / b -> q * b <= a.
Proof.
  intros a b q Hb Hq.
  pose proof (Z.div_mod a b ltac:(lia)) as Hdivmod.
  pose proof (Z.mod_pos_bound a b Hb) as Hmod.
  rewrite Hdivmod.
  replace (b * (a / b) + a mod b) with ((a / b) * b + a mod b) by ring.
  assert (Hqb : q * b <= (a / b) * b).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  lia.
Qed.

Lemma gmp_div_inverse_valid_shift0_lower_bound : forall dn d d1 d0 di,
  dn > 2 ->
  gmp_div_inverse_valid dn d 0 d1 d0 di ->
  (UINT_MOD / 2) * UINT_MOD ^ (dn - 1) <= d.
Proof.
  intros dn d d1 d0 di Hdn Hvalid.
  unfold gmp_div_inverse_valid in Hvalid.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  destruct H6 as [[Hbad _] | [Hdn1 Hnorm]]; [lia |].
  rewrite Z.pow_0_r in Hnorm.
  replace (d * 1) with d in Hnorm by ring.
  assert (Hq : (UINT_MOD / 2) * UINT_MOD <= d / UINT_MOD ^ (dn - 2)).
  { rewrite <- Hnorm. unfold UINT_MOD in *; nia. }
  pose proof (Z.pow_pos_nonneg UINT_MOD (dn - 2)
    ltac:(unfold UINT_MOD; lia) ltac:(lia)) as Hpowpos.
  pose proof (Z_le_div_mul_pos d (UINT_MOD ^ (dn - 2))
    ((UINT_MOD / 2) * UINT_MOD) Hpowpos Hq) as Hlower.
  replace (UINT_MOD ^ (dn - 1)) with (UINT_MOD * UINT_MOD ^ (dn - 2)).
  - replace (UINT_MOD / 2 * (UINT_MOD * UINT_MOD ^ (dn - 2)))
      with (UINT_MOD / 2 * UINT_MOD * UINT_MOD ^ (dn - 2)) by ring.
    exact Hlower.
  - replace UINT_MOD with (UINT_MOD ^ 1) at 1 by (simpl; lia).
    rewrite <- Z.pow_add_r by lia.
    replace (1 + (dn - 2)) with (dn - 1) by lia.
    reflexivity.
Qed.

Lemma gmp_div_inverse_valid_shift0_unique :
  forall dn d shift d1 d0 di d1z d0z diz,
    dn > 2 ->
    gmp_div_inverse_valid dn d 0 d1z d0z diz ->
    gmp_div_inverse_valid dn d shift d1 d0 di ->
    shift = 0.
Proof.
  intros dn d shift d1 d0 di d1z d0z diz Hdn Hz Hvalid.
  pose proof (gmp_div_inverse_valid_shift0_lower_bound dn d d1z d0z diz Hdn Hz)
    as Hlower.
  unfold gmp_div_inverse_valid in Hvalid.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  assert (Hshift_cases : shift = 0 \/ shift >= 1) by lia.
  destruct Hshift_cases as [Hshift0 | Hpos]; [exact Hshift0 |].
  assert (Hpow_ge2 : 2 <= 2 ^ shift).
  {
    replace 2 with (2 ^ 1) by reflexivity.
    apply Z.pow_le_mono_r; lia.
  }
  assert (Hnonneg_lb : 0 <= (UINT_MOD / 2) * UINT_MOD ^ (dn - 1)).
  {
    apply Z.mul_nonneg_nonneg.
    - change (0 <= 4294967296 / 2). vm_compute. discriminate.
    - apply Z.pow_nonneg. change (0 <= 4294967296). vm_compute. discriminate.
  }
  assert (Hbig : UINT_MOD ^ dn <= d * 2 ^ shift).
  {
    assert (Hmul :
      (UINT_MOD / 2) * UINT_MOD ^ (dn - 1) * 2 <= d * 2 ^ shift).
    {
      apply Z.mul_le_mono_nonneg.
      - exact Hnonneg_lb.
      - exact Hlower.
      - lia.
      - exact Hpow_ge2.
    }
    assert (Heq : (UINT_MOD / 2) * UINT_MOD ^ (dn - 1) * 2 = UINT_MOD ^ dn).
    {
      replace ((UINT_MOD / 2) * UINT_MOD ^ (dn - 1) * 2)
        with (UINT_MOD * UINT_MOD ^ (dn - 1)).
      - replace UINT_MOD with (UINT_MOD ^ 1) at 1 by (simpl; lia).
        rewrite <- Z.pow_add_r by lia.
        replace (1 + (dn - 1)) with dn by lia.
        reflexivity.
      - unfold UINT_MOD.
        change (4294967296 / 2) with 2147483648.
        ring.
    }
    rewrite Heq in Hmul. exact Hmul.
  }
  lia.
Qed.

Lemma store_preinv_divisor_shift0_valid_project :
  forall dp inv dn d d1z d0z diz,
    gmp_div_inverse_valid dn d 0 d1z d0z diz ->
    store_preinv_divisor dp inv dn d |--
    store_div_inverse inv dn d ** mpd_store_Z_compact UINT_MOD dp d dn.
Proof.
  intros dp inv dn d d1z d0z diz Hz.
  unfold gmp_div_inverse_valid in Hz.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  assert (Hdn_cases : dn = 1 \/ dn = 2 \/ dn > 2) by lia.
  destruct Hdn_cases as [Hdn | [Hdn | Hdn]].
  - subst dn.
    apply store_preinv_divisor_dn1_project.
  - subst dn.
    apply store_preinv_divisor_dn2_project.
  - sep_apply (store_preinv_divisor_gt2_project dp inv dn d Hdn).
    Intros di l_dp shift.
    assert (Hvalid_store :
      gmp_div_inverse_valid dn d shift
        (Znth (dn - 1) l_dp 0) (Znth (dn - 2) l_dp 0) di).
    {
      unfold gmp_div_inverse_valid, div_inverse_den.
      repeat split; try (unfold UINT_MOD in *; lia).
      + pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_dp H19) as Hbound.
        rewrite H18 in Hbound.
        rewrite H20 in Hbound.
        exact (proj2 Hbound).
      + right.
        split; [lia |].
        pose proof (list_to_Z_high2_quot_uint_for_div l_dp dn H18 ltac:(lia) H19)
          as Hhigh.
        rewrite H20 in Hhigh.
        rewrite Hhigh.
        ring.
      + destruct (Z.eq_dec dn 1); [lia |].
        assumption.
      + destruct (Z.eq_dec dn 1); [lia |].
        assumption.
    }
    assert (Hvalid_zero :
      gmp_div_inverse_valid dn d 0 d1z d0z diz).
    {
      unfold gmp_div_inverse_valid.
      repeat split; try assumption.
    }
    pose proof (gmp_div_inverse_valid_shift0_unique
      dn d shift (Znth (dn - 1) l_dp 0) (Znth (dn - 2) l_dp 0) di
      d1z d0z diz Hdn Hvalid_zero Hvalid_store) as Hshift0.
    subst shift.
    rewrite Z.pow_0_r in H20.
    replace (d * 1) with d in H20 by ring.
    assert (Hcompact : is_compact_Z UINT_MOD d dn).
    {
      apply (is_compact_Z_from_full_last l_dp dn d); try lia; try assumption.
      rewrite (list_last_eq_Znth_last l_dp dn H18 ltac:(lia)).
      unfold UINT_MOD in H21.
      change (4294967296 / 2) with 2147483648 in H21.
      lia.
    }
    sep_apply (UIntArray_full_to_mpd_store_Z_compact
      dp dn l_dp d H18 H20 H19 Hcompact).
    unfold store_div_inverse.
    Exists 0 (Znth (dn - 1) l_dp 0) (Znth (dn - 2) l_dp 0) di.
    split_pure_spatial.
    + unfold div_inverse_store, div_inverse_fields.
      destruct (Z.eq_dec dn 1); [lia |].
      cancel.
    + dump_pre_spatial. exact Hvalid_store.
Qed.

Lemma store_preinv_divisor_gt2_intro : forall dp inv dn d l_dp shift d1 d0 di,
  dn > 2 ->
  dn <= INT_MAX ->
  0 < d ->
  0 <= shift < 32 ->
  Zlength l_dp = dn ->
  list_within_bound UINT_MOD l_dp ->
  list_to_Z UINT_MOD l_dp = d * 2 ^ shift ->
  d1 = Znth (dn - 1) l_dp 0 ->
  d0 = Znth (dn - 2) l_dp 0 ->
  UINT_MOD / 2 <= d1 ->
  d1 <= UINT_MAX ->
  0 <= d0 ->
  d0 <= UINT_MAX ->
  0 <= di ->
  di <= UINT_MAX ->
  (di + UINT_MOD) * (UINT_MOD * d1 + d0) <= UINT_MOD ^ 3 - 1 ->
  UINT_MOD ^ 3 - 1 < (di + UINT_MOD + 1) * (UINT_MOD * d1 + d0) ->
  UIntArray.full dp dn l_dp ** div_inverse_fields inv shift d1 d0 di |--
  store_preinv_divisor dp inv dn d.
Proof.
  intros dp inv dn d l_dp shift d1 d0 di Hdn Hint Hd Hshift Hlen Hbound Hval
    Hd1 Hd0 Hd1norm Hd1range Hd0nonneg Hd0range Hdinonneg Hdirange Hdi1 Hdi2.
  unfold store_preinv_divisor.
  Exists l_dp shift d1 d0 di.
  assert (Hvalid: gmp_div_inverse_valid dn d shift d1 d0 di).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    repeat split; try (unfold UINT_MOD in *; lia).
    - pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_dp Hbound) as Hzb.
      rewrite Hlen in Hzb.
      rewrite Hval in Hzb.
      exact (proj2 Hzb).
    - right.
      split; [lia |].
      pose proof (list_to_Z_high2_quot_uint_for_div l_dp dn Hlen ltac:(lia) Hbound) as Hhigh.
      rewrite Hval in Hhigh.
      rewrite Hd1, Hd0.
      rewrite Hhigh.
      ring.
    - destruct (Z.eq_dec dn 1); [lia |].
      exact Hdi1.
    - destruct (Z.eq_dec dn 1); [lia |].
      exact Hdi2.
  }
  unfold preinv_dp_value.
  destruct (Z.gtb_spec dn 2); [| lia].
  split_pure_spatial.
  - unfold div_inverse_store, div_inverse_fields.
    destruct (Z.eq_dec dn 1); [lia |].
    cancel.
  - split_pures; dump_pre_spatial.
    + exact Hvalid.
    + exact Hlen.
    + exact Hbound.
    + exact Hval.
Qed.

Lemma UIntArray_seg_list_within_bound:
  forall x lo hi (l: list Z),
    UIntArray.seg x lo hi l |-- “ list_within_bound UINT_MOD l ”.
Proof.
  intros x lo hi l.
  unfold UIntArray.seg.
  revert lo.
  induction l; intros lo; simpl.
  - normalize; try cancel; try dump_pre_spatial; try lia.
  - sep_apply (store_uint_range (x + lo * sizeof(UINT)) a).
    Intros.
    sep_apply (IHl (lo + 1)).
    Intros.
    dump_pre_spatial.
    unfold UINT_MOD in *.
    replace Int.max_unsigned with 4294967295 in * by reflexivity.
    split; [lia | assumption].
Qed.

Lemma UIntArray_seg_list_within_bound_preserve:
  forall x lo hi (l: list Z),
    UIntArray.seg x lo hi l |--
      “ list_within_bound UINT_MOD l ” && UIntArray.seg x lo hi l.
Proof.
  intros.
  apply logic_equiv_coq_prop_andp1.
  apply UIntArray_seg_list_within_bound.
Qed.

Lemma UIntArray_full_list_within_bound_preserve:
  forall x n (l: list Z),
    UIntArray.full x n l |--
      “ list_within_bound UINT_MOD l ” && UIntArray.full x n l.
Proof.
  intros x n l.
  unfold UIntArray.full.
  unfold store_array.
  apply UIntArray_seg_list_within_bound_preserve.
Qed.

Lemma dup_undef_store_uint:
  forall x,
    x # UInt |->_ ** x # UInt |->_ |-- “ False ”.
Proof.
  intros x.
  unfold undef_store_uint.
  Intros.
  sep_apply_l_atomic (dup_store_4bytes_noninit x).
  cancel.
Qed.

Lemma UIntArray_undef_full_full_base_neq:
  forall p q n l,
    n > 0 ->
    Zlength l = n ->
    UIntArray.undef_full p n ** UIntArray.full q n l |-- “ p <> q ”.
Proof.
  intros p q n l Hn Hlen.
  destruct l as [| a tl].
  - rewrite Zlength_nil in Hlen. lia.
  - replace n with (n - 1 + 1) at 1 by lia.
    rewrite (UIntArray.undef_full_unfold p (n - 1) (@nil Z)) by lia.
    rewrite (UIntArray.full_unfold q n tl a).
    destruct (Z.eq_dec p q) as [Heq | Hne].
    + subst q.
      sep_apply_l_atomic (store_uint_undef_store_uint (p + 0 * sizeof(UINT)) a).
      sep_apply_l_atomic (dup_undef_store_uint (p + 0 * sizeof(UINT))).
      Intros_p Hfalse.
      contradiction.
    + dump_pre_spatial.
      exact Hne.
Qed.

Lemma sublist_replace_two_head:
  forall (l: list Z) a b,
    2 <= Zlength l ->
    sublist 0 2 (replace_Znth 0 a (replace_Znth 1 b l)) = a :: b :: nil.
Proof.
  intros l a b Hlen.
  assert (Hsub_len:
    Zlength (sublist 0 2 (replace_Znth 0 a (replace_Znth 1 b l))) = 2).
  {
    rewrite Zlength_sublist by (rewrite !Zlength_replace_Znth; lia).
    lia.
  }
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite Hsub_len.
    rewrite !Zlength_cons, Zlength_nil; lia.
  - intros i Hi.
    assert (Hi2: 0 <= i < 2) by (rewrite Hsub_len in Hi; lia).
    rewrite Znth_sublist by lia.
    replace (i + 0) with i by lia.
    destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
    + subst i.
      rewrite Znth_replace_Znth_Same by (try rewrite Zlength_replace_Znth; lia).
      reflexivity.
    + assert (Hi1: i = 1) by lia.
      subst i.
      rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Same by lia.
      reflexivity.
Qed.

Lemma sublist_replace_two_tail:
  forall (l: list Z) a b hi,
    2 <= hi <= Zlength l ->
    sublist 2 hi (replace_Znth 0 a (replace_Znth 1 b l)) = sublist 2 hi l.
Proof.
  intros l a b hi Hrange.
  assert (Hsub_len:
    Zlength (sublist 2 hi (replace_Znth 0 a (replace_Znth 1 b l))) = hi - 2).
  {
    rewrite Zlength_sublist by (rewrite !Zlength_replace_Znth; lia).
    lia.
  }
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite Hsub_len.
    rewrite Zlength_sublist by lia.
    lia.
  - intros i Hi.
    assert (Hi_tail: 0 <= i < hi - 2) by (rewrite Hsub_len in Hi; lia).
    rewrite Znth_sublist by (try rewrite !Zlength_replace_Znth; lia).
    rewrite Znth_sublist by lia.
    replace (i + 2) with (2 + i) by lia.
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
Qed.

Lemma mpn_lshift_list_to_Z_single_sublist:
  forall (Base: Z) (l: list Z) (i: Z),
    0 <= i < Zlength l ->
    list_to_Z Base (sublist i (i + 1) l) = Znth i l 0.
Proof.
  intros.
  rewrite (sublist_single 0 i l) by lia.
  rewrite list_to_Z_single.
  reflexivity.
Qed.

Lemma mpn_lshift_list_to_Z_suffix_cons:
  forall (Base: Z) (l: list Z) (i n: Z),
    0 <= i < n ->
    n <= Zlength l ->
    list_to_Z Base (sublist i n l) =
      Znth i l 0 + Base * list_to_Z Base (sublist (i + 1) n l).
Proof.
  intros.
  rewrite (sublist_split i n (i + 1) l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  change ([Znth i l 0] ++ sublist (i + 1) n l)
    with (Znth i l 0 :: sublist (i + 1) n l).
  rewrite list_to_Z_cons.
  reflexivity.
Qed.

Lemma list_to_Z_high_limb_quot_uint :
  forall (l : list Z) n,
    Zlength l = n ->
    1 <= n ->
    list_within_bound UINT_MOD l ->
    list_to_Z UINT_MOD l / UINT_MOD ^ (n - 1) = Znth (n - 1) l 0.
Proof.
  intros l n Hlen Hn Hbound.
  pose proof (list_to_Z_nth UINT_MOD UINT_MOD_pos l n (n - 1)
                ltac:(rewrite Hlen; lia) Hbound) as Hnth.
  rewrite Hnth.
  symmetry.
  apply Z.mod_small.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l Hbound) as Hval.
  split.
  - apply Z.div_pos.
    + lia.
    + apply Z.pow_pos_nonneg; unfold UINT_MOD; lia.
  - apply Z.div_lt_upper_bound.
    + apply Z.pow_pos_nonneg; unfold UINT_MOD; lia.
    + rewrite Hlen in Hval.
      replace (UINT_MOD ^ (n - 1) * UINT_MOD)
        with (UINT_MOD ^ n).
      * lia.
      * assert (Hpow_eq : UINT_MOD ^ n = UINT_MOD ^ (n - 1) * UINT_MOD).
        {
          replace UINT_MOD with (UINT_MOD ^ 1) at 3
            by (rewrite Z.pow_1_r; reflexivity).
          rewrite <- Z.pow_add_r by lia.
          f_equal.
          lia.
        }
        exact Hpow_eq.
Qed.

Lemma list_to_Z_high2_quot_uint :
  forall (l : list Z) n,
    Zlength l = n ->
    2 <= n ->
    list_within_bound UINT_MOD l ->
    list_to_Z UINT_MOD l / UINT_MOD ^ (n - 2) =
      Znth (n - 2) l 0 + Znth (n - 1) l 0 * UINT_MOD.
Proof.
  intros l n Hlen Hn Hbound.
  pose proof (sublist_split 0 n (n - 2) l ltac:(lia) ltac:(lia)) as Hsplit.
  rewrite (sublist_self l n ltac:(lia)) in Hsplit.
  assert (Htail_bound:
            list_within_bound UINT_MOD
              (sublist 0 (n - 2) l ++ sublist (n - 2) n l)).
  {
    rewrite <- Hsplit.
    exact Hbound.
  }
  pose proof (list_to_Z_split UINT_MOD UINT_MOD_pos
    (sublist 0 (n - 2) l) (sublist (n - 2) n l) Htail_bound) as [_ Hquot].
  rewrite Zlength_sublist in Hquot by lia.
  replace (n - 2 - 0) with (n - 2) in Hquot by lia.
  rewrite <- Hsplit in Hquot.
  rewrite <- Hquot.
  rewrite (sublist_split (n - 2) n (n - 1) l) by lia.
  replace (sublist (n - 2) (n - 1) l)
    with (sublist (n - 2) ((n - 2) + 1) l) by (f_equal; lia).
  rewrite (sublist_single 0 (n - 2) l) by lia.
  replace (sublist (n - 1) n l)
    with (sublist (n - 1) ((n - 1) + 1) l) by (f_equal; lia).
  rewrite (sublist_single 0 (n - 1) l) by lia.
  change ([Znth (n - 2) l 0] ++ [Znth (n - 1) l 0])
    with (Znth (n - 2) l 0 :: Znth (n - 1) l 0 :: nil).
  rewrite !list_to_Z_cons, list_to_Z_nil.
  ring.
Qed.

Lemma list_to_Z_prefix_mid_high_limb_quot_uint :
  forall (l l_mid : list Z) n dn i,
    Zlength l = n ->
    l_mid = sublist i (i + dn) l ->
    0 <= i ->
    1 <= dn ->
    i + dn <= n ->
    list_within_bound UINT_MOD l ->
    list_to_Z UINT_MOD (sublist 0 (dn + i) l) / UINT_MOD ^ (dn + i - 1) =
      Znth (dn - 1) l_mid 0.
Proof.
  intros l l_mid n dn i Hlen Hmid Hi Hdn Hrange Hbound.
  pose proof (list_to_Z_high_limb_quot_uint
                (sublist 0 (dn + i) l) (dn + i)) as Hhigh.
  rewrite Zlength_sublist in Hhigh by lia.
  specialize (Hhigh ltac:(lia) ltac:(lia)).
  specialize (Hhigh (list_within_bound_sublist UINT_MOD l 0 (dn + i)
                       ltac:(lia) ltac:(rewrite Hlen; lia) Hbound)).
  replace (dn + i - 0) with (dn + i) in Hhigh by lia.
  rewrite Hhigh.
  rewrite Znth_sublist by lia.
  replace (dn + i - 1 + 0) with (dn + i - 1) by lia.
  subst l_mid.
  rewrite Znth_sublist by lia.
  replace (dn - 1 + i) with (dn + i - 1) by lia.
  reflexivity.
Qed.

Lemma mpn_div_qr_pi1_trial_le :
  forall (l_cur l_mid l_dp : list Z)
         (dn0 nn0 i n1 remv dval d1 d0 : Z),
    dn0 > 2 ->
    0 <= i ->
    i <= nn0 - dn0 ->
    Zlength l_cur = nn0 ->
    Zlength l_dp = dn0 ->
    l_mid = sublist i (i + dn0) l_cur ->
    list_within_bound UINT_MOD l_cur ->
    list_within_bound UINT_MOD l_dp ->
    list_to_Z UINT_MOD l_dp = dval ->
    d1 = Znth (dn0 - 1) l_dp 0 ->
    d0 = Znth (dn0 - 2) l_dp 0 ->
    remv =
      n1 * UINT_MOD ^ (dn0 + i) +
      list_to_Z UINT_MOD (sublist 0 (dn0 + i) l_cur) ->
    remv < dval * UINT_MOD ^ (i + 1) ->
    0 <= n1 ->
    n1 * UINT_MOD + Znth (dn0 - 1) l_mid 0 <= d1 * UINT_MOD + d0.
Proof.
  intros l_cur l_mid l_dp dn0 nn0 i n1 remv dval d1 d0
         Hdn Hi Hirange Hcur_len Hdp_len Hmid Hcur_bound Hdp_bound
         Hdval Hd1 Hd0 Hrem Hrem_lt Hn1_nonneg.
  pose (den := UINT_MOD ^ (dn0 + i - 1)).
  assert (Hden_pos : 0 < den).
  {
    unfold den.
    apply Z.pow_pos_nonneg; unfold UINT_MOD; lia.
  }
  assert (Hdiv_le :
            remv / den <= (dval * UINT_MOD ^ (i + 1)) / den).
  {
    apply Z.div_le_mono.
    - exact Hden_pos.
    - lia.
  }
  rewrite Hrem in Hdiv_le.
  assert (Hden_shape :
            UINT_MOD ^ (dn0 + i) =
            UINT_MOD * den).
  {
    unfold den.
    replace (dn0 + i) with (1 + (dn0 + i - 1)) at 1 by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    lia.
  }
  rewrite Hden_shape in Hdiv_le.
  replace (n1 * (UINT_MOD * den)) with ((n1 * UINT_MOD) * den) in Hdiv_le by ring.
  rewrite Z.div_add_l in Hdiv_le by lia.
  assert (Hprefix :
            list_to_Z UINT_MOD (sublist 0 (dn0 + i) l_cur) / den =
            Znth (dn0 - 1) l_mid 0).
  {
    unfold den.
    apply list_to_Z_prefix_mid_high_limb_quot_uint with (n := nn0);
      try assumption; try lia.
  }
  rewrite Hprefix in Hdiv_le.
  assert (Hrhs_den :
            den = UINT_MOD ^ (dn0 - 2) * UINT_MOD ^ (i + 1)).
  {
    unfold den.
    replace (dn0 + i - 1) with ((dn0 - 2) + (i + 1)) by lia.
    rewrite Z.pow_add_r by lia.
    reflexivity.
  }
  rewrite Hrhs_den in Hdiv_le.
  rewrite Z.div_mul_cancel_r in Hdiv_le.
  2: { apply Z.pow_nonzero; unfold UINT_MOD; lia. }
  2: { apply Z.pow_nonzero; unfold UINT_MOD; lia. }
  rewrite <- Hdval in Hdiv_le.
  pose proof (list_to_Z_high2_quot_uint l_dp dn0 Hdp_len ltac:(lia) Hdp_bound) as Hdp_high.
  rewrite Hdp_high in Hdiv_le.
  rewrite Hd1, Hd0.
  lia.
Qed.

Lemma mpn_div_qr_pi1_trial_lt_neq :
  forall n1 d1 n0 d0,
    0 <= n0 ->
    n0 < UINT_MOD ->
    0 <= d0 ->
    d0 < UINT_MOD ->
    n1 <> d1 ->
    n1 * UINT_MOD + n0 <= d1 * UINT_MOD + d0 ->
    n1 * UINT_MOD + n0 < d1 * UINT_MOD + d0.
Proof.
  intros.
  unfold UINT_MOD in *.
  lia.
Qed.

Lemma mpn_div_qr_pi1_trial_lt_eq_high :
  forall n1 d1 n0 d0,
    0 <= n0 ->
    n0 < UINT_MOD ->
    0 <= d0 ->
    d0 < UINT_MOD ->
    n1 = d1 ->
    n0 <> d0 ->
    n1 * UINT_MOD + n0 <= d1 * UINT_MOD + d0 ->
    n1 * UINT_MOD + n0 < d1 * UINT_MOD + d0.
Proof.
  intros.
  subst.
  unfold UINT_MOD in *.
  lia.
Qed.

Lemma mpn_lshift_limb_decompose:
  forall a cnt,
    0 <= a < UINT_MOD ->
    1 <= cnt < 32 ->
    unsigned_last_nbits (Z.shiftl a cnt) 32 +
      Z.shiftr a (32 - cnt) * UINT_MOD = a * 2 ^ cnt.
Proof.
  intros a cnt Ha Hcnt.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  unfold unsigned_last_nbits.
  change (2 ^ 32) with UINT_MOD.
  rewrite Z.mod_eq by (unfold UINT_MOD; lia).
  assert (Hpow: UINT_MOD = 2 ^ (32 - cnt) * 2 ^ cnt).
  {
    unfold UINT_MOD.
    rewrite <- Z.pow_add_r by lia.
    replace (32 - cnt + cnt) with 32 by lia.
    reflexivity.
  }
  rewrite Hpow at 2.
  rewrite Z.mul_comm.
  replace (2 ^ cnt * a) with (a * 2 ^ cnt) by ring.
  rewrite Z.div_mul_cancel_r by (apply Z.pow_nonzero; lia).
  ring.
Qed.

Lemma mpn_lshift_lowbits_zero:
  forall a cnt,
    1 <= cnt < 32 ->
    (unsigned_last_nbits (a * 2 ^ cnt) 32) mod 2 ^ cnt = 0.
Proof.
  intros a cnt Hcnt.
  unfold unsigned_last_nbits.
  change (2 ^ 32) with UINT_MOD.
  replace ((a * 2 ^ cnt) mod UINT_MOD)
    with (a * 2 ^ cnt - UINT_MOD * ((a * 2 ^ cnt) / UINT_MOD)).
  2: {
    symmetry.
    apply Z.mod_eq.
    unfold UINT_MOD; lia.
  }
  rewrite Zminus_mod.
  rewrite Z_mod_mult.
  assert (Hpow: UINT_MOD = 2 ^ (32 - cnt) * 2 ^ cnt).
  {
    unfold UINT_MOD.
    rewrite <- Z.pow_add_r by lia.
    replace (32 - cnt + cnt) with 32 by lia.
    reflexivity.
  }
  rewrite Hpow.
  rewrite Zmult_mod.
  rewrite Z_mod_mult.
  rewrite Z.mul_0_l.
  rewrite Z.sub_0_r.
  rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
  reflexivity.
Qed.

Lemma mpn_lshift_lor_add:
  forall hi_src low cnt,
    0 <= low < UINT_MOD ->
    1 <= cnt < 32 ->
    Z.lor (unsigned_last_nbits (hi_src * 2 ^ cnt) 32)
      (Z.shiftr low (32 - cnt)) =
    unsigned_last_nbits (hi_src * 2 ^ cnt) 32 +
      Z.shiftr low (32 - cnt).
Proof.
  intros hi_src low cnt Hlow Hcnt.
  set (hi := unsigned_last_nbits (hi_src * 2 ^ cnt) 32).
  set (lo := Z.shiftr low (32 - cnt)).
  assert (Hlo_bound: 0 <= lo < 2 ^ cnt).
  {
    subst lo.
    rewrite Z.shiftr_div_pow2 by lia.
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound.
      + apply Z.pow_pos_nonneg; lia.
      + replace (2 ^ (32 - cnt) * 2 ^ cnt) with UINT_MOD.
        * lia.
        * unfold UINT_MOD.
          rewrite <- Z.pow_add_r by lia.
          replace (32 - cnt + cnt) with 32 by lia.
          reflexivity.
  }
  assert (Hhi_mask: Z.land hi (Z.ones cnt) = 0).
  {
    rewrite Z.land_ones by lia.
    subst hi.
    apply mpn_lshift_lowbits_zero.
    lia.
  }
  assert (Hland0: Z.land hi lo = 0).
  {
    replace lo with (Z.land lo (Z.ones cnt)).
    2: {
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small; lia.
    }
    rewrite (Z.land_comm lo (Z.ones cnt)).
    rewrite Z.land_assoc.
    rewrite Hhi_mask.
    apply Z.land_0_l.
  }
  rewrite <- Z.lxor_lor by exact Hland0.
  symmetry.
  apply Z.add_nocarry_lxor.
  exact Hland0.
Qed.

Lemma unsigned_last_nbits_lshift_upper_gap:
  forall x cnt,
    0 <= x < UINT_MOD ->
    1 <= cnt < 32 ->
    unsigned_last_nbits (x * 2 ^ cnt) 32 <= UINT_MOD - 2 ^ cnt.
Proof.
  intros x cnt Hx Hcnt.
  set (r := unsigned_last_nbits (x * 2 ^ cnt) 32).
  assert (Hr: 0 <= r < UINT_MOD).
  { subst r. change UINT_MOD with (2 ^ 32). apply unsigned_Lastnbits_range. lia. }
  assert (Hmod: r mod 2 ^ cnt = 0).
  { subst r. apply mpn_lshift_lowbits_zero. lia. }
  pose proof (Z.div_mod r (2 ^ cnt) ltac:(apply Z.pow_nonzero; lia)) as Hdm.
  rewrite Hmod in Hdm.
  rewrite Z.add_0_r in Hdm.
  assert (Hq_bound: r / 2 ^ cnt < 2 ^ (32 - cnt)).
  { apply Z.div_lt_upper_bound.
    - apply Z.pow_pos_nonneg; lia.
    - change UINT_MOD with (2 ^ 32) in Hr.
      replace (2 ^ cnt * 2 ^ (32 - cnt)) with (2 ^ 32).
      + exact (proj2 Hr).
      + rewrite <- Z.pow_add_r by lia. replace (cnt + (32 - cnt)) with 32 by ring. reflexivity.
  }
  rewrite Hdm.
  change UINT_MOD with (2 ^ 32).
  replace (2 ^ 32) with (2 ^ cnt * 2 ^ (32 - cnt)).
  - nia.
  - rewrite <- Z.pow_add_r by lia. replace (cnt + (32 - cnt)) with 32 by ring. reflexivity.
Qed.

Lemma mpn_lshift_high2_quot_uint:
  forall (l: list Z) n cnt,
    Zlength l = n ->
    n > 2 ->
    list_within_bound UINT_MOD l ->
    1 <= cnt < 32 ->
    Znth (n - 1) l 0 * 2 ^ cnt < UINT_MOD ->
    (list_to_Z UINT_MOD l * 2 ^ cnt) / UINT_MOD ^ (n - 2) =
      Z.lor (unsigned_last_nbits (Z.shiftl (Znth (n - 2) l 0) cnt) 32)
        (Z.shiftr (Znth (n - 3) l 0) (32 - cnt)) +
      Z.lor (unsigned_last_nbits (Z.shiftl (Znth (n - 1) l 0) cnt) 32)
        (Z.shiftr (Znth (n - 2) l 0) (32 - cnt)) * UINT_MOD.
Proof.
  intros l n cnt Hlen Hn Hbound Hcnt Htop_no_over.
  assert (Hidx_top : 0 <= n - 1 < Zlength l) by (rewrite Hlen; clear - Hn; lia).
  assert (Hidx_mid : 0 <= n - 2 < Zlength l) by (rewrite Hlen; clear - Hn; lia).
  assert (Hidx_low : 0 <= n - 3 < Zlength l) by (rewrite Hlen; clear - Hn; lia).
  set (top := Znth (n - 1) l 0).
  set (mid := Znth (n - 2) l 0).
  set (low := Znth (n - 3) l 0).
  set (prefix := list_to_Z UINT_MOD (sublist 0 (n - 3) l)).
  set (P := UINT_MOD ^ (n - 3)).
  set (s := 2 ^ cnt).
  assert (Htop_bound : 0 <= top < UINT_MOD).
  { subst top. exact (list_within_bound_Znth_bound UINT_MOD l (n - 1) Hidx_top Hbound). }
  assert (Hmid_bound : 0 <= mid < UINT_MOD).
  { subst mid. exact (list_within_bound_Znth_bound UINT_MOD l (n - 2) Hidx_mid Hbound). }
  assert (Hlow_bound : 0 <= low < UINT_MOD).
  { subst low. exact (list_within_bound_Znth_bound UINT_MOD l (n - 3) Hidx_low Hbound). }
  assert (Hprefix_bound_prop : list_within_bound UINT_MOD (sublist 0 (n - 3) l)).
  { apply list_within_bound_sublist.
    - split; [apply Z.le_refl| exact (proj1 Hidx_low)].
    - apply Z.lt_le_incl; exact (proj2 Hidx_low).
    - exact Hbound. }
  assert (Hsub_len : Zlength (sublist 0 (n - 3) l) = n - 3).
  { rewrite Zlength_sublist.
    - ring.
    - split; [split; [apply Z.le_refl| exact (proj1 Hidx_low)]|
              apply Z.lt_le_incl; exact (proj2 Hidx_low)]. }
  assert (Hprefix_bound : 0 <= prefix < P).
  { subst prefix P.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos
      (sublist 0 (n - 3) l) Hprefix_bound_prop) as Hpre.
    rewrite Hsub_len in Hpre.
    exact Hpre. }
  assert (HPpos : 0 < P).
  { subst P. apply Z.pow_pos_nonneg; unfold UINT_MOD; lia. }
  assert (Hspos : 0 < s).
  { subst s. apply Z.pow_pos_nonneg; lia. }
  assert (Hpow1 : UINT_MOD ^ (n - 2) = UINT_MOD * P).
  { subst P. replace (n - 2) with ((n - 3) + 1) by ring.
    rewrite Z.pow_add_r by (clear - Hn; lia). rewrite Z.pow_1_r. ring. }
  assert (Hpow2 : UINT_MOD ^ (n - 1) = UINT_MOD * UINT_MOD * P).
  { subst P. replace (n - 1) with ((n - 3) + 2) by ring.
    rewrite Z.pow_add_r by (clear - Hn; lia). change (UINT_MOD ^ 2) with (UINT_MOD * UINT_MOD). ring. }
  assert (Hdecomp :
    list_to_Z UINT_MOD l =
      prefix + low * P + mid * (UINT_MOD * P) +
      top * (UINT_MOD * UINT_MOD * P)).
  { pose proof (list_to_Z_list_append UINT_MOD UINT_MOD_pos l
      (n - 1) Hidx_top Hbound) as H1.
    replace (n - 1 + 1) with n in H1 by ring.
    rewrite (sublist_self l n (eq_sym Hlen)) in H1.
    pose proof (list_to_Z_list_append UINT_MOD UINT_MOD_pos l
      (n - 2) Hidx_mid Hbound) as H2.
    replace (n - 2 + 1) with (n - 1) in H2 by ring.
    pose proof (list_to_Z_list_append UINT_MOD UINT_MOD_pos l
      (n - 3) Hidx_low Hbound) as H3.
    replace (n - 3 + 1) with (n - 2) in H3 by ring.
    rewrite H2 in H1.
    rewrite H3 in H1.
    subst prefix low mid top.
    fold P.
    rewrite Hpow1 in H1.
    rewrite Hpow2 in H1.
    exact H1. }
  set (rlow := unsigned_last_nbits (Z.shiftl low cnt) 32).
  set (rmid := unsigned_last_nbits (Z.shiftl mid cnt) 32).
  set (qlo := Z.shiftr low (32 - cnt)).
  set (qmid := Z.shiftr mid (32 - cnt)).
  assert (Hlowdec : rlow + qlo * UINT_MOD = low * s).
  { subst rlow qlo s. apply mpn_lshift_limb_decompose; assumption. }
  assert (Hmiddec : rmid + qmid * UINT_MOD = mid * s).
  { subst rmid qmid s. apply mpn_lshift_limb_decompose; assumption. }
  assert (Hrlow_nonneg : 0 <= rlow).
  { subst rlow.
    pose proof (unsigned_Lastnbits_range (Z.shiftl low cnt) 32 ltac:(lia)) as Hr.
    change (2 ^ 32) with UINT_MOD in Hr. exact (proj1 Hr). }
  assert (Hrlow_gap : rlow <= UINT_MOD - s).
  { subst rlow s. rewrite Z.shiftl_mul_pow2 by lia.
    apply unsigned_last_nbits_lshift_upper_gap; assumption. }
  assert (Hsmall : 0 <= prefix * s + rlow * P < UINT_MOD * P).
  { destruct Hprefix_bound as [Hpre0 Hpre1].
    split.
    - apply Z.add_nonneg_nonneg; apply Z.mul_nonneg_nonneg; lia.
    - assert (prefix * s < P * s) by (apply Z.mul_lt_mono_pos_r; lia).
      assert (rlow * P <= (UINT_MOD - s) * P) by (apply Z.mul_le_mono_nonneg_r; lia).
      replace (UINT_MOD * P) with (P * s + (UINT_MOD - s) * P) by ring.
      apply Z.add_lt_le_mono; assumption. }
  assert (Hlor_top :
    Z.lor (unsigned_last_nbits (Z.shiftl top cnt) 32) qmid = top * s + qmid).
  { subst qmid s.
    replace (unsigned_last_nbits (Z.shiftl top cnt) 32)
      with (unsigned_last_nbits (top * 2 ^ cnt) 32).
    2: { rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
    rewrite (mpn_lshift_lor_add top mid cnt Hmid_bound Hcnt).
    rewrite unsigned_last_nbits_eq by
      (split; [apply Z.mul_nonneg_nonneg; lia| exact Htop_no_over]).
    reflexivity. }
  assert (Hlor_mid : Z.lor rmid qlo = rmid + qlo).
  { subst rmid qlo s.
    replace (unsigned_last_nbits (Z.shiftl mid cnt) 32)
      with (unsigned_last_nbits (mid * 2 ^ cnt) 32).
    2: { rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
    apply mpn_lshift_lor_add; assumption. }
  rewrite Hdecomp.
  rewrite Hpow1.
  rewrite Hlor_mid, Hlor_top.
  assert (Hnum :
    (prefix + low * P + mid * (UINT_MOD * P) +
       top * (UINT_MOD * UINT_MOD * P)) * s =
    (prefix * s + rlow * P) +
      (qlo + mid * s + top * s * UINT_MOD) * (UINT_MOD * P)).
  { replace ((prefix + low * P + mid * (UINT_MOD * P) +
                top * (UINT_MOD * UINT_MOD * P)) * s)
      with (prefix * s + (low * s) * P +
              (mid * s) * (UINT_MOD * P) +
              (top * s) * (UINT_MOD * UINT_MOD * P)) by ring.
    rewrite <- Hlowdec. ring. }
  rewrite Hnum.
  rewrite (Z.div_add (prefix * s + rlow * P)
    (qlo + mid * s + top * s * UINT_MOD) (UINT_MOD * P)).
  - rewrite Z.div_small by exact Hsmall.
    rewrite <- Hmiddec.
    ring.
  - apply Z.neq_mul_0.
    + unfold UINT_MOD; lia.
Qed.

Lemma mpn_lshift_initial_equation:
  forall (l: list Z) (n cnt: Z),
    n > 0 ->
    Zlength l = n ->
    list_within_bound UINT_MOD l ->
    1 <= cnt < 32 ->
    unsigned_last_nbits (Znth (n - 1) l 0 * 2 ^ cnt) 32 +
      list_to_Z UINT_MOD nil * UINT_MOD +
      (Znth (n - 1) l 0 ÷ 2 ^ (32 - cnt)) * UINT_MOD ^ (n - (n - 1)) =
      list_to_Z UINT_MOD (sublist (n - 1) n l) * 2 ^ cnt.
Proof.
  intros l n cnt Hn Hlen Hbound Hcnt.
  replace (sublist (n - 1) n l)
    with (sublist (n - 1) ((n - 1) + 1) l)
    by (f_equal; lia).
  assert (Hidx_last: 0 <= n - 1 < Zlength l).
  { rewrite Hlen. split; lia. }
  rewrite (mpn_lshift_list_to_Z_single_sublist UINT_MOD l (n - 1)) by exact Hidx_last.
  rewrite list_to_Z_nil.
  replace (UINT_MOD ^ (n - (n - 1))) with UINT_MOD
    by (replace (n - (n - 1)) with 1 by lia; ring).
  ring_simplify.
  rewrite Z.quot_div_nonneg.
  2: { apply (list_within_bound_Znth_bound UINT_MOD l (n - 1)); try exact Hbound; lia. }
  2: { apply Z.pow_pos_nonneg; lia. }
  replace (UINT_MOD * (Znth (n - 1) l 0 / 2 ^ (32 - cnt)))
    with ((Znth (n - 1) l 0 / 2 ^ (32 - cnt)) * UINT_MOD) by ring.
  rewrite <- Z.shiftr_div_pow2 by lia.
  replace (unsigned_last_nbits (Znth (n - 1) l 0 * 2 ^ cnt) 32)
    with (unsigned_last_nbits (Z.shiftl (Znth (n - 1) l 0) cnt) 32).
  2: { f_equal. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  apply mpn_lshift_limb_decompose.
  - apply (list_within_bound_Znth_bound UINT_MOD l (n - 1)); try exact Hbound; lia.
  - lia.
Qed.

Lemma mpn_lshift_step_equation:
  forall (l done: list Z) (n i cnt retval high low tnc: Z),
    0 <= i ->
    i + 1 < n ->
    n <= Zlength l ->
    1 <= cnt < 32 ->
    list_within_bound UINT_MOD l ->
    low = Znth i l 0 ->
    high = unsigned_last_nbits (Znth (i + 1) l 0 * 2 ^ cnt) 32 ->
    tnc = 32 - cnt ->
    high + list_to_Z UINT_MOD done * UINT_MOD +
      retval * UINT_MOD ^ (n - (i + 1)) =
      list_to_Z UINT_MOD (sublist (i + 1) n l) * 2 ^ cnt ->
    unsigned_last_nbits (Z.shiftl low cnt) 32 +
      list_to_Z UINT_MOD
        (replace_Znth ((i + 1) - (i + 1))
           (Z.lor high (Z.shiftr low tnc))
           (sublist (i + 1) (i + 2) l) ++ done) * UINT_MOD +
      retval * UINT_MOD ^ (n - i) =
      list_to_Z UINT_MOD (sublist i n l) * 2 ^ cnt.
Proof.
  intros l done n i cnt retval high low tnc Hi Hin Hlen Hcnt Hbound Hlow Hhigh Htnc Hstep.
  replace (i + 1 - (i + 1)) with 0 by lia.
  set (joined := Z.lor high (Z.shiftr low tnc)).
  assert (Hrep_cond: 0 <= i + 1 /\ i + 1 < i + 2 /\ i + 2 <= Zlength l).
  { clear Hstep Hbound Hlow Hhigh Htnc Hcnt. lia. }
  pose proof (replace_Znth_sublist_head l (i + 1) (i + 2) joined Hrep_cond) as Hrep.
  rewrite Hrep.
  replace ((i + 1) + 1) with (i + 2) by lia.
  rewrite Zsublist_nil by lia.
  simpl.
  subst joined.
  rewrite list_to_Z_cons.
  rewrite Hlow, Hhigh, Htnc.
  rewrite Hhigh in Hstep.
  assert (Hidx_i: 0 <= i < Zlength l).
  { clear Hstep Hhigh Htnc Hlow Hbound Hcnt. lia. }
  rewrite (mpn_lshift_lor_add (Znth (i + 1) l 0) (Znth i l 0) cnt).
  2: { apply (list_within_bound_Znth_bound UINT_MOD l i); try exact Hbound; exact Hidx_i. }
  2: { lia. }
  pose proof (mpn_lshift_limb_decompose (Znth i l 0) cnt) as Hdec.
  specialize (Hdec ltac:(apply (list_within_bound_Znth_bound UINT_MOD l i); try exact Hbound; exact Hidx_i) ltac:(lia)).
  assert (Hpow: UINT_MOD ^ (n - i) = UINT_MOD * UINT_MOD ^ (n - (i + 1))).
  {
    replace (n - i) with ((n - (i + 1)) + 1) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    lia.
  }
  rewrite Hpow.
  assert (Hi_n: 0 <= i < n).
  { clear Hstep Hbound Hlow Hhigh Htnc Hcnt. lia. }
  pose proof (mpn_lshift_list_to_Z_suffix_cons UINT_MOD l i n Hi_n Hlen) as Hsuffix.
  rewrite Hsuffix.
  replace (unsigned_last_nbits (Z.shiftl (Znth i l 0) cnt) 32 +
             (unsigned_last_nbits (Znth (i + 1) l 0 * 2 ^ cnt) 32 +
              Z.shiftr (Znth i l 0) (32 - cnt) +
              UINT_MOD * list_to_Z UINT_MOD done) * UINT_MOD +
             retval * (UINT_MOD * UINT_MOD ^ (n - (i + 1))))
    with ((unsigned_last_nbits (Z.shiftl (Znth i l 0) cnt) 32 +
           Z.shiftr (Znth i l 0) (32 - cnt) * UINT_MOD) +
          UINT_MOD *
          (unsigned_last_nbits (Znth (i + 1) l 0 * 2 ^ cnt) 32 +
           list_to_Z UINT_MOD done * UINT_MOD +
           retval * UINT_MOD ^ (n - (i + 1)))) by ring.
  rewrite Hstep.
  rewrite Hdec.
  ring.
Qed.

Lemma mpn_lshift_join_limb_bound:
  forall high low hi_src cnt,
    0 <= low <= 4294967295 ->
    1 <= cnt < 32 ->
    high = unsigned_last_nbits (hi_src * 2 ^ cnt) 32 ->
    0 <= Z.lor high (Z.shiftr low (32 - cnt)) < UINT_MOD.
Proof.
  intros high low hi_src cnt Hlow Hcnt Hhigh.
  subst high.
  set (hi := unsigned_last_nbits (hi_src * 2 ^ cnt) 32).
  set (lo := Z.shiftr low (32 - cnt)).
  assert (Hhi_bound: 0 <= hi < 2 ^ 32).
  { subst hi. apply unsigned_Lastnbits_range. lia. }
  assert (Hlo_bound: 0 <= lo < 2 ^ 32).
  {
    subst lo.
    rewrite Z.shiftr_div_pow2 by lia.
    split.
    - apply Z.div_pos; lia.
    - apply Z.le_lt_trans with (m := low).
      + apply Z.div_le_upper_bound.
        * apply Z.pow_pos_nonneg; lia.
        * replace low with (1 * low) at 1 by ring.
          apply Z.mul_le_mono_nonneg_r; lia.
      + replace (2 ^ 32) with 4294967296 by reflexivity.
        lia.
  }
  pose proof (unsigned_last_nbits_lor_distr_missing hi lo 32 ltac:(lia) Hhi_bound Hlo_bound) as Hmask.
  pose proof (unsigned_Lastnbits_range (Z.lor hi lo) 32 ltac:(lia)) as Hrange.
  rewrite Hmask in Hrange.
  change (2 ^ 32) with UINT_MOD in Hrange.
  exact Hrange.
Qed.

Lemma mpn_lshift_done_bound:
  forall (l done: list Z) (n i cnt high low tnc: Z),
    0 <= i ->
    i + 1 < n ->
    n <= Zlength l ->
    list_within_bound UINT_MOD done ->
    list_within_bound UINT_MOD l ->
    1 <= cnt < 32 ->
    0 <= low <= 4294967295 ->
    low = Znth i l 0 ->
    high = unsigned_last_nbits (Znth (i + 1) l 0 * 2 ^ cnt) 32 ->
    tnc = 32 - cnt ->
    list_within_bound UINT_MOD
      (replace_Znth ((i + 1) - (i + 1))
         (Z.lor high (Z.shiftr low tnc))
         (sublist (i + 1) (i + 2) l) ++ done).
Proof.
  intros l done n i cnt high low tnc Hi Hin Hlen Hdone Hbound Hcnt Hlow Hloweq Hhigh Htnc.
  replace (i + 1 - (i + 1)) with 0 by lia.
  set (joined := Z.lor high (Z.shiftr low tnc)).
  assert (Hrep_cond: 0 <= i + 1 /\ i + 1 < i + 2 /\ i + 2 <= Zlength l).
  { clear Hdone Hbound Hcnt Hlow Hloweq Hhigh Htnc. lia. }
  pose proof (replace_Znth_sublist_head l (i + 1) (i + 2) joined Hrep_cond) as Hrep.
  rewrite Hrep.
  replace ((i + 1) + 1) with (i + 2) by lia.
  rewrite Zsublist_nil by lia.
  subst joined.
  simpl.
  split.
  - subst tnc.
    apply (mpn_lshift_join_limb_bound high low (Znth (i + 1) l 0) cnt);
      try assumption.
  - exact Hdone.
Qed.

Lemma mpn_lshift_done_length:
  forall (l done: list Z) (n i joined: Z),
    0 <= i ->
    i + 1 < n ->
    n <= Zlength l ->
    Zlength done = n - (i + 2) ->
    Zlength
      (replace_Znth ((i + 1) - (i + 1))
         joined (sublist (i + 1) (i + 2) l) ++ done) =
      n - (i + 1).
Proof.
  intros l done n i joined Hi Hin Hlen Hdone.
  rewrite Zlength_app.
  rewrite Zlength_replace_Znth.
  rewrite Zlength_sublist by lia.
  rewrite Hdone.
  nia.
Qed.

Lemma mpn_lshift_step_equation_cons:
  forall (l done: list Z) (n i cnt retval high low tnc: Z),
    0 <= i ->
    i + 1 < n ->
    n <= Zlength l ->
    1 <= cnt < 32 ->
    list_within_bound UINT_MOD l ->
    low = Znth i l 0 ->
    high = unsigned_last_nbits (Znth (i + 1) l 0 * 2 ^ cnt) 32 ->
    tnc = 32 - cnt ->
    high + list_to_Z UINT_MOD done * UINT_MOD +
      retval * UINT_MOD ^ (n - (i + 1)) =
      list_to_Z UINT_MOD (sublist (i + 1) n l) * 2 ^ cnt ->
    unsigned_last_nbits (Z.shiftl low cnt) 32 +
      list_to_Z UINT_MOD (Z.lor high (Z.shiftr low tnc) :: done) * UINT_MOD +
      retval * UINT_MOD ^ (n - i) =
      list_to_Z UINT_MOD (sublist i n l) * 2 ^ cnt.
Proof.
  intros l done n i cnt retval high low tnc Hi Hin Hlen Hcnt Hbound Hlow Hhigh Htnc Hstep.
  replace (Z.lor high (Z.shiftr low tnc) :: done)
    with (replace_Znth ((i + 1) - (i + 1))
            (Z.lor high (Z.shiftr low tnc))
            (sublist (i + 1) (i + 2) l) ++ done).
  2: {
    replace (i + 1 - (i + 1)) with 0 by lia.
    set (joined := Z.lor high (Z.shiftr low tnc)).
    assert (Hrep_cond: 0 <= i + 1 /\ i + 1 < i + 2 /\ i + 2 <= Zlength l).
    { clear Hstep Hbound Hlow Hhigh Htnc Hcnt. lia. }
    pose proof (replace_Znth_sublist_head l (i + 1) (i + 2) joined Hrep_cond) as Hrep.
    rewrite Hrep.
    replace ((i + 1) + 1) with (i + 2) by lia.
    rewrite Zsublist_nil by lia.
    reflexivity.
  }
  apply (mpn_lshift_step_equation l done n i cnt retval high low tnc);
    assumption.
Qed.

Lemma mpn_rshift_limb_decompose:
  forall a cnt,
    0 <= a < UINT_MOD ->
    1 <= cnt < 32 ->
    a = Z.shiftr a cnt * 2 ^ cnt +
        unsigned_last_nbits (Z.shiftl a (32 - cnt)) 32 ÷ 2 ^ (32 - cnt).
Proof.
  intros a cnt Ha Hcnt.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.quot_div_nonneg.
  2: { unfold unsigned_last_nbits. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  2: { apply Z.pow_pos_nonneg; lia. }
  unfold unsigned_last_nbits.
  change (2 ^ 32) with UINT_MOD.
  assert (Hpow: UINT_MOD = 2 ^ cnt * 2 ^ (32 - cnt)).
  {
    unfold UINT_MOD.
    rewrite <- Z.pow_add_r by lia.
    replace (cnt + (32 - cnt)) with 32 by lia.
    reflexivity.
  }
  rewrite Hpow.
  rewrite Z.mul_mod_distr_r by (apply Z.pow_nonzero; lia).
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
  pose proof (Z.div_mod a (2 ^ cnt)) as Hdm.
  specialize (Hdm ltac:(apply Z.pow_nonzero; lia)).
  rewrite (Z.mul_comm (a / 2 ^ cnt) (2 ^ cnt)).
  exact Hdm.
Qed.

Lemma mpn_rshift_lor_add:
  forall low high cnt,
    0 <= low < UINT_MOD ->
    1 <= cnt < 32 ->
    Z.lor (Z.shiftr low cnt)
      (unsigned_last_nbits (Z.shiftl high (32 - cnt)) 32) =
    Z.shiftr low cnt + unsigned_last_nbits (Z.shiftl high (32 - cnt)) 32.
Proof.
  intros low high cnt Hlow Hcnt.
  set (lo := Z.shiftr low cnt).
  set (hi := unsigned_last_nbits (Z.shiftl high (32 - cnt)) 32).
  assert (Hlo_bound: 0 <= lo < 2 ^ (32 - cnt)).
  {
    subst lo.
    rewrite Z.shiftr_div_pow2 by lia.
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound.
      + apply Z.pow_pos_nonneg; lia.
      + replace (2 ^ cnt * 2 ^ (32 - cnt)) with UINT_MOD.
        * lia.
        * unfold UINT_MOD.
          rewrite <- Z.pow_add_r by lia.
          replace (cnt + (32 - cnt)) with 32 by lia.
          reflexivity.
  }
  assert (Hhi_mask: Z.land hi (Z.ones (32 - cnt)) = 0).
  {
    rewrite Z.land_ones by lia.
    subst hi.
    rewrite Z.shiftl_mul_pow2 by lia.
    apply mpn_lshift_lowbits_zero.
    lia.
  }
  assert (Hland0: Z.land lo hi = 0).
  {
    replace lo with (Z.land lo (Z.ones (32 - cnt))).
    2: {
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small; lia.
    }
    rewrite <- Z.land_assoc.
    rewrite (Z.land_comm (Z.ones (32 - cnt)) hi).
    rewrite Hhi_mask.
    apply Z.land_0_r.
  }
  rewrite <- Z.lxor_lor by exact Hland0.
  symmetry.
  apply Z.add_nocarry_lxor.
  exact Hland0.
Qed.

Lemma unsigned_last_nbits_shiftl_high:
  forall high cnt,
    0 <= high < UINT_MOD ->
    1 <= cnt < 32 ->
    unsigned_last_nbits (Z.shiftl high (32 - cnt)) 32 =
      (high mod 2 ^ cnt) * 2 ^ (32 - cnt).
Proof.
  intros high cnt Hhigh Hcnt.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold unsigned_last_nbits.
  change (2 ^ 32) with UINT_MOD.
  assert (Hpow: UINT_MOD = 2 ^ cnt * 2 ^ (32 - cnt)).
  {
    unfold UINT_MOD.
    rewrite <- Z.pow_add_r by lia.
    replace (cnt + (32 - cnt)) with 32 by lia.
    reflexivity.
  }
  rewrite Hpow.
  pose proof (Z.div_mod high (2 ^ cnt) ltac:(apply Z.pow_nonzero; lia)) as Hdm.
  rewrite Hdm at 1.
  replace ((2 ^ cnt * (high / 2 ^ cnt) + high mod 2 ^ cnt) * 2 ^ (32 - cnt))
    with ((high mod 2 ^ cnt) * 2 ^ (32 - cnt) +
          (high / 2 ^ cnt) * (2 ^ cnt * 2 ^ (32 - cnt))) by ring.
  rewrite Z.mod_add by (apply Z.neq_mul_0; split; apply Z.pow_nonzero; lia).
  rewrite Z.mod_small.
  - reflexivity.
  - pose proof (Z.mod_pos_bound high (2 ^ cnt) ltac:(apply Z.pow_pos_nonneg; lia)) as Hmod.
    split.
    + apply Z.mul_nonneg_nonneg; lia.
    + replace (2 ^ cnt * 2 ^ (32 - cnt)) with
        ((2 ^ cnt) * (2 ^ (32 - cnt))) by ring.
      apply Z.mul_lt_mono_pos_r; lia.
Qed.

Lemma mpn_rshift_two_limb_value:
  forall low high cnt,
    0 <= low < UINT_MOD ->
    0 <= high < UINT_MOD ->
    1 <= cnt < 32 ->
    list_to_Z UINT_MOD
      (Z.lor (Z.shiftr low cnt)
         (unsigned_last_nbits (Z.shiftl high (32 - cnt)) 32)
       :: Z.shiftr high cnt :: nil) =
    (high * UINT_MOD + low) / 2 ^ cnt.
Proof.
  intros low high cnt Hlow Hhigh Hcnt.
  rewrite list_to_Z_cons.
  rewrite list_to_Z_cons.
  rewrite list_to_Z_nil.
  rewrite (mpn_rshift_lor_add low high cnt Hlow Hcnt).
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite unsigned_last_nbits_shiftl_high by assumption.
  assert (Hpow: UINT_MOD = 2 ^ cnt * 2 ^ (32 - cnt)).
  {
    unfold UINT_MOD.
    rewrite <- Z.pow_add_r by lia.
    replace (cnt + (32 - cnt)) with 32 by lia.
    reflexivity.
  }
  rewrite Hpow.
  replace ((high * (2 ^ cnt * 2 ^ (32 - cnt)) + low) / 2 ^ cnt)
    with (high * 2 ^ (32 - cnt) + low / 2 ^ cnt).
  2: {
    replace (high * (2 ^ cnt * 2 ^ (32 - cnt)) + low)
      with (low + (high * 2 ^ (32 - cnt)) * 2 ^ cnt) by ring.
    rewrite Z.div_add by (apply Z.pow_nonzero; lia).
    ring.
  }
  pose proof (Z.div_mod high (2 ^ cnt) ltac:(apply Z.pow_nonzero; lia)) as Hdm.
  replace (high * 2 ^ (32 - cnt))
    with (high / 2 ^ cnt * (2 ^ cnt * 2 ^ (32 - cnt)) +
          high mod 2 ^ cnt * 2 ^ (32 - cnt)).
  - ring.
  - replace (high / 2 ^ cnt * (2 ^ cnt * 2 ^ (32 - cnt)) +
              high mod 2 ^ cnt * 2 ^ (32 - cnt))
      with ((2 ^ cnt * (high / 2 ^ cnt) + high mod 2 ^ cnt) *
            2 ^ (32 - cnt)) by ring.
    rewrite <- Hdm.
    ring.
Qed.

Lemma mpn_rshift_join_limb_bound:
  forall low high cnt,
    0 <= low < UINT_MOD ->
    1 <= cnt < 32 ->
    0 <= Z.lor (Z.shiftr low cnt)
             (unsigned_last_nbits (Z.shiftl high (32 - cnt)) 32) < UINT_MOD.
Proof.
  intros low high cnt Hlow Hcnt.
  set (lo := Z.shiftr low cnt).
  set (hi := unsigned_last_nbits (Z.shiftl high (32 - cnt)) 32).
  assert (Hhi_bound: 0 <= hi < 2 ^ 32).
  { subst hi. apply unsigned_Lastnbits_range. lia. }
  assert (Hlo_bound: 0 <= lo < 2 ^ 32).
  {
    subst lo.
    rewrite Z.shiftr_div_pow2 by lia.
    split.
    - apply Z.div_pos; lia.
    - apply Z.le_lt_trans with (m := low).
      + apply Z.div_le_upper_bound.
        * apply Z.pow_pos_nonneg; lia.
        * replace low with (1 * low) at 1 by ring.
          apply Z.mul_le_mono_nonneg_r; lia.
      + exact (proj2 Hlow).
  }
  pose proof (unsigned_last_nbits_lor_distr_missing lo hi 32 ltac:(lia) Hlo_bound Hhi_bound) as Hmask.
  pose proof (unsigned_Lastnbits_range (Z.lor lo hi) 32 ltac:(lia)) as Hrange.
  rewrite Hmask in Hrange.
  change (2 ^ 32) with UINT_MOD in Hrange.
  exact Hrange.
Qed.

Lemma mpn_rshift_done_length:
  forall (l done: list Z) (n i joined: Z),
    1 <= i ->
    i < n ->
    n <= Zlength l ->
    Zlength done = i - 1 ->
    Zlength
      (done ++ replace_Znth ((i - 1) - (i - 1)) joined
         (sublist (i - 1) i l)) = i.
Proof.
  intros l done n i joined Hi Hin Hlen Hdone.
  rewrite Zlength_app.
  rewrite Zlength_replace_Znth.
  rewrite Zlength_sublist by lia.
  rewrite Hdone.
  nia.
Qed.

Lemma mpn_rshift_done_bound:
  forall (l done: list Z) (n i cnt high low tnc: Z),
    1 <= i ->
    i < n ->
    n <= Zlength l ->
    list_within_bound UINT_MOD done ->
    list_within_bound UINT_MOD l ->
    1 <= cnt < 32 ->
    low = Znth (i - 1) l 0 ÷ 2 ^ cnt ->
    high = Znth i l 0 ->
    tnc = 32 - cnt ->
    list_within_bound UINT_MOD
      (done ++ replace_Znth ((i - 1) - (i - 1))
         (Z.lor low (unsigned_last_nbits (Z.shiftl high tnc) 32))
         (sublist (i - 1) i l)).
Proof.
  intros l done n i cnt high low tnc Hi Hin Hlen Hdone Hbound Hcnt Hlow Hhigh Htnc.
  replace (i - 1 - (i - 1)) with 0 by lia.
  set (joined := Z.lor low (unsigned_last_nbits (Z.shiftl high tnc) 32)).
  assert (Hrep_cond: 0 <= i - 1 /\ i - 1 < i /\ i <= Zlength l).
  { clear Hdone Hbound Hcnt Hlow Hhigh Htnc. lia. }
  pose proof (replace_Znth_sublist_head l (i - 1) i joined Hrep_cond) as Hrep.
  rewrite Hrep.
  replace (i - 1 + 1) with i by lia.
  rewrite Zsublist_nil by lia.
  subst joined.
  apply list_within_bound_app_single.
  - exact Hdone.
  - subst low high tnc.
    assert (Hlowq:
      Znth (i - 1) l 0 ÷ 2 ^ cnt = Z.shiftr (Znth (i - 1) l 0) cnt).
    {
      rewrite Z.shiftr_div_pow2 by lia.
      apply Z.quot_div_nonneg.
      - apply (list_within_bound_Znth_bound UINT_MOD l (i - 1)); try exact Hbound; lia.
      - apply Z.pow_pos_nonneg; lia.
    }
    rewrite Hlowq.
    apply mpn_rshift_join_limb_bound.
    + apply (list_within_bound_Znth_bound UINT_MOD l (i - 1)); try exact Hbound; lia.
    + lia.
Qed.

Lemma mpn_rshift_shifted_low_scale:
  forall a cnt i,
    1 <= cnt < 32 ->
    1 <= i ->
    unsigned_last_nbits (Z.shiftl a (32 - cnt)) 32 * UINT_MOD ^ (i - 1) * 2 ^ cnt =
    (unsigned_last_nbits (Z.shiftl a (32 - cnt)) 32 ÷ 2 ^ (32 - cnt)) * UINT_MOD ^ i.
Proof.
  intros a cnt i Hcnt Hi.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold unsigned_last_nbits.
  change (2 ^ 32) with UINT_MOD.
  assert (Hpow: UINT_MOD = 2 ^ cnt * 2 ^ (32 - cnt)).
  {
    unfold UINT_MOD.
    rewrite <- Z.pow_add_r by lia.
    replace (cnt + (32 - cnt)) with 32 by lia.
    reflexivity.
  }
  rewrite Hpow.
  rewrite Z.mul_mod_distr_r by (apply Z.pow_nonzero; lia).
  rewrite Z.quot_div_nonneg.
  2: {
    apply Z.mul_nonneg_nonneg.
    - apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
    - apply Z.pow_nonneg; lia.
  }
  2: { apply Z.pow_pos_nonneg; lia. }
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
  assert (Hp: (2 ^ cnt * 2 ^ (32 - cnt)) ^ i =
              (2 ^ cnt * 2 ^ (32 - cnt)) ^ (i - 1) *
              (2 ^ cnt * 2 ^ (32 - cnt))).
  {
    replace i with ((i - 1) + 1) at 1 by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    ring.
  }
  rewrite Hp.
  ring.
Qed.

Lemma mpn_rshift_step_equation:
  forall (l done: list Z) (n i cnt retval high low tnc: Z),
    1 <= i ->
    i < n ->
    n <= Zlength l ->
    Zlength done = i - 1 ->
    1 <= cnt < 32 ->
    list_within_bound UINT_MOD l ->
    low = Znth (i - 1) l 0 ÷ 2 ^ cnt ->
    high = Znth i l 0 ->
    tnc = 32 - cnt ->
    list_to_Z UINT_MOD (sublist 0 i l) =
      (list_to_Z UINT_MOD done + low * UINT_MOD ^ (i - 1)) * 2 ^ cnt +
      retval ÷ 2 ^ tnc ->
    list_to_Z UINT_MOD (sublist 0 (i + 1) l) =
      (list_to_Z UINT_MOD
        (done ++ replace_Znth ((i - 1) - (i - 1))
          (Z.lor low (unsigned_last_nbits (Z.shiftl high tnc) 32))
          (sublist (i - 1) i l)) +
       Z.shiftr high cnt * UINT_MOD ^ i) * 2 ^ cnt +
      retval ÷ 2 ^ tnc.
Proof.
  intros l done n i cnt retval high low tnc Hi Hin Hlen Hdone Hcnt Hbound Hlow Hhigh Htnc Hstep.
  rewrite (list_to_Z_list_append UINT_MOD) by (try unfold UINT_MOD; try lia; try exact Hbound).
  rewrite Hstep.
  replace (i - 1 - (i - 1)) with 0 by lia.
  set (joined := Z.lor low (unsigned_last_nbits (Z.shiftl high tnc) 32)).
  assert (Hrep_cond: 0 <= i - 1 /\ i - 1 < i /\ i <= Zlength l).
  { clear Hstep Hbound Hlow Hhigh Htnc Hcnt Hdone. lia. }
  pose proof (replace_Znth_sublist_head l (i - 1) i joined Hrep_cond) as Hrep.
  rewrite Hrep.
  replace (i - 1 + 1) with i by lia.
  rewrite Zsublist_nil by lia.
  subst joined.
  rewrite list_to_Z_concat_r.
  2: { unfold UINT_MOD; lia. }
  2: {
    subst low high tnc.
    assert (Hlowq:
      Znth (i - 1) l 0 ÷ 2 ^ cnt = Z.shiftr (Znth (i - 1) l 0) cnt).
    {
      rewrite Z.shiftr_div_pow2 by lia.
      apply Z.quot_div_nonneg.
      - apply (list_within_bound_Znth_bound UINT_MOD l (i - 1)); try exact Hbound; lia.
      - apply Z.pow_pos_nonneg; lia.
    }
    rewrite Hlowq.
    apply mpn_rshift_join_limb_bound.
    - apply (list_within_bound_Znth_bound UINT_MOD l (i - 1)); try exact Hbound; lia.
    - lia.
  }
  rewrite Hdone.
  subst low high tnc.
  assert (Hlowq:
    Znth (i - 1) l 0 ÷ 2 ^ cnt = Z.shiftr (Znth (i - 1) l 0) cnt).
  {
    rewrite Z.shiftr_div_pow2 by lia.
    apply Z.quot_div_nonneg.
    - apply (list_within_bound_Znth_bound UINT_MOD l (i - 1)); try exact Hbound; lia.
    - apply Z.pow_pos_nonneg; lia.
  }
  rewrite Hlowq.
  rewrite (mpn_rshift_lor_add (Znth (i - 1) l 0) (Znth i l 0) cnt).
  2: { apply (list_within_bound_Znth_bound UINT_MOD l (i - 1)); try exact Hbound; lia. }
  2: { lia. }
  pose proof (mpn_rshift_limb_decompose (Znth i l 0) cnt) as Hdec.
  specialize (Hdec ltac:(apply (list_within_bound_Znth_bound UINT_MOD l i); try exact Hbound; lia) ltac:(lia)).
  pose proof (mpn_rshift_shifted_low_scale (Znth i l 0) cnt i ltac:(lia) ltac:(lia)) as Hscale.
  replace (Znth i l 0 * UINT_MOD ^ i)
    with ((Z.shiftr (Znth i l 0) cnt * 2 ^ cnt +
           unsigned_last_nbits (Z.shiftl (Znth i l 0) (32 - cnt)) 32 ÷
             2 ^ (32 - cnt)) * UINT_MOD ^ i).
  2: { rewrite <- Hdec. reflexivity. }
  replace ((Z.shiftr (Znth i l 0) cnt * 2 ^ cnt +
            unsigned_last_nbits (Z.shiftl (Znth i l 0) (32 - cnt)) 32 ÷
              2 ^ (32 - cnt)) * UINT_MOD ^ i)
    with (Z.shiftr (Znth i l 0) cnt * UINT_MOD ^ i * 2 ^ cnt +
          (unsigned_last_nbits (Z.shiftl (Znth i l 0) (32 - cnt)) 32 ÷
             2 ^ (32 - cnt)) * UINT_MOD ^ i) by ring.
  rewrite <- Hscale.
  ring.
Qed.

Lemma mpn_rshift_quot_limb_bound:
  forall a cnt,
    0 <= a < UINT_MOD ->
    1 <= cnt < 32 ->
    0 <= a ÷ 2 ^ cnt < UINT_MOD.
Proof.
  intros a cnt Ha Hcnt.
  rewrite Z.quot_div_nonneg.
  2: { lia. }
  2: { apply Z.pow_pos_nonneg; lia. }
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound.
    + apply Z.pow_pos_nonneg; lia.
    + replace (2 ^ cnt * UINT_MOD) with (UINT_MOD * 2 ^ cnt) by ring.
      pose proof (Z.pow_pos_nonneg 2 cnt ltac:(lia) ltac:(lia)) as Hpow.
      nia.
Qed.

Lemma mpn_rshift_return_equation:
  forall (l done: list Z) (n i cnt retval low tnc: Z),
    i = n - 1 ->
    Zlength l = n ->
    Zlength done = n - 1 ->
    tnc = 32 - cnt ->
    list_within_bound UINT_MOD l ->
    1 <= cnt < 32 ->
    low = Znth i l 0 ÷ 2 ^ cnt ->
    list_to_Z UINT_MOD (sublist 0 n l) =
      (list_to_Z UINT_MOD done + low * UINT_MOD ^ i) * 2 ^ cnt + retval ÷ 2 ^ tnc ->
    list_to_Z UINT_MOD l =
      list_to_Z UINT_MOD
        (done ++ replace_Znth (i - i) low (sublist i (i + 1) l)) * 2 ^ cnt +
      retval ÷ 2 ^ (32 - cnt).
Proof.
  intros l done n i cnt retval low tnc Hi Hlen Hdone Htnc Hbound Hcnt Hlow Hinv.
  replace (i - i) with 0 by lia.
  assert (Hrep_cond: 0 <= i /\ i < i + 1 /\ i + 1 <= Zlength l).
  {
    rewrite Hlen.
    split.
    - pose proof (Zlength_nonneg done) as Hdone_nonneg.
      rewrite Hi.
      rewrite <- Hdone.
      exact Hdone_nonneg.
    - split.
      + pose proof (Zlength_nonneg done) as Hdone_nonneg.
        rewrite Hi.
        rewrite <- Hdone.
        replace (Zlength done + 1) with (Z.succ (Zlength done)) by lia.
        apply Z.lt_succ_diag_r.
      + rewrite Hi.
        replace (n - 1 + 1) with n by ring.
        apply Z.le_refl.
  }
  pose proof (replace_Znth_sublist_head l i (i + 1) low Hrep_cond) as Hrep.
  rewrite Hrep.
  rewrite Zsublist_nil by lia.
  simpl.
  rewrite list_to_Z_concat_r.
  2: { unfold UINT_MOD; lia. }
  2: {
    subst low.
    apply mpn_rshift_quot_limb_bound.
    - apply (list_within_bound_Znth_bound UINT_MOD l i); try exact Hbound; rewrite Hlen; lia.
    - lia.
  }
  rewrite Hdone.
  rewrite (sublist_self l n) in Hinv by (symmetry; exact Hlen).
  rewrite Hinv.
  change (2 ^ match - cnt with
       | 0 => 32
       | Z.pos y' => Z.pos_sub 32 y'
       | Z.neg y' => Z.pos_sub 32 y'
       end) with (2 ^ (32 - cnt)).
  replace (2 ^ (32 - cnt)) with (2 ^ tnc) by (rewrite Htnc; reflexivity).
  replace (UINT_MOD ^ (n - 1)) with (UINT_MOD ^ i) by (rewrite Hi; reflexivity).
  match goal with
  | |- _ = _ + ?q => replace q with (retval ÷ 2 ^ tnc)
  end.
  2: { f_equal. f_equal. rewrite Htnc. reflexivity. }
  ring.
Qed.

Lemma mpn_rshift_return_zero_if_multiple :
  forall (l l_out: list Z) cnt retval k,
    1 <= cnt < 32 ->
    0 < Zlength l ->
    list_within_bound UINT_MOD l ->
    retval = unsigned_last_nbits (Znth 0 l 0 * 2 ^ (32 - cnt)) 32 ->
    list_to_Z UINT_MOD l =
      list_to_Z UINT_MOD l_out * 2 ^ cnt + retval ÷ 2 ^ (32 - cnt) ->
    list_to_Z UINT_MOD l = k * 2 ^ cnt ->
    retval = 0.
Proof.
  intros l l_out cnt retval k Hcnt Hlen_pos Hbound Hretval Hdecomp Hmult.
  assert (Hz0: 0 <= Znth 0 l 0 < UINT_MOD).
  {
    apply (list_within_bound_Znth_bound UINT_MOD l 0); try exact Hbound; lia.
  }
  pose proof (unsigned_last_nbits_shiftl_high (Znth 0 l 0) cnt Hz0 Hcnt) as Hshift.
  rewrite Z.shiftl_mul_pow2 in Hshift by lia.
  rewrite Hshift in Hretval.
  set (r := Znth 0 l 0 mod 2 ^ cnt) in *.
  assert (Hr_bound: 0 <= r < 2 ^ cnt).
  { subst r. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  assert (Hquot: retval ÷ 2 ^ (32 - cnt) = r).
  {
    replace (retval ÷ 2 ^ (32 - cnt)) with (retval / 2 ^ (32 - cnt)).
    2: {
      symmetry.
      apply Z.quot_div_nonneg.
      - rewrite Hretval.
        apply Z.mul_nonneg_nonneg; lia.
      - apply Z.pow_pos_nonneg; lia.
    }
    rewrite Hretval.
    rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
    reflexivity.
  }
  assert (Hr_mult: r = (k - list_to_Z UINT_MOD l_out) * 2 ^ cnt).
  {
    rewrite Hmult in Hdecomp.
    rewrite Hquot in Hdecomp.
    nia.
  }
  assert (Hcoeff_zero: k - list_to_Z UINT_MOD l_out = 0).
  {
    eapply Z_unit_interval_multiple_zero with
      (k := k - list_to_Z UINT_MOD l_out) (p := 2 ^ cnt) (r := 0).
    - apply Z.pow_pos_nonneg; lia.
    - split; [lia | apply Z.pow_pos_nonneg; lia].
    - exact Hr_bound.
    - rewrite Hr_mult. ring.
  }
  assert (Hr_zero: r = 0) by (rewrite Hr_mult, Hcoeff_zero; ring).
  rewrite Hretval, Hr_zero.
  ring.
Qed.

Lemma mpn_div_qr_preinv_quotient_fit :
  forall (l_np l_dp: list Z) nn dn d shift,
    dn > 2 ->
    dn <= nn ->
    Zlength l_np = nn ->
    Zlength l_dp = dn ->
    list_within_bound UINT_MOD l_np ->
    list_within_bound UINT_MOD l_dp ->
    list_to_Z UINT_MOD l_dp = d * 2 ^ shift ->
    0 < d ->
    0 <= shift < 32 ->
    UINT_MOD / 2 <= Znth (dn - 1) l_dp 0 ->
    list_to_Z UINT_MOD l_np * 2 ^ shift <
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn - dn + 1).
Proof.
  intros l_np l_dp nn dn d shift Hdn Hdnle Hlen_np Hlen_dp Hbound_np
    Hbound_dp Hdp_val Hd_pos Hshift Htop.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_np Hbound_np) as Hnp_bound.
  rewrite Hlen_np in Hnp_bound.
  pose proof (list_to_Z_high_limb_quot_uint_for_div l_dp dn Hlen_dp ltac:(lia) Hbound_dp)
    as Hhigh.
  assert (Hden_pos: 0 < UINT_MOD ^ (dn - 1)).
  { apply Z.pow_pos_nonneg; unfold UINT_MOD; lia. }
  pose proof (Z.div_mod (list_to_Z UINT_MOD l_dp) (UINT_MOD ^ (dn - 1))
                ltac:(apply Z.pow_nonzero; unfold UINT_MOD; lia)) as Hdm.
  rewrite Hhigh in Hdm.
  pose proof (Z.mod_pos_bound (list_to_Z UINT_MOD l_dp) (UINT_MOD ^ (dn - 1))
                ltac:(apply Z.pow_pos_nonneg; unfold UINT_MOD; lia)) as Hmod.
  assert (Hdp_lower:
    (UINT_MOD / 2) * UINT_MOD ^ (dn - 1) <= list_to_Z UINT_MOD l_dp).
  {
    rewrite Hdm.
    assert (0 <= (list_to_Z UINT_MOD l_dp) mod UINT_MOD ^ (dn - 1)) by lia.
    nia.
  }
  assert (Hshift_le: 2 ^ shift <= UINT_MOD / 2).
  {
    replace (UINT_MOD / 2) with (2 ^ 31) by (unfold UINT_MOD; reflexivity).
    apply Z.pow_le_mono_r; lia.
  }
  assert (Hqpow_pos: 0 < UINT_MOD ^ (nn - dn + 1)).
  { apply Z.pow_pos_nonneg; unfold UINT_MOD; lia. }
  assert (Hrhs_lower:
    (UINT_MOD / 2) * UINT_MOD ^ (dn - 1) * UINT_MOD ^ (nn - dn + 1) <=
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn - dn + 1)).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  assert (Hpow_join:
    UINT_MOD ^ (dn - 1) * UINT_MOD ^ (nn - dn + 1) = UINT_MOD ^ nn).
  {
    rewrite <- Z.pow_add_r by lia.
    f_equal; lia.
  }
  assert (Hlhs_upper:
    list_to_Z UINT_MOD l_np * 2 ^ shift <
      UINT_MOD ^ nn * (UINT_MOD / 2)).
  {
    assert (Hpow_nn_pos: 0 < UINT_MOD ^ nn).
    { apply Z.pow_pos_nonneg; unfold UINT_MOD; lia. }
    assert (Hshift_nonneg: 0 <= 2 ^ shift).
    { apply Z.pow_nonneg; lia. }
    nia.
  }
  replace (UINT_MOD ^ nn * (UINT_MOD / 2))
    with ((UINT_MOD / 2) * UINT_MOD ^ (dn - 1) * UINT_MOD ^ (nn - dn + 1))
    in Hlhs_upper.
  - nia.
  - rewrite <- Hpow_join. ring.
Qed.

Lemma gmp_clz_mask8_zero_lt24:
  forall x,
    0 <= x < 2 ^ 32 ->
    Z.land x (Z.shiftl 255 (32 - 8)) = 0 ->
    x < 2 ^ 24.
Proof.
  intros x Hx Hland.
  destruct (Z_lt_ge_dec x (2 ^ 24)) as [Hlt | Hge]; [exact Hlt |].
  exfalso.
  assert (Hxpos: 0 < x) by lia.
  set (k := Z.log2 x).
  assert (Hk_low: 24 <= k).
  { subst k.
    apply (proj1 (Z.log2_le_pow2 x 24 Hxpos)).
    lia. }
  assert (Hk_high: k < 32).
  { subst k.
    apply (proj1 (Z.log2_lt_pow2 x 32 Hxpos)).
    lia. }
  assert (Hmaskbit: Z.testbit (Z.shiftl 255 (32 - 8)) k = true).
  { replace (32 - 8) with 24 by lia.
    rewrite Z.shiftl_spec_high by lia.
    change 255 with (Z.ones 8).
    apply Z.ones_spec_low.
    lia. }
  assert (Hzero: Z.testbit (Z.land x (Z.shiftl 255 (32 - 8))) k = false).
  { rewrite Hland.
    apply Z.testbit_0_l. }
  rewrite Z.land_spec in Hzero.
  rewrite Z.bit_log2 in Hzero by exact Hxpos.
  rewrite Hmaskbit in Hzero.
  discriminate.
Qed.

Lemma gmp_clz_mask8_step_bound:
  forall xpre x c,
    Z.land x (Z.shiftl 255 (32 - 8)) = 0 ->
    x = xpre * 2 ^ c ->
    c % 8 = 0 ->
    0 <= c -> c <= 24 ->
    0 < x -> x < 2 ^ 32 ->
    c + 8 <= 24.
Proof.
  intros xpre x c Hland Hx Hmod Hc0 Hc24 Hxpos Hx32.
  assert (Hlt24: x < 2 ^ 24).
  { apply gmp_clz_mask8_zero_lt24.
    - split; [lia | exact Hx32].
    - exact Hland. }
  assert (Hxpre_pos: 0 < xpre).
  { subst x.
    pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) ltac:(lia)).
    nia. }
  assert (Hc_lt24: c < 24).
  { destruct (Z_lt_ge_dec c 24) as [Hlt | Hge]; [exact Hlt |].
    exfalso.
    assert (Hpow: 2 ^ 24 <= 2 ^ c).
    { apply Z.pow_le_mono_r; lia. }
    subst x.
    assert (1 <= xpre) by lia.
    nia. }
  assert (Hmod_mod: c mod 8 = 0).
  { rewrite <- (Z.rem_mod_nonneg c 8) by lia.
    exact Hmod. }
  pose proof (Z.div_mod c 8 ltac:(lia)) as Hdivmod.
  rewrite Hmod_mod in Hdivmod.
  assert (Hdivlt: c / 8 < 3) by (apply Z.div_lt_upper_bound; lia).
  clear Hland Hx Hlt24 Hxpre_pos Hxpos Hx32 Hc24.
  remember (c / 8) as q.
  assert (Hqle: q <= 2).
  { lia. }
  rewrite Hdivmod.
  replace (8 * q + 0 + 8) with (8 * (q + 1)) by ring.
  replace 24 with (8 * 3) by ring.
  apply Z.mul_le_mono_nonneg_l.
  - lia.
  - lia.
Qed.

Lemma gmp_clz_shift8_step:
  forall xpre x c local,
    Z.land x (Z.shiftl 255 (32 - 8)) = 0 ->
    x = xpre * 2 ^ c ->
    c % 8 = 0 ->
    0 <= c -> c <= 24 ->
    0 < x -> x < 2 ^ 32 ->
    local = 8 ->
    unsigned_last_nbits (Z.shiftl x local) 32 = xpre * 2 ^ (c + 8) /\
    (c + 8) % 8 = 0 /\
    0 <= c + 8 /\
    c + 8 <= 24 /\
    0 < unsigned_last_nbits (Z.shiftl x local) 32 /\
    unsigned_last_nbits (Z.shiftl x local) 32 < 2 ^ 32.
Proof.
  intros xpre x c local Hland Hx Hmod Hc0 Hc24 Hxpos Hx32 Hlocal.
  assert (Hcstep: c + 8 <= 24).
  { apply (gmp_clz_mask8_step_bound xpre x c); assumption. }
  assert (Hlt24: x < 2 ^ 24).
  { apply gmp_clz_mask8_zero_lt24.
    - split; [lia | exact Hx32].
    - exact Hland. }
  assert (Hshift_range: 0 <= Z.shiftl x local < 2 ^ 32).
  { subst local.
    rewrite Z.shiftl_mul_pow2 by lia.
    split.
    - pose proof (Z.pow_pos_nonneg 2 8 ltac:(lia) ltac:(lia)). nia.
    - replace (2 ^ 32) with (2 ^ 24 * 2 ^ 8) by reflexivity.
      pose proof (Z.pow_pos_nonneg 2 8 ltac:(lia) ltac:(lia)).
      nia. }
  rewrite unsigned_last_nbits_eq by exact Hshift_range.
  subst local.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Hx.
  assert (Hpowadd: 2 ^ (c + 8) = 2 ^ c * 2 ^ 8).
  { rewrite Z.pow_add_r by lia. reflexivity. }
  repeat split; try nia.
  assert (Hmod_mod: c mod 8 = 0).
  { rewrite <- (Z.rem_mod_nonneg c 8) by lia.
    exact Hmod. }
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Z.add_mod by lia.
  rewrite Hmod_mod.
  reflexivity.
Qed.

Lemma gmp_clz_highbit_zero_lt31:
  forall x,
    0 <= x < 2 ^ 32 ->
    Z.land x (Z.shiftl 1 (32 - 1)) = 0 ->
    x < 2 ^ 31.
Proof.
  intros x Hx Hland.
  destruct (Z_lt_ge_dec x (2 ^ 31)) as [Hlt | Hge]; [exact Hlt |].
  exfalso.
  assert (Hxpos: 0 < x) by lia.
  set (k := Z.log2 x).
  assert (Hk_low: 31 <= k).
  { subst k.
    apply (proj1 (Z.log2_le_pow2 x 31 Hxpos)).
    lia. }
  assert (Hk_high: k < 32).
  { subst k.
    apply (proj1 (Z.log2_lt_pow2 x 32 Hxpos)).
    lia. }
  assert (Hk: k = 31) by lia.
  assert (Hmaskbit: Z.testbit (Z.shiftl 1 (32 - 1)) k = true).
  { replace (32 - 1) with 31 by lia.
    rewrite Hk.
    rewrite Z.shiftl_spec_high by lia.
    replace (31 - 31) with 0 by lia.
    change 1 with (Z.ones 1).
    apply Z.ones_spec_low.
    lia. }
  assert (Hzero: Z.testbit (Z.land x (Z.shiftl 1 (32 - 1))) k = false).
  { rewrite Hland.
    apply Z.testbit_0_l. }
  rewrite Z.land_spec in Hzero.
  subst k.
  rewrite Z.bit_log2 in Hzero by exact Hxpos.
  rewrite Hmaskbit in Hzero.
  discriminate.
Qed.

Lemma gmp_clz_highbit_nonzero_ge31:
  forall x,
    0 <= x < 2 ^ 32 ->
    Z.land x (Z.shiftl 1 (32 - 1)) <> 0 ->
    2 ^ 31 <= x.
Proof.
  intros x Hx Hland.
  destruct (Z_le_gt_dec (2 ^ 31) x) as [Hge | Hlt]; [exact Hge |].
  exfalso.
  apply Hland.
  apply Z.bits_inj_0.
  intros n.
  rewrite Z.land_spec.
  destruct (Z.eq_dec n 31) as [Heq | Hneq].
  - subst n.
    assert (Hxbit: Z.testbit x 31 = false).
    { apply (proj2 (Z.testbit_false x 31 ltac:(lia))).
      rewrite Z.div_small.
      - reflexivity.
      - split; lia. }
    rewrite Hxbit.
    reflexivity.
  - assert (Hmaskbit: Z.testbit (Z.shiftl 1 (32 - 1)) n = false).
    { replace (32 - 1) with 31 by lia.
      destruct (Z_lt_ge_dec n 31) as [Hnlt | Hnge].
      - rewrite Z.shiftl_spec_low by lia.
        reflexivity.
      - rewrite Z.shiftl_spec_high by lia.
        change 1 with (Z.ones 1).
        apply Z.ones_spec_high.
        lia. }
    rewrite Hmaskbit.
    destruct (Z.testbit x n); reflexivity.
Qed.

Lemma gmp_clz_shift1_step:
  forall xpre x c local,
    Z.land x (Z.shiftl 1 (32 - 1)) = 0 ->
    x = xpre * 2 ^ c ->
    0 <= c -> c <= 31 ->
    0 < x -> x < 2 ^ 32 ->
    local = 8 ->
    unsigned_last_nbits (Z.shiftl x 1) 32 = xpre * 2 ^ (c + 1) /\
    0 <= c + 1 /\
    c + 1 <= 31 /\
    0 < unsigned_last_nbits (Z.shiftl x 1) 32 /\
    unsigned_last_nbits (Z.shiftl x 1) 32 < 2 ^ 32.
Proof.
  intros xpre x c local Hland Hx Hc0 Hc31 Hxpos Hx32 Hlocal.
  assert (Hlt31: x < 2 ^ 31).
  { apply gmp_clz_highbit_zero_lt31.
    - split; [lia | exact Hx32].
    - exact Hland. }
  assert (Hxpre_pos: 0 < xpre).
  { subst x.
    pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) ltac:(lia)).
    nia. }
  assert (Hcstep: c + 1 <= 31).
  { assert (Hc_lt31: c < 31).
    { destruct (Z_lt_ge_dec c 31) as [Hlt | Hge]; [exact Hlt |].
      exfalso.
      assert (Hpow: 2 ^ 31 <= 2 ^ c).
      { apply Z.pow_le_mono_r; lia. }
      subst x.
      assert (1 <= xpre) by lia.
      nia. }
    lia. }
  assert (Hshift_range: 0 <= Z.shiftl x 1 < 2 ^ 32).
  { rewrite Z.shiftl_mul_pow2 by lia.
    split.
    - pose proof (Z.pow_pos_nonneg 2 1 ltac:(lia) ltac:(lia)). nia.
    - replace (2 ^ 32) with (2 ^ 31 * 2 ^ 1) by reflexivity.
      pose proof (Z.pow_pos_nonneg 2 1 ltac:(lia) ltac:(lia)).
      nia. }
  rewrite unsigned_last_nbits_eq by exact Hshift_range.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Hx.
  assert (Hpowadd: 2 ^ (c + 1) = 2 ^ c * 2 ^ 1).
  { rewrite Z.pow_add_r by lia. reflexivity. }
  repeat split; try nia.
Qed.

Lemma mpn_invert_u1_range:
  forall u,
    UINT_MOD ÷ 2 <= u -> u <= 4294967295 ->
    0 <= u < 4294967296.
Proof.
  intros.
  change (UINT_MOD ÷ 2) with 2147483648 in H.
  lia.
Qed.

Lemma mpn_invert_u1_high_nonzero:
  forall u,
    UINT_MOD ÷ 2 <= u -> u <= 4294967295 ->
    Z.shiftr u 16 <> 0.
Proof.
  intros u Hlo Hhi.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 16) with 65536.
  change (UINT_MOD ÷ 2) with 2147483648 in Hlo.
  assert (0 < u / 65536) by (apply Z.div_str_pos; lia).
  lia.
Qed.

Lemma udiv_preinv_e_bounds:
  forall d di,
    2147483648 <= d -> d <= 4294967295 ->
    0 <= di -> di <= 4294967295 ->
    (di + 4294967296) * (4294967296 * d) <=
      4294967296 ^ 3 - 1 ->
    4294967296 ^ 3 - 1 <
      (di + 4294967296 + 1) * (4294967296 * d) ->
    1 <= 4294967296 ^ 2 - (di + 4294967296) * d <= d.
Proof.
  intros d di Hdlo Hdhi Hdipos Hdihi Hlo Hhi.
  assert (Hmd_lt: (di + 4294967296) * d < 4294967296 ^ 2).
  { apply (Zmult_lt_reg_r _ _ 4294967296); [lia|].
    replace (((di + 4294967296) * d) * 4294967296)
      with ((di + 4294967296) * (4294967296 * d)) by ring.
    replace ((4294967296 ^ 2) * 4294967296)
      with (4294967296 ^ 3) by reflexivity.
    lia. }
  assert (Hmd_ge: 4294967296 ^ 2 <= (di + 4294967296 + 1) * d).
  { apply (proj2 (Z.mul_le_mono_pos_r _ _ 4294967296 ltac:(lia))).
    replace ((4294967296 ^ 2) * 4294967296)
      with (4294967296 ^ 3) by reflexivity.
    replace (((di + 4294967296 + 1) * d) * 4294967296)
      with ((di + 4294967296 + 1) * (4294967296 * d)) by ring.
    lia. }
  nia.
Qed.

Lemma udiv_3by2_preinv_e_bounds:
  forall d1 d0 di,
    2147483648 <= d1 -> d1 <= 4294967295 ->
    0 <= d0 -> d0 <= 4294967295 ->
    0 <= di -> di <= 4294967295 ->
    (di + 4294967296) * (4294967296 * d1 + d0) <=
      4294967296 ^ 3 - 1 ->
    4294967296 ^ 3 - 1 <
      (di + 4294967296 + 1) * (4294967296 * d1 + d0) ->
    1 <= 4294967296 ^ 3 -
      (di + 4294967296) * (4294967296 * d1 + d0) <=
      4294967296 * d1 + d0.
Proof.
  intros d1 d0 di Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hlo Hhi.
  nia.
Qed.

Lemma udiv_3by2_preinv_error_range:
  forall d1 d0 di n2 n1 n0 w0 w1 qlo c,
    2147483648 <= d1 -> d1 <= 4294967295 ->
    0 <= d0 -> d0 <= 4294967295 ->
    0 <= di -> di <= 4294967295 ->
    0 <= n2 -> n2 <= 4294967295 ->
    0 <= n1 -> n1 <= 4294967295 ->
    0 <= n0 -> n0 <= 4294967295 ->
    n2 * 4294967296 + n1 < d1 * 4294967296 + d0 ->
    0 <= w0 -> w0 <= 4294967295 ->
    0 <= w1 -> w1 <= 4294967295 ->
    0 <= qlo -> qlo < 4294967296 ->
    (c = 0 \/ c = 1) ->
    w0 + n1 = c * 4294967296 + qlo ->
    w1 * 4294967296 + w0 = n2 * di ->
    (di + 4294967296) * (4294967296 * d1 + d0) <=
      4294967296 ^ 3 - 1 ->
    4294967296 ^ 3 - 1 <
      (di + 4294967296 + 1) * (4294967296 * d1 + d0) ->
    -(4294967296 ^ 2) <
      n2 * 4294967296 ^ 2 + n1 * 4294967296 + n0 -
        (w1 + n2 + c + 1) * (d1 * 4294967296 + d0) <
      4294967296 ^ 2.
Proof.
  intros d1 d0 di n2 n1 n0 w0 w1 qlo c
    Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn20 Hn2hi Hn10 Hn1hi
    Hn00 Hn0hi Hnd Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Hc Hcarry
    Hmul Hinvlo Hinvhi.
  set (B := 4294967296).
  set (D := B * d1 + d0).
  set (E := B ^ 3 - (di + B) * D).
  assert (HBpos: 0 < B) by (subst B; lia).
  assert (HDpos: 0 < D) by (subst D B; nia).
  assert (HDlt: D < B ^ 2) by (subst D B; nia).
  assert (HDlo: B ^ 2 <= 2 * D).
  { subst D B. change (4294967296 ^ 2) with 18446744073709551616.
    nia. }
  assert (HE: 1 <= E <= D).
  { subst E D B. eapply udiv_3by2_preinv_e_bounds; eauto. }
  assert (Hn1: n1 = c * B + qlo - w0) by (subst B; lia).
  assert (Hw1B: w1 * B = n2 * di - w0) by (subst B; lia).
  assert (HdiD: di * D = B ^ 3 - B * D - E) by (subst E; ring).
  assert (Hformula:
    B *
      (n2 * B ^ 2 + n1 * B + n0 -
       (w1 + n2 + c + 1) * D) =
    qlo * B ^ 2 + n0 * B + n2 * E +
    w0 * D - w0 * B ^ 2 + c * B ^ 3 - (c + 1) * D * B).
  { replace (B * (n2 * B ^ 2 + n1 * B + n0 -
                    (w1 + n2 + c + 1) * D))
      with (n2 * B ^ 3 + n1 * B ^ 2 + n0 * B -
            (w1 * B + n2 * B + c * B + B) * D) by ring.
    rewrite Hw1B, Hn1.
    replace (n2 * B ^ 3 + (c * B + qlo - w0) * B ^ 2 +
               n0 * B - (n2 * di - w0 + n2 * B + c * B + B) * D)
      with (qlo * B ^ 2 + n0 * B + w0 * D - w0 * B ^ 2 +
            c * B ^ 3 - (c + 1) * D * B +
            n2 * (B ^ 3 - B * D - di * D)) by ring.
    rewrite HdiD.
    nia. }
  destruct Hc as [Hc | Hc]; subst c; split.
  - apply (Zmult_lt_reg_r _ _ B); [exact HBpos |].
    replace ((n2 * B ^ 2 + n1 * B + n0 -
              (w1 + n2 + 0 + 1) * (d1 * B + d0)) * B)
      with (B * (n2 * B ^ 2 + n1 * B + n0 -
                  (w1 + n2 + 0 + 1) * D)) by (subst D; ring).
    rewrite Hformula.
    replace (qlo * B ^ 2 + n0 * B + n2 * E + w0 * D -
               w0 * B ^ 2 + 0 * B ^ 3 - (0 + 1) * D * B)
      with (n1 * B ^ 2 + n0 * B + n2 * E + w0 * D - D * B)
      by (rewrite Hn1; ring).
    nia.
  - apply (Zmult_lt_reg_r _ _ B); [exact HBpos |].
    replace ((n2 * B ^ 2 + n1 * B + n0 -
              (w1 + n2 + 0 + 1) * (d1 * B + d0)) * B)
      with (B * (n2 * B ^ 2 + n1 * B + n0 -
                  (w1 + n2 + 0 + 1) * D)) by (subst D; ring).
    rewrite Hformula.
    assert (Hn2E: n2 * E < B * D) by nia.
    assert (Hw0D: w0 * D - w0 * B ^ 2 <= 0) by nia.
    assert (Hhead: qlo * B ^ 2 + n0 * B < B ^ 3) by nia.
    assert (Htail_lt_bd : n2 * E + (w0 * D - w0 * B ^ 2) < B * D).
    {
      eapply Z.le_lt_trans; [| exact Hn2E].
      lia.
    }
    assert (Htail: n2 * E + (w0 * D - w0 * B ^ 2) - D * B < 0).
    {
      replace (D * B) with (B * D) by ring.
      lia.
    }
    replace (qlo * B ^ 2 + n0 * B + n2 * E + w0 * D -
               w0 * B ^ 2 + 0 * B ^ 3 - (0 + 1) * D * B)
      with ((qlo * B ^ 2 + n0 * B) +
            (n2 * E + (w0 * D - w0 * B ^ 2) - D * B)) by ring.
    replace (B ^ 2 * B) with (B ^ 3 + 0) by ring.
    apply Z.add_lt_mono; assumption.
  - apply (Zmult_lt_reg_r _ _ B); [exact HBpos |].
    replace ((n2 * B ^ 2 + n1 * B + n0 -
              (w1 + n2 + 1 + 1) * (d1 * B + d0)) * B)
      with (B * (n2 * B ^ 2 + n1 * B + n0 -
                  (w1 + n2 + 1 + 1) * D)) by (subst D; ring).
    rewrite Hformula.
    replace (qlo * B ^ 2 + n0 * B + n2 * E + w0 * D -
               w0 * B ^ 2 + 1 * B ^ 3 - (1 + 1) * D * B)
      with (n1 * B ^ 2 + n0 * B + n2 * E + w0 * D - 2 * D * B)
      by (rewrite Hn1; ring).
    assert (Hn1lo: B - w0 <= n1) by (rewrite Hn1; lia).
    assert (Hlower:
      -(B ^ 2 * B) <
      n1 * B ^ 2 + n0 * B + n2 * E + w0 * D - 2 * D * B).
    { assert (Hbase: (B - w0) * B ^ 2 + w0 * D - 2 * D * B >
                     -(B ^ 2 * B)).
      { assert (Hpos:
          0 < (2 * B - w0) * (B ^ 2 - D)).
        { apply Z.mul_pos_pos; nia. }
        replace ((B - w0) * B ^ 2 + w0 * D - 2 * D * B + B ^ 2 * B)
          with ((2 * B - w0) * (B ^ 2 - D)) by ring.
        lia. }
      assert ((B - w0) * B ^ 2 <= n1 * B ^ 2).
      { apply Z.mul_le_mono_nonneg_r; nia. }
      assert (0 <= n0 * B + n2 * E) by nia.
      nia. }
    nia.
  - apply (Zmult_lt_reg_r _ _ B); [exact HBpos |].
    replace ((n2 * B ^ 2 + n1 * B + n0 -
              (w1 + n2 + 1 + 1) * (d1 * B + d0)) * B)
      with (B * (n2 * B ^ 2 + n1 * B + n0 -
                  (w1 + n2 + 1 + 1) * D)) by (subst D; ring).
    rewrite Hformula.
    replace (qlo * B ^ 2 + n0 * B + n2 * E + w0 * D -
               w0 * B ^ 2 + 1 * B ^ 3 - (1 + 1) * D * B)
      with (n1 * B ^ 2 + n0 * B + n2 * E + w0 * D - 2 * D * B)
      by (rewrite Hn1; ring).
    assert (Htail: n2 * E + w0 * D - 2 * D * B < 0) by nia.
    assert (Hhead: n1 * B ^ 2 + n0 * B < B ^ 3) by nia.
    nia.
Qed.

Lemma udiv_3by2_qhat_no_overflow:
  forall d1 d0 di n2 n1 n0 w0 w1 qlo c,
    2147483648 <= d1 -> d1 <= 4294967295 ->
    0 <= d0 -> d0 <= 4294967295 ->
    0 <= di -> di <= 4294967295 ->
    0 <= n2 -> n2 <= 4294967295 ->
    0 <= n1 -> n1 <= 4294967295 ->
    0 <= n0 -> n0 <= 4294967295 ->
    n2 * 4294967296 + n1 < d1 * 4294967296 + d0 ->
    0 <= w0 -> w0 <= 4294967295 ->
    0 <= w1 -> w1 <= 4294967295 ->
    0 <= qlo -> qlo < 4294967296 ->
    (c = 0 \/ c = 1) ->
    w0 + n1 = c * 4294967296 + qlo ->
    w1 * 4294967296 + w0 = n2 * di ->
    (di + 4294967296) * (4294967296 * d1 + d0) <=
      4294967296 ^ 3 - 1 ->
    4294967296 ^ 3 - 1 <
      (di + 4294967296 + 1) * (4294967296 * d1 + d0) ->
    w1 + n2 + c < 4294967296.
Proof.
  intros.
  nia.
Qed.

Lemma udiv_3by2_error_qlo_lower:
  forall d1 d0 di n2 n1 n0 w0 w1 qlo c,
    2147483648 <= d1 -> d1 <= 4294967295 ->
    0 <= d0 -> d0 <= 4294967295 ->
    0 <= di -> di <= 4294967295 ->
    0 <= n2 -> n2 <= 4294967295 ->
    0 <= n1 -> n1 <= 4294967295 ->
    0 <= n0 -> n0 <= 4294967295 ->
    n2 * 4294967296 + n1 < d1 * 4294967296 + d0 ->
    0 <= w0 -> w0 <= 4294967295 ->
    0 <= w1 -> w1 <= 4294967295 ->
    0 <= qlo -> qlo < 4294967296 ->
    (c = 0 \/ c = 1) ->
    w0 + n1 = c * 4294967296 + qlo ->
    w1 * 4294967296 + w0 = n2 * di ->
    (di + 4294967296) * (4294967296 * d1 + d0) <=
      4294967296 ^ 3 - 1 ->
    4294967296 ^ 3 - 1 <
      (di + 4294967296 + 1) * (4294967296 * d1 + d0) ->
    (qlo - 4294967296) * 4294967296 <=
      n2 * 4294967296 ^ 2 + n1 * 4294967296 + n0 -
        (w1 + n2 + c + 1) * (d1 * 4294967296 + d0).
Proof.
  intros d1 d0 di n2 n1 n0 w0 w1 qlo c
    Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn20 Hn2hi Hn10 Hn1hi Hn00 Hn0hi
    Hnd Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Hc Hcarry Hmul Hinvlo Hinvhi.
  set (B := 4294967296).
  set (D := B * d1 + d0).
  set (E := B ^ 3 - (di + B) * D).
  assert (HBpos: 0 < B) by (subst B; lia).
  assert (HDlt: D < B ^ 2) by (subst D B; nia).
  assert (HE: 1 <= E <= D).
  { subst E D B. eapply udiv_3by2_preinv_e_bounds; eauto. }
  assert (Hn1: n1 = c * B + qlo - w0) by (subst B; lia).
  assert (Hw1B: w1 * B = n2 * di - w0) by (subst B; lia).
  assert (HdiD: di * D = B ^ 3 - B * D - E) by (subst E; ring).
  assert (Hformula:
    B *
      (n2 * B ^ 2 + n1 * B + n0 -
       (w1 + n2 + c + 1) * D) =
    qlo * B ^ 2 + n0 * B + n2 * E +
    w0 * D - w0 * B ^ 2 + c * B ^ 3 - (c + 1) * D * B).
  { replace (B * (n2 * B ^ 2 + n1 * B + n0 -
                    (w1 + n2 + c + 1) * D))
      with (n2 * B ^ 3 + n1 * B ^ 2 + n0 * B -
            (w1 * B + n2 * B + c * B + B) * D) by ring.
    rewrite Hw1B, Hn1.
    replace (n2 * B ^ 3 + (c * B + qlo - w0) * B ^ 2 +
               n0 * B - (n2 * di - w0 + n2 * B + c * B + B) * D)
      with (qlo * B ^ 2 + n0 * B + w0 * D - w0 * B ^ 2 +
            c * B ^ 3 - (c + 1) * D * B +
            n2 * (B ^ 3 - B * D - di * D)) by ring.
    rewrite HdiD.
    nia. }
  apply (Zmult_le_reg_r _ _ B); [lia |].
  replace (d1 * B + d0) with D by (subst D; ring).
  replace ((qlo - B) * B * B) with ((qlo - B) * B ^ 2) by ring.
  replace ((n2 * B ^ 2 + n1 * B + n0 - (w1 + n2 + c + 1) * D) * B)
    with (B * (n2 * B ^ 2 + n1 * B + n0 - (w1 + n2 + c + 1) * D)) by ring.
  rewrite Hformula.
  destruct Hc as [Hc | Hc]; subst c.
  - replace (qlo * B ^ 2 + n0 * B + n2 * E + w0 * D -
               w0 * B ^ 2 + 0 * B ^ 3 - (0 + 1) * D * B -
               (qlo - B) * B ^ 2)
      with (n0 * B + n2 * E + (B - w0) * (B ^ 2 - D)) by ring.
    assert (0 <= (B - w0) * (B ^ 2 - D)).
    {
      assert (0 <= B - w0) by lia.
      assert (0 <= B ^ 2 - D) by lia.
      apply Z.mul_nonneg_nonneg; assumption.
    }
    nia.
  - replace (qlo * B ^ 2 + n0 * B + n2 * E + w0 * D -
               w0 * B ^ 2 + 1 * B ^ 3 - (1 + 1) * D * B -
               (qlo - B) * B ^ 2)
      with (n0 * B + n2 * E + (2 * B - w0) * (B ^ 2 - D)) by ring.
    assert (0 <= (2 * B - w0) * (B ^ 2 - D)).
    {
      assert (0 <= 2 * B - w0) by lia.
      assert (0 <= B ^ 2 - D) by lia.
      apply Z.mul_nonneg_nonneg; assumption.
    }
    nia.
Qed.

Lemma udiv_3by2_raw_base_eq:
  forall d1 d0 n2 n1 n0 qhat t0 t1 raw rlo b0 b1,
    t1 * 4294967296 + t0 = d0 * qhat ->
    raw = n1 - d1 * qhat - d1 - b0 - t1 - b1 + n2 * 4294967296 ->
    rlo = n0 - d0 + b0 * 4294967296 - t0 + b1 * 4294967296 ->
    n2 * 4294967296 ^ 2 + n1 * 4294967296 + n0 =
      (qhat + 1) * (d1 * 4294967296 + d0) + raw * 4294967296 + rlo.
Proof.
  intros.
  subst raw rlo.
  nia.
Qed.

Lemma udiv_3by2_raw_high_between:
  forall d1 d0 di n2 n1 n0 w0 w1 qlo qhat t0 t1 c b0 b1,
    2147483648 <= d1 -> d1 <= 4294967295 ->
    0 <= d0 -> d0 <= 4294967295 ->
    0 <= di -> di <= 4294967295 ->
    0 <= n2 -> n2 <= 4294967295 ->
    0 <= n1 -> n1 <= 4294967295 ->
    0 <= n0 -> n0 <= 4294967295 ->
    n2 * 4294967296 + n1 < d1 * 4294967296 + d0 ->
    0 <= w0 -> w0 <= 4294967295 ->
    0 <= w1 -> w1 <= 4294967295 ->
    0 <= qlo -> qlo < 4294967296 ->
    0 <= t0 -> t0 <= 4294967295 ->
    0 <= t1 -> t1 <= 4294967295 ->
    (c = 0 \/ c = 1) ->
    (b0 = 0 \/ b0 = 1) ->
    (b1 = 0 \/ b1 = 1) ->
    w0 + n1 = c * 4294967296 + qlo ->
    w1 * 4294967296 + w0 = n2 * di ->
    qhat = w1 + n2 + c ->
    t1 * 4294967296 + t0 = d0 * qhat ->
    0 <= n0 - d0 + b0 * 4294967296 < 4294967296 ->
    0 <= n0 - d0 + b0 * 4294967296 - t0 + b1 * 4294967296 < 4294967296 ->
    (di + 4294967296) * (4294967296 * d1 + d0) <=
      4294967296 ^ 3 - 1 ->
    4294967296 ^ 3 - 1 <
      (di + 4294967296 + 1) * (4294967296 * d1 + d0) ->
    qlo - 4294967296 <=
      n1 - d1 * qhat - d1 - b0 - t1 - b1 + n2 * 4294967296 <
      4294967296.
Proof.
  intros d1 d0 di n2 n1 n0 w0 w1 qlo qhat t0 t1 c b0 b1
    Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn20 Hn2hi Hn10 Hn1hi
    Hn00 Hn0hi Hnd Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Ht00 Ht0hi Ht10 Ht1hi
    Hc Hb0 Hb1 Hcarry Hmul Hqhat Hprod Hlo0 Hlo1 Hinvlo Hinvhi.
  set (B := 4294967296).
  set (D := d1 * B + d0).
  set (raw := n1 - d1 * qhat - d1 - b0 - t1 - b1 + n2 * B).
  set (rlo := n0 - d0 + b0 * B - t0 + b1 * B).
  assert (HBpos: 0 < B) by (subst B; lia).
  assert (Hrlo_bounds: 0 <= rlo < B) by (subst rlo B; exact Hlo1).
  assert (Herr_eq:
    n2 * B ^ 2 + n1 * B + n0 - (w1 + n2 + c + 1) * D =
    raw * B + rlo).
  { subst D B raw rlo.
    rewrite Hqhat.
    rewrite Hqhat in Hprod.
    replace ((w1 + n2 + c) * d0) with (t1 * 4294967296 + t0)
      by (replace ((w1 + n2 + c) * d0) with (d0 * (w1 + n2 + c)) by ring;
          rewrite <- Hprod; ring).
    nia. }
  pose proof (udiv_3by2_error_qlo_lower d1 d0 di n2 n1 n0 w0 w1 qlo c
    Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn20 Hn2hi Hn10 Hn1hi Hn00 Hn0hi Hnd
    Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Hc Hcarry Hmul Hinvlo Hinvhi) as Hlower_err.
  pose proof (udiv_3by2_preinv_error_range d1 d0 di n2 n1 n0 w0 w1 qlo c
    Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn20 Hn2hi Hn10 Hn1hi Hn00 Hn0hi Hnd
    Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Hc Hcarry Hmul Hinvlo Hinvhi) as Herr_range.
  change 4294967296 with B in Hlower_err.
  change 4294967296 with B in Herr_range.
  change 4294967296 with B.
  replace (d1 * B + d0) with D in Hlower_err by (subst D; ring).
  replace (d1 * B + d0) with D in Herr_range by (subst D; ring).
  rewrite Herr_eq in Hlower_err, Herr_range.
  split.
  - destruct (Z_lt_ge_dec raw (qlo - B)) as [Hlt | Hge].
    + assert (raw <= qlo - B - 1) by lia.
      assert (raw * B + rlo < (qlo - B) * B).
      { assert (raw * B <= (qlo - B - 1) * B).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        assert (rlo <= B - 1) by lia.
        replace ((qlo - B - 1) * B + (B - 1))
          with ((qlo - B) * B - 1) by ring.
        lia. }
      lia.
    + lia.
  - destruct (Z_lt_ge_dec raw B) as [Hlt | Hge].
    + exact Hlt.
    + destruct Herr_range as [_ Herr_hi].
      assert (B ^ 2 <= raw * B + rlo).
      { assert (HrawB: B * B <= raw * B).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        replace (B * B) with (B ^ 2) in HrawB by ring.
        lia. }
      lia.
Qed.

Lemma udiv_3by2_qhat_remainder_nonneg:
  forall d1 d0 di n2 n1 n0 w0 w1 qlo c,
    2147483648 <= d1 -> d1 <= 4294967295 ->
    0 <= d0 -> d0 <= 4294967295 ->
    0 <= di -> di <= 4294967295 ->
    0 <= n2 -> n2 <= 4294967295 ->
    0 <= n1 -> n1 <= 4294967295 ->
    0 <= n0 -> n0 <= 4294967295 ->
    n2 * 4294967296 + n1 < d1 * 4294967296 + d0 ->
    0 <= w0 -> w0 <= 4294967295 ->
    0 <= w1 -> w1 <= 4294967295 ->
    0 <= qlo -> qlo < 4294967296 ->
    (c = 0 \/ c = 1) ->
    w0 + n1 = c * 4294967296 + qlo ->
    w1 * 4294967296 + w0 = n2 * di ->
    (di + 4294967296) * (4294967296 * d1 + d0) <=
      4294967296 ^ 3 - 1 ->
    4294967296 ^ 3 - 1 <
      (di + 4294967296 + 1) * (4294967296 * d1 + d0) ->
    0 <= n2 * 4294967296 ^ 2 + n1 * 4294967296 + n0 -
         (w1 + n2 + c) * (d1 * 4294967296 + d0).
Proof.
  intros d1 d0 di n2 n1 n0 w0 w1 qlo c
    Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn20 Hn2hi Hn10 Hn1hi Hn00 Hn0hi Hnd
    Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Hc Hcarry Hmul Hinvlo Hinvhi.
  set (B := 4294967296).
  set (D := B * d1 + d0).
  set (E := B ^ 3 - (di + B) * D).
  assert (HE: 1 <= E <= D) by
    (subst E D B; eapply udiv_3by2_preinv_e_bounds; eauto).
  assert (Hn1: n1 = c * B + qlo - w0) by (subst B; lia).
  assert (Hw1B: w1 * B = n2 * di - w0) by (subst B; lia).
  assert (HdiD: di * D = B ^ 3 - B * D - E) by (subst E; ring).
  assert (Hformula:
    B * (n2 * B ^ 2 + n1 * B + n0 - (w1 + n2 + c) * D) =
    qlo * B ^ 2 + n0 * B + n2 * E + w0 * D - w0 * B ^ 2 +
    c * B ^ 3 - c * D * B).
  { replace (B * (n2 * B ^ 2 + n1 * B + n0 - (w1 + n2 + c) * D))
      with (n2 * B ^ 3 + n1 * B ^ 2 + n0 * B -
            (w1 * B + n2 * B + c * B) * D) by ring.
    rewrite Hw1B, Hn1.
    replace (n2 * B ^ 3 + (c * B + qlo - w0) * B ^ 2 + n0 * B -
             (n2 * di - w0 + n2 * B + c * B) * D)
      with (qlo * B ^ 2 + n0 * B + w0 * D - w0 * B ^ 2 +
            c * B ^ 3 - c * D * B +
            n2 * (B ^ 3 - B * D - di * D)) by ring.
    rewrite HdiD; ring. }
  destruct Hc as [Hc | Hc]; subst c.
  - enough (0 <= B * (n2 * B ^ 2 + n1 * B + n0 - (w1 + n2 + 0) * D)) by nia.
    rewrite Hformula; nia.
  - enough (0 <= B * (n2 * B ^ 2 + n1 * B + n0 - (w1 + n2 + 1) * D)) by nia.
    rewrite Hformula; nia.
Qed.

Lemma udiv_3by2_raw_ge_coeff_k_gt1_bound:
  forall d1 d0 di w0 w1 c K,
    2147483648 <= d1 -> d1 < 4294967296 ->
    0 <= d0 -> d0 < 4294967296 ->
    0 <= di -> 0 <= w0 -> w0 < 4294967296 -> 0 <= w1 ->
    (c = 0 \/ c = 1) ->
    w1 * 4294967296 + w0 = d1 * di ->
    K = 4294967296 - (w1 + d1 + c) ->
    K >= 2 ->
    d0 * (di - K + 1) + 4294967296 * K <
      K * (4294967296 ^ 2 - (4294967296 * d1 + d0)).
Proof.
  intros d1 d0 di w0 w1 c K Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hw0lo Hw0hi Hw1lo Hc Hmul HK HKge.
  set (B := 4294967296).
  assert (Hdi_succ: di + 1 <= 2 * (w1 + 1)).
  { assert (Hprod_lt: d1 * di < (w1 + 1) * B).
    { rewrite <- Hmul. nia. }
    assert (HB_le_2d1: B <= 2 * d1) by (subst B; lia).
    assert ((w1 + 1) * B <= (w1 + 1) * (2 * d1)).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    assert (d1 * di < d1 * (2 * (w1 + 1))) by nia.
    nia. }
  assert (HKA: K * (B - d1 - 1) >= 2 * (w1 + 1)).
  { destruct Hc as [Hc | Hc]; subst c; subst K; nia. }
  assert (Hmain: d0 * (di + 1) < B * (K * (B - d1 - 1))).
  { assert (0 < di + 1) by lia.
    assert (d0 * (di + 1) < B * (di + 1)).
    { apply Z.mul_lt_mono_pos_r; lia. }
    assert (B * (di + 1) <= B * (2 * (w1 + 1))).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    assert (B * (2 * (w1 + 1)) <= B * (K * (B - d1 - 1))).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    lia. }
  enough (d0 * (di - K + 1) + B * K < K * (B ^ 2 - (B * d1 + d0))) by (subst B; exact H).
  replace (K * (B ^ 2 - (B * d1 + d0)) - (d0 * (di - K + 1) + B * K))
    with (B * (K * (B - d1 - 1)) - d0 * (di + 1)) by ring.
  lia.
Qed.

Lemma udiv_3by2_raw_ge_coeff_boundary:
  forall d1 d0 di n1 w0 w1 qlo t0 t1 c b0 b1,
    2147483648 <= d1 -> d1 < 4294967296 ->
    0 <= d0 -> d0 < 4294967296 ->
    0 <= di -> di < 4294967296 ->
    0 <= n1 -> n1 < 4294967296 -> n1 < d0 ->
    0 <= w0 -> w0 < 4294967296 ->
    0 <= w1 -> w1 < 4294967296 ->
    0 <= qlo -> qlo < 4294967296 ->
    0 <= t0 -> t0 < 4294967296 ->
    0 <= t1 -> t1 < 4294967296 ->
    (c = 0 \/ c = 1) ->
    (b0 = 0 \/ b0 = 1) ->
    (b1 = 0 \/ b1 = 1) ->
    w0 + n1 = c * 4294967296 + qlo ->
    w1 * 4294967296 + w0 = d1 * di ->
    t1 * 4294967296 + t0 = d0 * (w1 + d1 + c) ->
    1 <= 4294967296 ^ 3 - (di + 4294967296) * (4294967296 * d1 + d0) ->
    4294967296 ^ 3 - (di + 4294967296) * (4294967296 * d1 + d0) <= 4294967296 * d1 + d0 ->
    n1 - d1 * (w1 + d1 + c) - d1 - b0 - t1 - b1 + d1 * 4294967296 >= qlo ->
    n1 - d1 * (w1 + d1 + c) - t1 + d1 * 4294967296 <= 4294967296.
Proof.
  intros d1 d0 di n1 w0 w1 qlo t0 t1 c b0 b1
    Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn10 Hn1hi Hn1d0
    Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Ht00 Ht0hi Ht10 Ht1hi
    Hc Hb0 Hb1 Hcarry Hmul Hprod HElo HEhi Hrawge.
  set (B := 4294967296).
  set (K := B - (w1 + d1 + c)).
  assert (HqhatK: w1 + d1 + c = B - K) by (subst K; ring).
  assert (HprodK: t1 * B + t0 = d0 * (B - K)).
  { rewrite <- HqhatK. exact Hprod. }
  assert (HEK: K * B ^ 2 =
      (B ^ 3 - (di + B) * (B * d1 + d0)) + d0 * (di + B) - c * B ^ 2 + w0 * B).
  { change 4294967296 with B in Hmul.
    subst K B.
    change (4294967296 ^ 2) with (4294967296 * 4294967296).
    change (4294967296 ^ 3) with (4294967296 * 4294967296 * 4294967296).
    replace ((di + 4294967296) * (4294967296 * d1 + d0))
      with (4294967296 * (d1 * di) + 4294967296 * 4294967296 * d1 +
            d0 * di + d0 * 4294967296) by ring.
    rewrite <- Hmul.
    ring. }
  assert (HrawK: 0 <= d1 * (K - 1) + c * B - w0 - t1 - b0 - b1).
  { replace (d1 * (K - 1) + c * B - w0 - t1 - b0 - b1)
      with (n1 - d1 * (w1 + d1 + c) - d1 - b0 - t1 - b1 + d1 * B - qlo).
    - lia.
    - change 4294967296 with B in Hcarry.
      subst K.
      replace qlo with (w0 + n1 - c * B) by lia.
      ring. }
  set (Ecur := B ^ 3 - (di + B) * (B * d1 + d0)) in HElo, HEhi, HEK.
  assert (HKge1: 1 <= K).
  { destruct (Z_le_gt_dec 1 K) as [Hle | Hlt]; [exact Hle |].
    assert (HKle0: K <= 0) by lia.
    destruct Hc as [Hc0 | Hc1]; subst c.
    - assert (K * B ^ 2 <= 0).
      { apply Z.mul_nonpos_nonneg; [lia | apply Z.pow_nonneg; lia]. }
      assert (0 <= d0 * (di + B)).
      { apply Z.mul_nonneg_nonneg; lia. }
      assert (0 <= w0 * B).
      { apply Z.mul_nonneg_nonneg; lia. }
      lia.
    - assert (K * B ^ 2 <= 0).
      { apply Z.mul_nonpos_nonneg; [lia | apply Z.pow_nonneg; lia]. }
      assert (B < w0 + d0) by lia.
      assert (B ^ 2 < (w0 + d0) * B).
      { replace (B ^ 2) with (B * B) by ring.
        apply Z.mul_lt_mono_pos_r; lia. }
      assert (0 <= d0 * di).
      { apply Z.mul_nonneg_nonneg; lia. }
      replace (d0 * (di + B) - B ^ 2 + w0 * B)
        with (d0 * di + ((w0 + d0) * B - B ^ 2)) in HEK by ring.
      lia. }
  assert (HKle1: K <= 1).
  { destruct (Z_le_gt_dec K 1) as [Hle | Hgt]; [exact Hle |].
    assert (HKge2: K >= 2) by lia.
    assert (Hupper: K * (B * B - (B * d1 + d0)) <= d0 * (di + 1) + t0 - (b0 + b1) * B).
    { assert (HrawKB:
        0 <= K * (B * d1 + d0) - d1 * B - d0 * B +
             c * (B * B) - w0 * B + t0 - (b0 + b1) * B).
      { assert (0 <= B * (d1 * (K - 1) + c * B - w0 - t1 - b0 - b1)).
        { apply Z.mul_nonneg_nonneg; lia. }
        replace (K * (B * d1 + d0) - d1 * B - d0 * B +
                 c * (B * B) - w0 * B + t0 - (b0 + b1) * B)
          with (B * (d1 * (K - 1) + c * B - w0 - t1 - b0 - b1)).
        - exact H.
        - replace (B * (d1 * (K - 1) + c * B - w0 - t1 - b0 - b1))
            with (B * d1 * (K - 1) + c * (B * B) - w0 * B -
                  B * t1 - (b0 + b1) * B) by ring.
          replace (B * t1) with (d0 * (B - K) - t0)
            by (rewrite <- HprodK; ring).
          ring. }
      assert (Hw0B: w0 * B = K * (B * B) - Ecur - d0 * (di + B) + c * (B * B)).
      { replace (B ^ 2) with (B * B) in HEK by ring.
        lia. }
      rewrite Hw0B in HrawKB.
      lia. }
    assert (Ht1_lower: d0 - K <= t1).
    { destruct (Z_le_gt_dec (d0 - K) t1) as [Hle | Hgt_t1]; [exact Hle |].
      exfalso.
      assert (Ht1_le: t1 <= d0 - K - 1) by lia.
      assert (Hsum_lt: t1 * B + t0 < (d0 - K) * B).
      { assert (t1 * B <= (d0 - K - 1) * B).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        assert (t0 <= B - 1) by lia.
        replace ((d0 - K - 1) * B + (B - 1)) with ((d0 - K) * B - 1) by ring.
        lia. }
      assert (Hsum_gt: (d0 - K) * B < t1 * B + t0).
      { rewrite HprodK.
        replace (d0 * (B - K) - (d0 - K) * B) with (K * (B - d0)) by ring.
        assert (0 < K * (B - d0)).
        { apply Z.mul_pos_pos; lia. }
        lia. }
      lia. }
    assert (Ht0_upper: d0 * (di + 1) + t0 <= d0 * (di - K + 1) + B * K).
    { assert (Hdiff:
        d0 * (di - K + 1) + B * K - (d0 * (di + 1) + t0) =
        B * (t1 - (d0 - K))).
      { assert (Ht0eq: t0 = d0 * (B - K) - t1 * B).
        { rewrite <- HprodK. ring. }
        rewrite Ht0eq.
        ring. }
      apply Z.le_0_sub.
      rewrite Hdiff.
      apply Z.mul_nonneg_nonneg; [subst B; lia | clear - Ht1_lower; lia]. }
    pose proof (udiv_3by2_raw_ge_coeff_k_gt1_bound d1 d0 di w0 w1 c K
      Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hw00 Hw0hi Hw10 Hc Hmul ltac:(subst B; reflexivity) HKge2) as Hbound.
    change 4294967296 with B in Hbound.
    change (B ^ 2) with (B * B) in Hbound.
    assert (Hbits_nonneg: 0 <= (b0 + b1) * B).
    { destruct Hb0 as [Hb0 | Hb0]; subst b0; destruct Hb1 as [Hb1 | Hb1]; subst b1; lia. }
    assert (Hupper_weak: K * (B * B - (B * d1 + d0)) <= d0 * (di + 1) + t0).
    { clear - Hupper Hbits_nonneg.
      lia. }
    exfalso.
    apply (Z.lt_irrefl (K * (B * B - (B * d1 + d0)))).
    eapply Z.le_lt_trans.
    - eapply Z.le_trans.
      + exact Hupper_weak.
      + exact Ht0_upper.
    - exact Hbound. }
  assert (HK: K = 1) by (clear - HKge1 HKle1; lia).
  rewrite HK in HprodK, HqhatK.
  assert (Hd0pos: 0 < d0) by (clear - Hn10 Hn1d0; lia).
  assert (Ht1eq: t1 = d0 - 1).
  { subst B.
    assert (Ht1div: t1 = d0 * (4294967296 - 1) / 4294967296).
    { apply Z.div_unique with (r := t0); lia. }
    assert (Hddiv: d0 * (4294967296 - 1) / 4294967296 = d0 - 1).
    { symmetry.
      apply Z.div_unique with (r := 4294967296 - d0); lia. }
    lia. }
  assert (Hqhat1: w1 + d1 + c = 4294967296 - 1) by (clear - HqhatK; lia).
  rewrite Hqhat1.
  rewrite Ht1eq.
  clear - Hd1hi Hn1d0.
  lia.
Qed.

Lemma udiv_3by2_raw_ge_coeff:
  forall d1 d0 di n2 n1 w0 w1 qlo qhat t0 t1 raw E D c b0 b1,
    2147483648 <= d1 -> d1 < 4294967296 ->
    0 <= d0 -> d0 < 4294967296 ->
    0 <= di -> di < 4294967296 ->
    0 <= n2 -> n2 < 4294967296 ->
    0 <= n1 -> n1 < 4294967296 ->
    n2 * 4294967296 + n1 < d1 * 4294967296 + d0 ->
    0 <= w0 -> w0 < 4294967296 ->
    0 <= w1 -> w1 < 4294967296 ->
    0 <= qlo -> qlo < 4294967296 ->
    0 <= t0 -> t0 < 4294967296 ->
    0 <= t1 -> t1 < 4294967296 ->
    D = 4294967296 * d1 + d0 ->
    E = 4294967296 ^ 3 - (di + 4294967296) * D ->
    1 <= E -> E <= D ->
    (c = 0 \/ c = 1) ->
    (b0 = 0 \/ b0 = 1) ->
    (b1 = 0 \/ b1 = 1) ->
    w0 + n1 = c * 4294967296 + qlo ->
    w1 * 4294967296 + w0 = n2 * di ->
    qhat = w1 + n2 + c ->
    t1 * 4294967296 + t0 = d0 * qhat ->
    raw = n1 - d1 * qhat - d1 - b0 - t1 - b1 + n2 * 4294967296 ->
    raw >= qlo ->
    raw + d1 + b0 + b1 <= 4294967296.
Proof.
  intros d1 d0 di n2 n1 w0 w1 qlo qhat t0 t1 raw E D c b0 b1
    Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn20 Hn2hi Hn10 Hn1hi Hnd
    Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Ht00 Ht0hi Ht10 Ht1hi
    HD HE HElo HEhi Hc Hb0 Hb1 Hcarry Hmul Hqhat Hprod Hraw Hrawge.
  subst qhat raw D E.
  assert (Hn2_cases: n2 < d1 \/ (n2 = d1 /\ n1 < d0)).
  { destruct (Z_lt_ge_dec n2 d1) as [Hlt | Hge].
    - left; exact Hlt.
    - right.
      assert (n2 <= d1).
      { destruct (Z_le_gt_dec n2 d1) as [Hle | Hgt]; [exact Hle |].
        assert (d1 + 1 <= n2) by lia.
        assert ((d1 + 1) * 4294967296 <= n2 * 4294967296).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        nia. }
      split; [lia | nia]. }
  destruct Hn2_cases as [Hn2d | [Hn2eq Hn1d0]].
  - clear Hnd Hn2hi.
    destruct Hc as [Hc | Hc]; subst c;
    destruct Hb0 as [Hb0 | Hb0]; subst b0;
    destruct Hb1 as [Hb1 | Hb1]; subst b1.
    + nia.
    + nia.
    + nia.
    + nia.
    + nia.
    + nia.
    + nia.
    + nia.
  - subst n2.
    clear Hnd Hn2hi.
    replace (n1 - d1 * (w1 + d1 + c) - d1 - b0 - t1 - b1 + d1 * 4294967296 + d1 + b0 + b1)
      with (n1 - d1 * (w1 + d1 + c) - t1 + d1 * 4294967296) by ring.
    apply (udiv_3by2_raw_ge_coeff_boundary d1 d0 di n1 w0 w1 qlo t0 t1 c b0 b1);
      assumption.
Qed.

Lemma udiv_3by2_raw_ge_no_over:
  forall d1 d0 di n2 n1 n0 w0 w1 qlo qhat t0 t1 raw rlo c b0 b1,
    2147483648 <= d1 -> d1 <= 4294967295 ->
    0 <= d0 -> d0 <= 4294967295 ->
    0 <= di -> di <= 4294967295 ->
    0 <= n2 -> n2 <= 4294967295 ->
    0 <= n1 -> n1 <= 4294967295 ->
    0 <= n0 -> n0 <= 4294967295 ->
    n2 * 4294967296 + n1 < d1 * 4294967296 + d0 ->
    0 <= w0 -> w0 <= 4294967295 ->
    0 <= w1 -> w1 <= 4294967295 ->
    0 <= qlo -> qlo < 4294967296 ->
    0 <= t0 -> t0 <= 4294967295 ->
    0 <= t1 -> t1 <= 4294967295 ->
    (c = 0 \/ c = 1) ->
    (b0 = 0 \/ b0 = 1) ->
    (b1 = 0 \/ b1 = 1) ->
    w0 + n1 = c * 4294967296 + qlo ->
    w1 * 4294967296 + w0 = n2 * di ->
    qhat = w1 + n2 + c ->
    t1 * 4294967296 + t0 = d0 * qhat ->
    raw = n1 - d1 * qhat - d1 - b0 - t1 - b1 + n2 * 4294967296 ->
    rlo = n0 - d0 + b0 * 4294967296 - t0 + b1 * 4294967296 ->
    0 <= rlo -> rlo < 4294967296 ->
    (di + 4294967296) * (4294967296 * d1 + d0) <=
      4294967296 ^ 3 - 1 ->
    4294967296 ^ 3 - 1 <
      (di + 4294967296 + 1) * (4294967296 * d1 + d0) ->
    raw >= qlo ->
    raw * 4294967296 + rlo + (d1 * 4294967296 + d0) < 4294967296 ^ 2.
Proof.
  intros d1 d0 di n2 n1 n0 w0 w1 qlo qhat t0 t1 raw rlo c b0 b1
    Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn20 Hn2hi Hn10 Hn1hi Hn00 Hn0hi Hnd
    Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Ht00 Ht0hi Ht10 Ht1hi
    Hc Hb0 Hb1 Hcarry Hmul Hqhat Hprod Hraw Hrlo Hrlo0 Hrlohi Hinvlo Hinvhi Hrawge.
  pose proof (udiv_3by2_preinv_e_bounds d1 d0 di
    Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hinvlo Hinvhi) as HE.
  pose proof (udiv_3by2_raw_ge_coeff d1 d0 di n2 n1 w0 w1 qlo qhat t0 t1 raw
    (4294967296 ^ 3 - (di + 4294967296) * (4294967296 * d1 + d0))
    (4294967296 * d1 + d0) c b0 b1
    Hd1lo ltac:(lia) Hd0lo ltac:(lia) Hdilo ltac:(lia) Hn20 ltac:(lia) Hn10 ltac:(lia) Hnd
    Hw00 ltac:(lia) Hw10 ltac:(lia) Hqlo0 Hqlohi Ht00 ltac:(lia) Ht10 ltac:(lia)
    eq_refl eq_refl (proj1 HE) (proj2 HE) Hc Hb0 Hb1 Hcarry Hmul Hqhat Hprod Hraw Hrawge)
    as Hcoeff.
  subst rlo.
  assert (n0 - t0 < 4294967296) by lia.
  nia.
Qed.

Lemma udiv_3by2_initial_split:
  forall d1 d0 di n2 n1 n0 w0 w1 qlo qhat t0 t1 raw rlo rhi c b0 b1,
    2147483648 <= d1 -> d1 <= 4294967295 ->
    0 <= d0 -> d0 <= 4294967295 ->
    0 <= di -> di <= 4294967295 ->
    0 <= n2 -> n2 <= 4294967295 ->
    0 <= n1 -> n1 <= 4294967295 ->
    0 <= n0 -> n0 <= 4294967295 ->
    n2 * 4294967296 + n1 < d1 * 4294967296 + d0 ->
    0 <= w0 -> w0 <= 4294967295 ->
    0 <= w1 -> w1 <= 4294967295 ->
    0 <= qlo -> qlo < 4294967296 ->
    0 <= t0 -> t0 <= 4294967295 ->
    0 <= t1 -> t1 <= 4294967295 ->
    (c = 0 \/ c = 1) ->
    (b0 = 0 \/ b0 = 1) ->
    (b1 = 0 \/ b1 = 1) ->
    w0 + n1 = c * 4294967296 + qlo ->
    w1 * 4294967296 + w0 = n2 * di ->
    qhat = w1 + n2 + c ->
    t1 * 4294967296 + t0 = d0 * qhat ->
    raw = n1 - d1 * qhat - d1 - b0 - t1 - b1 + n2 * 4294967296 ->
    rlo = n0 - d0 + b0 * 4294967296 - t0 + b1 * 4294967296 ->
    rhi = unsigned_last_nbits raw 32 ->
    0 <= rlo -> rlo < 4294967296 ->
    qlo - 4294967296 <= raw < 4294967296 ->
    (di + 4294967296) * (4294967296 * d1 + d0) <=
      4294967296 ^ 3 - 1 ->
    4294967296 ^ 3 - 1 <
      (di + 4294967296 + 1) * (4294967296 * d1 + d0) ->
    (rhi < qlo /\
      n2 * 4294967296 ^ 2 + n1 * 4294967296 + n0 =
        (qhat + 1) * (d1 * 4294967296 + d0) + rhi * 4294967296 + rlo) \/
    (rhi >= qlo /\
      rhi * 4294967296 + rlo + (d1 * 4294967296 + d0) >= 4294967296 ^ 2 /\
      n2 * 4294967296 ^ 2 + n1 * 4294967296 + n0 + 4294967296 ^ 2 =
        (qhat + 1) * (d1 * 4294967296 + d0) + rhi * 4294967296 + rlo) \/
    (rhi >= qlo /\
      rhi * 4294967296 + rlo + (d1 * 4294967296 + d0) < 4294967296 ^ 2 /\
      n2 * 4294967296 ^ 2 + n1 * 4294967296 + n0 =
        (qhat + 1) * (d1 * 4294967296 + d0) + rhi * 4294967296 + rlo).
Proof.
  intros d1 d0 di n2 n1 n0 w0 w1 qlo qhat t0 t1 raw rlo rhi c b0 b1
    Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn20 Hn2hi Hn10 Hn1hi Hn00 Hn0hi Hnd
    Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Ht00 Ht0hi Ht10 Ht1hi
    Hc Hb0 Hb1 Hcarry Hmul Hqhat Hprod Hraw Hrlo Hrhieq Hrlo0 Hrlohi
    Hraw_range Hinvlo Hinvhi.
  pose proof (udiv_3by2_raw_base_eq d1 d0 n2 n1 n0 qhat t0 t1 raw rlo b0 b1
    Hprod Hraw Hrlo) as Hbase.
  destruct (Z_lt_ge_dec raw 0) as [Hraw_neg | Hraw_nonneg].
  - assert (Hrhi: rhi = raw + 4294967296).
    { rewrite Hrhieq.
      unfold unsigned_last_nbits.
      change (2 ^ 32) with 4294967296.
      rewrite Z.mod_eq by lia.
      assert (raw / 4294967296 = -1).
      { symmetry. apply Z.div_unique with (r := raw + 4294967296); lia. }
      lia. }
    right; left.
    split; [lia |].
    split.
    + pose proof (udiv_3by2_qhat_remainder_nonneg d1 d0 di n2 n1 n0 w0 w1 qlo c
        Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn20 Hn2hi Hn10 Hn1hi Hn00 Hn0hi Hnd
        Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Hc Hcarry Hmul Hinvlo Hinvhi) as Hrem.
      rewrite Hrhi.
      rewrite <- Hqhat in Hrem.
      nia.
    + rewrite Hrhi.
      nia.
  - assert (Hrhi: rhi = raw).
    { rewrite Hrhieq.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    destruct (Z_lt_ge_dec raw qlo) as [Hraw_lt_qlo | Hraw_ge_qlo].
    + left.
      split; [lia |].
      rewrite Hrhi; exact Hbase.
    + right; right.
      split; [lia |].
      split.
      * rewrite Hrhi.
        pose proof (udiv_3by2_raw_ge_no_over d1 d0 di n2 n1 n0 w0 w1 qlo qhat t0 t1 raw rlo c b0 b1
          Hd1lo Hd1hi Hd0lo Hd0hi Hdilo Hdihi Hn20 Hn2hi Hn10 Hn1hi Hn00 Hn0hi Hnd
          Hw00 Hw0hi Hw10 Hw1hi Hqlo0 Hqlohi Ht00 Ht0hi Ht10 Ht1hi
          Hc Hb0 Hb1 Hcarry Hmul Hqhat Hprod Hraw Hrlo Hrlo0 Hrlohi Hinvlo Hinvhi Hraw_ge_qlo) as Hno.
        exact Hno.
      * rewrite Hrhi; exact Hbase.
Qed.

Lemma unsigned_last_nbits_add_mul_32:
  forall x k,
    unsigned_last_nbits (x + k * 4294967296) 32 =
    unsigned_last_nbits x 32.
Proof.
  intros x k.
  unfold unsigned_last_nbits.
  change (2 ^ 32) with 4294967296.
  rewrite Z.add_mod by lia.
  rewrite Z.mod_mul by lia.
  rewrite Z.add_0_r.
  rewrite Z.mod_mod by lia.
  reflexivity.
Qed.

Lemma u32_add_carry_eq:
  forall a b,
    0 <= a -> a <= 4294967295 ->
    0 <= b -> b <= 4294967295 ->
    (a + b) mod 4294967296 < a ->
    a + b = 4294967296 + (a + b) mod 4294967296.
Proof.
  intros a b Ha0 Hahi Hb0 Hbhi Hcarry.
  assert (HB: 0 < 4294967296) by lia.
  assert (Hsum_hi: a + b < 2 * 4294967296) by lia.
  assert (Hsum_ge: 4294967296 <= a + b).
  { destruct (Z_lt_ge_dec (a + b) 4294967296) as [Hlt | Hge]; [| lia].
    rewrite Z.mod_small in Hcarry by lia.
    lia. }
  assert (Hdiv: (a + b) / 4294967296 = 1).
  { symmetry. apply Z.div_unique with (r := a + b - 4294967296); lia. }
  pose proof (Z.div_mod (a + b) 4294967296 ltac:(lia)) as Hdm.
  nia.
Qed.

Lemma u32_add_no_carry_eq:
  forall a b,
    0 <= a -> a <= 4294967295 ->
    0 <= b -> b <= 4294967295 ->
    (a + b) mod 4294967296 >= a ->
    a + b = (a + b) mod 4294967296.
Proof.
  intros a b Ha0 Hahi Hb0 Hbhi Hnocarry.
  pose proof (Z_mod_add_uncarry b a 4294967296
    ltac:(lia) ltac:(lia) ltac:(lia)) as H.
  replace (b + a) with (a + b) in H by ring.
  replace ((b + a) mod 4294967296) with ((a + b) mod 4294967296) in H
    by (replace (b + a) with (a + b) by ring; reflexivity).
  apply H.
  replace (b + a) with (a + b) by ring.
  exact Hnocarry.
Qed.

Lemma u32_sub_borrow_eq:
  forall a b,
    0 <= a -> a <= 4294967295 ->
    0 <= b -> b <= 4294967295 ->
    a < b ->
    unsigned_last_nbits (a - b) 32 = a - b + 4294967296.
Proof.
  intros a b Ha0 Hahi Hb0 Hbhi Hlt.
  unfold unsigned_last_nbits.
  change (2 ^ 32) with 4294967296.
  rewrite Z.mod_eq by lia.
  assert ((a - b) / 4294967296 = -1).
  { symmetry. apply Z.div_unique with (r := a - b + 4294967296); lia. }
  lia.
Qed.

Lemma u32_sub_no_borrow_eq:
  forall a b,
    0 <= a -> a <= 4294967295 ->
    0 <= b -> b <= 4294967295 ->
    a >= b ->
    unsigned_last_nbits (a - b) 32 = a - b.
Proof.
  intros a b Ha0 Hahi Hb0 Hbhi Hge.
  apply unsigned_last_nbits_eq.
  change (2 ^ 32) with 4294967296.
  lia.
Qed.

Lemma mpn_div_qr_pi1_addback_transition :
  forall (l_cur l_low l_mid l_high l_mid_low l_mid_high l_out data_np
          l_np_add l_np_tail l_dp l_dp_low l_dp_high l_dp_add l_dp_tail : list Z)
         (dn0 nn0 i q n1 n0 n1_in n1_before n0_before d1 d0 dval
          val_out retval_2 val_np_add val_dp_add val_r_out retval remv_2 : Z),
    dn0 > 2 ->
    0 <= i ->
    i <= nn0 - dn0 ->
    Zlength l_cur = nn0 ->
    Zlength l_low = i ->
    Zlength l_mid = dn0 ->
    Zlength l_high = nn0 - (i + dn0) ->
    Zlength l_mid_low = dn0 - 2 ->
    Zlength l_mid_high = 2 ->
    Zlength l_out = dn0 - 2 ->
    Zlength data_np = dn0 - 1 ->
    Zlength l_np_tail = 1 ->
    Zlength l_dp = dn0 ->
    Zlength l_dp_low = dn0 - 2 ->
    Zlength l_dp_high = 2 ->
    Zlength l_dp_add = dn0 - 1 ->
    Zlength l_dp_tail = 1 ->
    l_low = sublist 0 i l_cur ->
    l_mid = sublist i (i + dn0) l_cur ->
    l_high = sublist (i + dn0) nn0 l_cur ->
    l_mid_low = sublist 0 (dn0 - 2) l_mid ->
    l_mid_high = sublist (dn0 - 2) dn0 l_mid ->
    l_np_add = l_out ++ sublist 0 1 (replace_Znth 0 n0 l_mid_high) ->
    l_np_tail = sublist 1 2 (replace_Znth 0 n0 l_mid_high) ->
    l_dp_low = sublist 0 (dn0 - 2) l_dp ->
    l_dp_high = sublist (dn0 - 2) dn0 l_dp ->
    l_dp_add = l_dp_low ++ sublist 0 1 l_dp_high ->
    l_dp_tail = sublist 1 2 l_dp_high ->
    list_within_bound UINT_MOD l_low ->
    list_within_bound UINT_MOD l_mid ->
    list_within_bound UINT_MOD l_high ->
    list_within_bound UINT_MOD l_mid_low ->
    list_within_bound UINT_MOD l_mid_high ->
    list_within_bound UINT_MOD l_out ->
    list_within_bound UINT_MOD data_np ->
    list_within_bound UINT_MOD l_np_tail ->
    list_within_bound UINT_MOD l_dp ->
    list_within_bound UINT_MOD l_dp_low ->
    list_within_bound UINT_MOD l_dp_high ->
    list_within_bound UINT_MOD l_dp_add ->
    list_within_bound UINT_MOD l_dp_tail ->
    list_to_Z UINT_MOD l_out = val_out ->
    list_to_Z UINT_MOD data_np = val_r_out ->
    list_to_Z UINT_MOD l_np_add = val_np_add ->
    list_to_Z UINT_MOD l_dp_add = val_dp_add ->
    val_r_out + retval * UINT_MOD ^ (dn0 - 1) = val_np_add + val_dp_add ->
    val_out - retval_2 * UINT_MOD ^ (dn0 - 2) =
      list_to_Z UINT_MOD l_mid_low - list_to_Z UINT_MOD l_dp_low * q ->
    list_to_Z UINT_MOD l_dp = dval ->
    d1 = Znth (dn0 - 1) l_dp 0 ->
    d0 = Znth (dn0 - 2) l_dp 0 ->
    0 <= retval ->
    retval <= 1 ->
    0 <= q ->
    q <= UINT_MAX ->
    0 <= n1_before ->
    n1_before <= UINT_MAX ->
    0 <= n0_before ->
    n0_before <= UINT_MAX ->
    n1_before < 1 ->
    n0_before < retval_2 ->
    n1 = unsigned_last_nbits (n1_before - 1) 32 ->
    n0 = unsigned_last_nbits (n0_before - retval_2) 32 ->
    UINT_MOD / 2 <= d1 ->
    d1 <= UINT_MAX ->
    0 <= d0 ->
    d0 <= UINT_MAX ->
    n1_in * UINT_MOD ^ 2 + Znth (dn0 - 1) l_mid 0 * UINT_MOD +
      Znth (dn0 - 2) l_mid 0 =
      q * (d1 * UINT_MOD + d0) + n1_before * UINT_MOD + n0_before ->
    n1_before * UINT_MOD + n0_before < d1 * UINT_MOD + d0 ->
    remv_2 =
      n1_in * UINT_MOD ^ (dn0 + i) +
      list_to_Z UINT_MOD (sublist 0 (dn0 + i) l_cur) ->
    let q_dec := unsigned_last_nbits (q - 1) 32 in
    let n1_new := unsigned_last_nbits (unsigned_last_nbits (n1 + d1) 32 + retval) 32 in
    let l_new := l_low ++ data_np ++ l_np_tail ++ l_high in
    let remv_new :=
      n1_new * UINT_MOD ^ (dn0 + (i - 1)) +
      list_to_Z UINT_MOD (sublist 0 (dn0 + (i - 1)) l_new) in
    q_dec = q - 1 /\
    remv_new = remv_2 - q_dec * dval * UINT_MOD ^ i /\
    0 <= remv_new /\
    remv_new < dval * UINT_MOD ^ i.
Proof.
  intros l_cur l_low l_mid l_high l_mid_low l_mid_high l_out data_np
         l_np_add l_np_tail l_dp l_dp_low l_dp_high l_dp_add l_dp_tail
         dn0 nn0 i q n1 n0 n1_in n1_before n0_before d1 d0 dval
         val_out retval_2 val_np_add val_dp_add val_r_out retval remv_2
         Hdn Hi Hirange Hcur_len Hlow_len Hmid_len Hhigh_len
         Hmidlow_len Hmidhigh_len Hout_len Hdata_len Hnptail_len
         Hdp_len Hdplow_len Hdphigh_len Hdpadd_len Hdptail_len
         Hlow Hmid Hhigh Hmidlow Hmidhigh Hnpadd Hnptail Hdplow Hdphigh
         Hdpadd Hdptail Hlow_bound Hmid_bound Hhigh_bound Hmidlow_bound
         Hmidhigh_bound Hout_bound Hdata_bound Hnptail_bound Hdp_bound
         Hdplow_bound Hdphigh_bound Hdpadd_bound Hdptail_bound
         Hout_val Hdata_val Hnpadd_val Hdpadd_val Hadd Hsubmul
         Hdval Hd1 Hd0 Hretval0 Hretval1 Hq0 Hqhi Hn1b0 Hn1bhi Hn0b0 Hn0bhi
         Hn1b_lt Hn0b_lt_ret Hn1_eq Hn0_eq Hd1lo Hd1hi Hd0lo Hd0hi
         Hwindow_eq Hpair_lt Hrem.
  set (B := UINT_MOD).
  assert (HBpos : 0 < B) by (subst B; unfold UINT_MOD; lia).
  assert (Hn1b_zero : n1_before = 0) by lia.
  assert (Hret2_pos : 1 <= retval_2) by lia.
  assert (Hpow_dn2_pos : 0 < B ^ (dn0 - 2)).
  { apply Z.pow_pos_nonneg; subst B; unfold UINT_MOD; lia. }
  assert (Hmidlow_bound_val :
    0 <= list_to_Z B l_mid_low < B ^ (dn0 - 2)).
  {
    subst B.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_mid_low Hmidlow_bound) as H.
    rewrite Hmidlow_len in H.
    exact H.
  }
  assert (Hdplow_bound_val :
    0 <= list_to_Z B l_dp_low < B ^ (dn0 - 2)).
  {
    subst B.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_dp_low Hdplow_bound) as H.
    rewrite Hdplow_len in H.
    exact H.
  }
  assert (Hout_bound_val :
    0 <= val_out < B ^ (dn0 - 2)).
  {
    subst B.
    rewrite <- Hout_val.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out Hout_bound) as H.
    rewrite Hout_len in H.
    exact H.
  }
  assert (Hret2_hi : retval_2 <= UINT_MAX).
  {
    subst B.
    change UINT_MAX with 4294967295.
    change UINT_MOD with 4294967296 in *.
    destruct (Z_le_gt_dec retval_2 4294967295) as [Hle | Hgt]; [exact Hle |].
    assert (Hleft : val_out - retval_2 * 4294967296 ^ (dn0 - 2) <=
                    val_out - 4294967296 * 4294967296 ^ (dn0 - 2)).
    { apply Z.sub_le_mono_l.
      apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hright :
      list_to_Z 4294967296 l_mid_low - list_to_Z 4294967296 l_dp_low * q >=
      - ((4294967296 ^ (dn0 - 2) - 1) * 4294967295)).
    {
      destruct Hmidlow_bound_val as [Hml0 _].
      destruct Hdplow_bound_val as [Hdl0 Hdlhi].
      assert (list_to_Z 4294967296 l_dp_low * q <=
              (4294967296 ^ (dn0 - 2) - 1) * 4294967295).
      { apply Z.mul_le_mono_nonneg; lia. }
      lia.
    }
    rewrite Hsubmul in Hleft.
    assert (4294967296 ^ (dn0 - 2) >= 1).
    {
      pose proof (Z.pow_pos_nonneg 4294967296 (dn0 - 2)
        ltac:(lia) ltac:(lia)).
      lia.
    }
    lia.
  }
  assert (Hret2_range : 0 <= retval_2 <= UINT_MAX) by lia.
  assert (Hn0_eq_full : n0 = n0_before + B - retval_2).
  {
    rewrite Hn0_eq.
    subst B.
    change UINT_MAX with 4294967295 in Hret2_hi.
    change UINT_MOD with 4294967296.
    rewrite (u32_sub_borrow_eq n0_before retval_2); try lia.
  }
  assert (Hn1_eq_full : n1 = B - 1).
  {
    rewrite Hn1_eq.
    rewrite Hn1b_zero.
    subst B.
    change UINT_MOD with 4294967296.
    rewrite (u32_sub_borrow_eq 0 1); try lia.
  }
  assert (Hq_pos : 1 <= q).
  {
    destruct (Z_le_gt_dec 1 q) as [Hqpos | Hqle]; [exact Hqpos |].
    assert (Hq_zero : q = 0) by lia.
    subst q.
    rewrite Z.mul_0_r, Z.sub_0_r in Hsubmul.
    assert (Hsubmul_B :
      val_out - retval_2 * B ^ (dn0 - 2) = list_to_Z B l_mid_low).
    { subst B.
      change UINT_MOD with 4294967296 in Hsubmul.
      exact Hsubmul. }
    rewrite <- Hsubmul_B in Hmidlow_bound_val.
    assert (val_out - retval_2 * B ^ (dn0 - 2) < 0).
    { destruct Hout_bound_val as [_ Hout_hi].
      assert (B ^ (dn0 - 2) <= retval_2 * B ^ (dn0 - 2)).
      { replace (B ^ (dn0 - 2)) with (1 * B ^ (dn0 - 2)) at 1 by ring.
        apply Z.mul_le_mono_nonneg_r; lia. }
      lia. }
    lia.
  }
  assert (Hq_dec : unsigned_last_nbits (q - 1) 32 = q - 1).
  {
    subst B.
    rewrite (u32_sub_no_borrow_eq q 1); try lia.
  }
  assert (Hn1_high : unsigned_last_nbits (n1 + d1) 32 = d1 - 1).
  {
    rewrite Hn1_eq_full.
    subst B.
    change UINT_MOD with 4294967296 in *.
    change UINT_MAX with 4294967295 in *.
    change (4294967296 / 2) with 2147483648 in Hd1lo.
    unfold unsigned_last_nbits.
    change (2 ^ 32) with 4294967296.
    symmetry.
    apply Z.mod_unique with (q := 1).
    - left; lia.
    - ring.
  }
  assert (Hn1_new :
    unsigned_last_nbits (unsigned_last_nbits (n1 + d1) 32 + retval) 32 =
    d1 - 1 + retval).
  {
    rewrite Hn1_high.
    apply unsigned_last_nbits_eq.
    change (2 ^ 32) with 4294967296.
    change UINT_MOD with 4294967296 in *.
    change UINT_MAX with 4294967295 in *.
    change (4294967296 / 2) with 2147483648 in Hd1lo.
    subst B.
    lia.
  }
  assert (Hmid_split : l_mid = l_mid_low ++ l_mid_high).
  {
    rewrite Hmidlow, Hmidhigh.
    rewrite <- (sublist_split 0 dn0 (dn0 - 2) l_mid) by lia.
    rewrite sublist_self by (symmetry; exact Hmid_len).
    reflexivity.
  }
  assert (Hdp_split : l_dp = l_dp_low ++ l_dp_high).
  {
    rewrite Hdplow, Hdphigh.
    rewrite <- (sublist_split 0 dn0 (dn0 - 2) l_dp) by lia.
    rewrite sublist_self by (symmetry; exact Hdp_len).
    reflexivity.
  }
  assert (Hmid_high_val :
    list_to_Z B l_mid_high =
      Znth (dn0 - 2) l_mid 0 + Znth (dn0 - 1) l_mid 0 * B).
  {
    subst B.
    rewrite Hmidhigh.
    replace (sublist (dn0 - 2) dn0 l_mid)
      with (sublist (dn0 - 2) (dn0 - 1) l_mid ++
            sublist (dn0 - 1) dn0 l_mid).
    - replace (sublist (dn0 - 2) (dn0 - 1) l_mid)
        with (sublist (dn0 - 2) ((dn0 - 2) + 1) l_mid) by (f_equal; lia).
      replace (sublist (dn0 - 1) dn0 l_mid)
        with (sublist (dn0 - 1) ((dn0 - 1) + 1) l_mid) by (f_equal; lia).
      rewrite !(sublist_single 0) by (rewrite Hmid_len; lia).
      change (((Znth (dn0 - 2) l_mid 0 :: nil) ++
               (Znth (dn0 - 1) l_mid 0 :: nil))%list)
        with (Znth (dn0 - 2) l_mid 0 :: Znth (dn0 - 1) l_mid 0 :: nil).
      rewrite list_to_Z_cons, list_to_Z_cons, list_to_Z_nil.
      ring.
    - rewrite (sublist_split (dn0 - 2) dn0 (dn0 - 1) l_mid) by lia.
      reflexivity.
  }
  assert (Hdp_high_val :
    list_to_Z B l_dp_high = d0 + d1 * B).
  {
    subst B.
    rewrite Hdphigh.
    replace (sublist (dn0 - 2) dn0 l_dp)
      with (sublist (dn0 - 2) (dn0 - 1) l_dp ++
            sublist (dn0 - 1) dn0 l_dp).
    - replace (sublist (dn0 - 2) (dn0 - 1) l_dp)
        with (sublist (dn0 - 2) ((dn0 - 2) + 1) l_dp) by (f_equal; lia).
      replace (sublist (dn0 - 1) dn0 l_dp)
        with (sublist (dn0 - 1) ((dn0 - 1) + 1) l_dp) by (f_equal; lia).
      rewrite !(sublist_single 0) by (rewrite Hdp_len; lia).
      change (((Znth (dn0 - 2) l_dp 0 :: nil) ++
               (Znth (dn0 - 1) l_dp 0 :: nil))%list)
        with (Znth (dn0 - 2) l_dp 0 :: Znth (dn0 - 1) l_dp 0 :: nil).
      rewrite list_to_Z_cons, list_to_Z_cons, list_to_Z_nil.
      rewrite <- Hd1, <- Hd0.
      ring.
    - rewrite (sublist_split (dn0 - 2) dn0 (dn0 - 1) l_dp) by lia.
      reflexivity.
  }
  assert (Hmid_decomp :
    list_to_Z B l_mid =
      list_to_Z B l_mid_low + list_to_Z B l_mid_high * B ^ (dn0 - 2)).
  {
    subst B.
    rewrite Hmid_split.
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hmidlow_len.
    reflexivity.
  }
  assert (Hdp_decomp :
    dval =
      list_to_Z B l_dp_low + list_to_Z B l_dp_high * B ^ (dn0 - 2)).
  {
    subst B.
    rewrite <- Hdval.
    rewrite Hdp_split.
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hdplow_len.
    reflexivity.
  }
  assert (Hnpadd_value :
    val_np_add = val_out + n0 * B ^ (dn0 - 2)).
  {
    rewrite <- Hnpadd_val, Hnpadd.
    rewrite list_to_Z_app by exact HBpos.
    rewrite Hout_len.
    replace (sublist 0 1 (replace_Znth 0 n0 l_mid_high))
      with (n0 :: nil).
    - rewrite list_to_Z_single.
      rewrite Hout_val.
      subst B.
      reflexivity.
    - replace (sublist 0 1 (replace_Znth 0 n0 l_mid_high))
        with (sublist 0 (0 + 1) (replace_Znth 0 n0 l_mid_high)) by reflexivity.
      rewrite (sublist_single 0) by (rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Same by lia.
      reflexivity.
  }
  assert (Hdpadd_value :
    val_dp_add = list_to_Z B l_dp_low + d0 * B ^ (dn0 - 2)).
  {
    rewrite <- Hdpadd_val, Hdpadd.
    rewrite list_to_Z_app by exact HBpos.
    rewrite Hdplow_len.
    replace (sublist 0 1 l_dp_high) with (d0 :: nil).
    - rewrite list_to_Z_single.
      subst B.
      reflexivity.
    - replace (sublist 0 1 l_dp_high)
        with (sublist 0 (0 + 1) l_dp_high) by reflexivity.
      rewrite (sublist_single 0) by (rewrite Hdphigh_len; lia).
      rewrite Hdphigh.
      rewrite Znth_sublist by (try rewrite Hdp_len; lia).
      replace (0 + (dn0 - 2)) with (dn0 - 2) by lia.
      rewrite <- Hd0.
      reflexivity.
  }
  assert (Hnew_prefix :
    sublist 0 (dn0 + (i - 1)) (l_low ++ data_np ++ l_np_tail ++ l_high) =
      l_low ++ data_np).
  {
    replace (dn0 + (i - 1)) with (Zlength (l_low ++ data_np)).
    - replace (l_low ++ data_np ++ l_np_tail ++ l_high)
        with ((l_low ++ data_np) ++ (l_np_tail ++ l_high)).
      apply sublist_app_exact1.
      repeat rewrite app_assoc.
      reflexivity.
    - rewrite Zlength_app, Hlow_len, Hdata_len.
      lia.
  }
  assert (Hnew_value :
    unsigned_last_nbits (unsigned_last_nbits (n1 + d1) 32 + retval) 32 *
      B ^ (dn0 + (i - 1)) +
    list_to_Z B (sublist 0 (dn0 + (i - 1))
      (l_low ++ data_np ++ l_np_tail ++ l_high)) =
    list_to_Z B l_low +
      (val_r_out +
       unsigned_last_nbits (unsigned_last_nbits (n1 + d1) 32 + retval) 32 *
       B ^ (dn0 - 1)) * B ^ i).
	  {
    subst B.
    rewrite Hnew_prefix.
    rewrite list_to_Z_app by exact HBpos.
    rewrite Hlow_len.
    rewrite Hdata_val.
    replace (dn0 + (i - 1)) with ((dn0 - 1) + i) by lia.
    rewrite Z.pow_add_r by lia.
    ring.
  }
  assert (Hpow_dni : B ^ (dn0 + i) = B ^ dn0 * B ^ i).
  { rewrite Z.pow_add_r by lia; reflexivity. }
  assert (Hpow_dn : B ^ dn0 = B ^ 2 * B ^ (dn0 - 2)).
  {
    replace dn0 with (2 + (dn0 - 2)) by lia.
    rewrite Z.pow_add_r by lia.
    replace (2 + (dn0 - 2) - 2) with (dn0 - 2) by lia.
    reflexivity.
  }
  assert (Hold_prefix :
    list_to_Z B (sublist 0 (dn0 + i) l_cur) =
    list_to_Z B l_low + list_to_Z B l_mid * B ^ i).
  {
    subst B.
    rewrite (sublist_split 0 (dn0 + i) i l_cur)
      by (split; try lia; rewrite Hcur_len; lia).
    rewrite <- Hlow.
    replace (sublist i (dn0 + i) l_cur) with l_mid
      by (rewrite Hmid; f_equal; lia).
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hlow_len.
    reflexivity.
  }
  assert (Hold_value :
    remv_2 =
    list_to_Z B l_low +
      (list_to_Z B l_mid + n1_in * B ^ dn0) * B ^ i).
  {
    rewrite Hrem.
    fold B.
    rewrite Hold_prefix, Hpow_dni.
    ring.
  }
  assert (Hwindow_relation :
    val_r_out +
      unsigned_last_nbits (unsigned_last_nbits (n1 + d1) 32 + retval) 32 *
        B ^ (dn0 - 1) =
    list_to_Z B l_mid + n1_in * B ^ dn0 - (q - 1) * dval).
  {
    assert (HsubmulB :
      list_to_Z B l_mid_low =
        list_to_Z B l_out - retval_2 * B ^ (dn0 - 2) +
        list_to_Z B l_dp_low * q).
    {
      subst B.
      rewrite Hout_val.
      lia.
    }
    assert (HwindowB :
      n1_in * B ^ 2 +
        (Znth (dn0 - 2) l_mid 0 + Znth (dn0 - 1) l_mid 0 * B) =
      q * (d1 * B + d0) + n0_before).
    {
      subst B.
      rewrite Hn1b_zero in Hwindow_eq.
      replace (n1_in * UINT_MOD ^ 2 +
        (Znth (dn0 - 2) l_mid 0 + Znth (dn0 - 1) l_mid 0 * UINT_MOD))
        with (n1_in * UINT_MOD ^ 2 +
          Znth (dn0 - 1) l_mid 0 * UINT_MOD + Znth (dn0 - 2) l_mid 0)
        by ring.
      rewrite Hwindow_eq.
      ring.
    }
    assert (Hpow_dn1 : B ^ (dn0 - 1) = B * B ^ (dn0 - 2)).
    {
      replace (dn0 - 1) with (1 + (dn0 - 2)) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      ring.
    }
    assert (HaddB :
      val_r_out + retval * B ^ (dn0 - 1) = val_np_add + val_dp_add).
    { subst B; exact Hadd. }
    assert (HoutB : list_to_Z B l_out = val_out).
    { subst B; exact Hout_val. }
    assert (Hsub_cancel :
      list_to_Z B l_mid_low - q * list_to_Z B l_dp_low =
      list_to_Z B l_out - retval_2 * B ^ (dn0 - 2)).
    { rewrite HsubmulB. ring. }
    assert (Hwin_cancel :
      n1_in * B ^ 2 +
        (Znth (dn0 - 2) l_mid 0 + Znth (dn0 - 1) l_mid 0 * B) -
        q * (d1 * B + d0) =
      n0_before).
    { rewrite HwindowB. ring. }
    rewrite Hn1_new.
    replace (val_r_out + (d1 - 1 + retval) * B ^ (dn0 - 1))
      with (val_r_out + retval * B ^ (dn0 - 1) +
            (d1 - 1) * B ^ (dn0 - 1)) by ring.
    replace (val_r_out + retval * B ^ (dn0 - 1) +
             (d1 - 1) * B ^ (dn0 - 1))
      with ((val_r_out + retval * B ^ (dn0 - 1)) +
            (d1 - 1) * B ^ (dn0 - 1)) by ring.
    rewrite HaddB, Hnpadd_value, Hdpadd_value, Hn0_eq_full.
    rewrite Hmid_decomp, Hdp_decomp, Hmid_high_val, Hdp_high_val.
    rewrite Hpow_dn, Hpow_dn1.
    set (P := B ^ (dn0 - 2)) in *.
    set (Lm := list_to_Z B l_mid_low) in *.
    set (C := list_to_Z B l_dp_low) in *.
    set (M := Znth (dn0 - 2) l_mid 0 + Znth (dn0 - 1) l_mid 0 * B) in *.
    assert (Hsub_cancel_v : Lm - q * C = val_out - retval_2 * P).
    {
      rewrite Hsub_cancel.
      rewrite HoutB.
      reflexivity.
    }
    assert (Hwin_cancel_v :
      n1_in * B ^ 2 + M - q * (d0 + d1 * B) = n0_before).
    {
      replace (d0 + d1 * B) with (d1 * B + d0) by ring.
      exact Hwin_cancel.
    }
    replace (val_out + (n0_before + B - retval_2) * P +
             (C + d0 * P) + (d1 - 1) * B * P)
      with (val_out + C + (n0_before - retval_2 + (d0 + d1 * B)) * P)
      by ring.
    replace (Lm + M * P + n1_in * (B ^ 2 * P) -
             (q - 1) * (C + (d0 + d1 * B) * P))
      with ((Lm - q * C) + C +
            (n1_in * B ^ 2 + M - q * (d0 + d1 * B) +
             (d0 + d1 * B)) * P) by ring.
    rewrite Hsub_cancel_v.
    replace (n1_in * B ^ 2 + M - q * (d0 + d1 * B) + (d0 + d1 * B))
      with (n0_before + (d0 + d1 * B)) by (rewrite Hwin_cancel_v; ring).
    ring.
  }
  assert (Hrem_eq :
    unsigned_last_nbits (unsigned_last_nbits (n1 + d1) 32 + retval) 32 *
      B ^ (dn0 + (i - 1)) +
    list_to_Z B (sublist 0 (dn0 + (i - 1))
      (l_low ++ data_np ++ l_np_tail ++ l_high)) =
    remv_2 - (q - 1) * dval * B ^ i).
  {
    rewrite Hnew_value, Hold_value, Hwindow_relation.
    ring.
  }
  assert (Hblock_nonneg :
    0 <= val_r_out +
      unsigned_last_nbits (unsigned_last_nbits (n1 + d1) 32 + retval) 32 *
        B ^ (dn0 - 1)).
  {
    rewrite Hn1_new.
    apply Z.add_nonneg_nonneg.
    - subst B.
      rewrite <- Hdata_val.
      pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos data_np Hdata_bound) as H.
      lia.
    - assert (0 <= d1 - 1 + retval).
      { change UINT_MOD with 4294967296 in Hd1lo.
        change (4294967296 / 2) with 2147483648 in Hd1lo.
        lia. }
      apply Z.mul_nonneg_nonneg; [lia |].
      apply Z.pow_nonneg; lia.
  }
  assert (Hblock_lt :
    val_r_out +
      unsigned_last_nbits (unsigned_last_nbits (n1 + d1) 32 + retval) 32 *
        B ^ (dn0 - 1) < dval).
  {
    rewrite Hwindow_relation.
    rewrite Hmid_decomp, Hdp_decomp, Hmid_high_val, Hdp_high_val.
    assert (HwindowB :
      n1_in * B ^ 2 +
        (Znth (dn0 - 2) l_mid 0 + Znth (dn0 - 1) l_mid 0 * B) =
      q * (d1 * B + d0) + n0_before).
    {
      subst B.
      rewrite Hn1b_zero in Hwindow_eq.
      replace (n1_in * UINT_MOD ^ 2 +
        (Znth (dn0 - 2) l_mid 0 + Znth (dn0 - 1) l_mid 0 * UINT_MOD))
        with (n1_in * UINT_MOD ^ 2 +
          Znth (dn0 - 1) l_mid 0 * UINT_MOD + Znth (dn0 - 2) l_mid 0)
        by ring.
      rewrite Hwindow_eq.
      ring.
    }
    assert (HsubmulB :
      list_to_Z B l_mid_low =
        list_to_Z B l_out - retval_2 * B ^ (dn0 - 2) +
        list_to_Z B l_dp_low * q).
    {
      subst B.
      rewrite Hout_val.
      lia.
    }
    assert (Hpow_dn_block : B ^ dn0 = B ^ 2 * B ^ (dn0 - 2)).
    {
      replace dn0 with (2 + (dn0 - 2)) by lia.
      rewrite Z.pow_add_r by lia.
      replace (2 + (dn0 - 2) - 2) with (dn0 - 2) by lia.
      reflexivity.
    }
    rewrite Hpow_dn_block.
    replace (list_to_Z B l_mid_low +
       (Znth (dn0 - 2) l_mid 0 + Znth (dn0 - 1) l_mid 0 * B) *
       B ^ (dn0 - 2) + n1_in * (B ^ 2 * B ^ (dn0 - 2)) -
       (q - 1) * (list_to_Z B l_dp_low + (d0 + d1 * B) * B ^ (dn0 - 2)))
      with (list_to_Z B l_mid_low - (q - 1) * list_to_Z B l_dp_low +
            (n1_in * B ^ 2 + (Znth (dn0 - 2) l_mid 0 +
             Znth (dn0 - 1) l_mid 0 * B) - (q - 1) * (d0 + d1 * B)) *
            B ^ (dn0 - 2)) by ring.
    rewrite HwindowB.
    replace (q * (d1 * B + d0) + n0_before -
             (q - 1) * (d0 + d1 * B))
      with (d0 + d1 * B + n0_before) by ring.
    replace (d0 + d1 * B) with (d1 * B + d0) by ring.
    assert (Hborrow_low :
      list_to_Z B l_mid_low + n0_before * B ^ (dn0 - 2) <
      q * list_to_Z B l_dp_low).
    {
      rewrite HsubmulB.
      replace (list_to_Z B l_out - retval_2 * B ^ (dn0 - 2) +
               list_to_Z B l_dp_low * q + n0_before * B ^ (dn0 - 2))
        with (list_to_Z B l_dp_low * q +
              list_to_Z B l_out - (retval_2 - n0_before) * B ^ (dn0 - 2))
        by ring.
      assert (1 <= retval_2 - n0_before) by lia.
      destruct Hout_bound_val as [_ Hout_hi].
	      assert (list_to_Z B l_out < (retval_2 - n0_before) * B ^ (dn0 - 2)).
	      { assert (B ^ (dn0 - 2) <= (retval_2 - n0_before) * B ^ (dn0 - 2)).
	        { replace (B ^ (dn0 - 2)) with (1 * B ^ (dn0 - 2)) at 1 by ring.
            apply Z.mul_le_mono_nonneg_r; lia. }
          assert (list_to_Z B l_out = val_out) by (subst B; exact Hout_val).
	        lia. }
      lia.
    }
    replace (list_to_Z B l_dp_low + (d0 + d1 * B) * B ^ (dn0 - 2))
      with (list_to_Z B l_dp_low + (d1 * B + d0) * B ^ (dn0 - 2)) by ring.
    replace (list_to_Z B l_mid_low - (q - 1) * list_to_Z B l_dp_low +
             (d1 * B + d0 + n0_before) * B ^ (dn0 - 2))
      with (list_to_Z B l_dp_low + (d1 * B + d0) * B ^ (dn0 - 2) +
            (list_to_Z B l_mid_low + n0_before * B ^ (dn0 - 2) -
             q * list_to_Z B l_dp_low)) by ring.
    lia.
  }
  split.
  - exact Hq_dec.
  - split.
    + rewrite Hq_dec.
      exact Hrem_eq.
	    + split.
	      * rewrite Hnew_value, Hn1_new.
	        rewrite Hn1_new in Hblock_nonneg.
	        apply Z.add_nonneg_nonneg.
	        -- pose proof (list_to_Z_bound B HBpos l_low Hlow_bound) as H.
	           lia.
	        -- apply Z.mul_nonneg_nonneg; [exact Hblock_nonneg | apply Z.pow_nonneg; lia].
	      * rewrite Hnew_value, Hn1_new.
	        assert (Hlow_bound_val :
	          0 <= list_to_Z B l_low < B ^ i).
        {
          pose proof (list_to_Z_bound B HBpos l_low Hlow_bound) as H.
          rewrite Hlow_len in H.
          exact H.
        }
	        assert (Hpow_i_pos : 0 < B ^ i).
	        { apply Z.pow_pos_nonneg; lia. }
	        rewrite Hn1_new in Hblock_lt.
	        set (low := list_to_Z B l_low) in *.
	        set (blk := val_r_out + (d1 - 1 + retval) * B ^ (dn0 - 1)) in *.
	        assert (Hlow_le : low <= B ^ i - 1) by lia.
	        assert (Hblk_le : blk <= dval - 1) by lia.
	        replace (dval * B ^ i) with (B ^ i + (dval - 1) * B ^ i) by ring.
	        apply Z.add_lt_le_mono.
	        -- lia.
	        -- apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma unsigned_last_nbits_sub_low_32:
  forall a b,
    unsigned_last_nbits (a - unsigned_last_nbits b 32) 32 =
    unsigned_last_nbits (a - b) 32.
Proof.
  intros a b.
  replace (a - unsigned_last_nbits b 32) with
    (a - b + (b / 4294967296) * 4294967296).
  - apply unsigned_last_nbits_add_mul_32.
  - unfold unsigned_last_nbits.
    change (2 ^ 32) with 4294967296.
    pose proof (Z.div_mod b 4294967296 ltac:(lia)).
    nia.
Qed.

Lemma unsigned_last_nbits_sub_32:
  forall x y,
    unsigned_last_nbits (unsigned_last_nbits x 32 - y) 32 =
    unsigned_last_nbits (x - y) 32.
Proof.
  intros.
  apply unsigned_unsigned_sub_l.
  lia.
Qed.

Lemma unsigned_last_nbits_sub2_32:
  forall x y z,
    unsigned_last_nbits (unsigned_last_nbits x 32 - y - z) 32 =
    unsigned_last_nbits (x - y - z) 32.
Proof.
  intros.
  replace (unsigned_last_nbits x 32 - y - z)
    with (unsigned_last_nbits x 32 - (y + z)) by ring.
  rewrite unsigned_last_nbits_sub_32.
  replace (x - (y + z)) with (x - y - z) by ring.
  reflexivity.
Qed.

Lemma unsigned_last_nbits_sub3_32:
  forall x y z w,
    unsigned_last_nbits (unsigned_last_nbits x 32 - y - z - w) 32 =
    unsigned_last_nbits (x - y - z - w) 32.
Proof.
  intros.
  replace (unsigned_last_nbits x 32 - y - z - w)
    with (unsigned_last_nbits x 32 - (y + z + w)) by ring.
  rewrite unsigned_last_nbits_sub_32.
  replace (x - (y + z + w)) with (x - y - z - w) by ring.
  reflexivity.
Qed.

Lemma unsigned_last_nbits_sub4_32:
  forall x y z w v,
    unsigned_last_nbits (unsigned_last_nbits x 32 - y - z - w - v) 32 =
    unsigned_last_nbits (x - y - z - w - v) 32.
Proof.
  intros.
  replace (unsigned_last_nbits x 32 - y - z - w - v)
    with (unsigned_last_nbits x 32 - (y + z + w + v)) by ring.
  rewrite unsigned_last_nbits_sub_32.
  replace (x - (y + z + w + v)) with (x - y - z - w - v) by ring.
  reflexivity.
Qed.

Lemma udiv_3by2_raw_high_expr_eq:
  forall n1 d1 qhat b0 t1 b1 n2,
    unsigned_last_nbits
      (unsigned_last_nbits
         (unsigned_last_nbits
            (unsigned_last_nbits
               (unsigned_last_nbits
                  (n1 - unsigned_last_nbits (d1 * qhat) 32) 32 - d1) 32 - b0)
            32 - t1) 32 - b1) 32 =
    unsigned_last_nbits
      (n1 - d1 * qhat - d1 - b0 - t1 - b1 + n2 * 4294967296) 32.
Proof.
  intros.
  rewrite unsigned_last_nbits_sub_low_32.
  rewrite unsigned_last_nbits_sub_32.
  rewrite unsigned_last_nbits_sub2_32.
  rewrite unsigned_last_nbits_sub3_32.
  rewrite unsigned_last_nbits_sub4_32.
  replace (n1 - d1 * qhat - d1 - b0 - t1 - b1 + n2 * 4294967296)
    with ((n1 - d1 * qhat - d1 - b0 - t1 - b1) +
          n2 * 4294967296) by ring.
  rewrite unsigned_last_nbits_add_mul_32.
  reflexivity.
Qed.

Lemma Z_land_m1_l:
  forall x, Z.land (-1) x = x.
Proof.
  intros x.
  apply Z.bits_inj'; intros n Hn.
  rewrite Z.land_spec, Z.bits_m1 by lia.
  destruct (Z.testbit x n); reflexivity.
Qed.

Lemma udiv_preinv_error_range:
  forall d di nh nl w0 w1 ql c,
    2147483648 <= d -> d <= 4294967295 ->
    0 <= di -> di <= 4294967295 ->
    0 <= nh -> nh < d ->
    0 <= nl -> nl <= 4294967295 ->
    0 <= w0 -> w0 <= 4294967295 ->
    0 <= w1 -> w1 <= 4294967295 ->
    0 <= ql -> ql < 4294967296 ->
    (c = 0 \/ c = 1) ->
    w0 + nl = c * 4294967296 + ql ->
    w1 * 4294967296 + w0 = nh * di ->
    (di + 4294967296) * (4294967296 * d) <= 4294967296 ^ 3 - 1 ->
    4294967296 ^ 3 - 1 < (di + 4294967296 + 1) * (4294967296 * d) ->
    -4294967296 <
      nh * 4294967296 + nl - (w1 + nh + 1 + c) * d <
    4294967296.
Proof.
  intros d di nh nl w0 w1 ql c Hdlo Hdhi Hdi0 Hdi1 Hnh0 Hnhd Hnl0 Hnl1
    Hw00 Hw01 Hw10 Hw11 Hql0 Hql1 Hc Hcarry Hmul Hinvlo Hinvhi.
  set (e := 4294967296 ^ 2 - (di + 4294967296) * d).
  pose proof (udiv_preinv_e_bounds d di Hdlo Hdhi Hdi0 Hdi1 Hinvlo Hinvhi)
    as He.
  fold e in He.
  assert (Hdi_eq: di * d = 4294967296 ^ 2 - 4294967296 * d - e)
    by (subst e; ring).
  assert (Hmul_d: (w1 * 4294967296 + w0) * d = nh * di * d)
    by (rewrite Hmul; ring).
  assert (Hformula:
    4294967296 * (nh * 4294967296 + nl - (w1 + nh + 1 + c) * d) =
    w0 * d + nl * 4294967296 + nh * e -
      (1 + c) * d * 4294967296) by nia.
  destruct Hc as [Hc | Hc]; subst c; split.
  - enough (-4294967296 * 4294967296 <
      4294967296 * (nh * 4294967296 + nl - (w1 + nh + 1 + 0) * d))
      by nia.
    rewrite Hformula; nia.
  - enough (4294967296 * (nh * 4294967296 + nl -
      (w1 + nh + 1 + 0) * d) < 4294967296 * 4294967296) by nia.
    rewrite Hformula; nia.
  - enough (-4294967296 * 4294967296 <
      4294967296 * (nh * 4294967296 + nl - (w1 + nh + 1 + 1) * d))
      by nia.
    rewrite Hformula; nia.
  - enough (4294967296 * (nh * 4294967296 + nl -
      (w1 + nh + 1 + 1) * d) < 4294967296 * 4294967296) by nia.
    rewrite Hformula; nia.
Qed.

Lemma udiv_preinv_wit8_R_nonneg_contra:
  forall d nh nl w0 R e,
    2147483648 <= d ->
    d <= 4294967295 ->
    0 <= nh ->
    nh < d ->
    0 <= nl ->
    nl <= 4294967295 ->
    0 <= w0 ->
    w0 <= 4294967295 ->
    1 <= e ->
    e <= d ->
    4294967296 <= w0 + nl ->
    4294967296 * R =
      w0 * d + nl * 4294967296 + nh * e - 2 * d * 4294967296 ->
    R >= 0 ->
    R > w0 + nl - 4294967296 ->
    4294967296 <= R + d ->
    False.
Proof.
  intros.
  nia.
Qed.

Lemma mpn_invert_u1_split16:
  forall u,
    UINT_MOD ÷ 2 <= u -> u <= 4294967295 ->
    0 <= Z.land u 65535 < 65536 /\
    1 <= Z.shiftr u 16 < 65536 /\
    u = Z.shiftr u 16 * 65536 + Z.land u 65535.
Proof.
  intros u Hlo Hhi.
  pose proof (mpn_invert_u1_range u Hlo Hhi) as Hu.
  pose proof (land_65535_bounds u Hu) as Hland.
  pose proof (shiftr_16_bounds u Hu) as Hshr.
  split; [exact Hland | split].
  - split.
    + pose proof (mpn_invert_u1_high_nonzero u Hlo Hhi) as Hnz.
      lia.
    + lia.
  - rewrite Z.shiftr_div_pow2 by lia.
    assert (Hones: 65535 = Z.ones 16) by reflexivity.
    rewrite Hones.
    rewrite Z.land_ones by lia.
    change (2 ^ 16) with 65536.
    rewrite (Z.div_mod u 65536) at 1 by lia.
    ring.
Qed.

Lemma unsigned_lnot_32:
  forall u,
    0 <= u < 4294967296 ->
    unsigned_last_nbits (Z.lnot u) 32 = 4294967295 - u.
Proof.
  intros u Hu.
  rewrite Z.lnot_eq_pred_opp.
  unfold unsigned_last_nbits.
  replace (2 ^ 32) with 4294967296 by reflexivity.
  symmetry.
  apply Z.mod_unique with (q := -1).
  - left; lia.
  - ring.
Qed.

Lemma lxor_uintmax_sub:
  forall u,
    0 <= u < 4294967296 ->
    Z.lxor u 4294967295 = 4294967295 - u.
Proof.
  intros u Hu.
  assert (Hxor_range:
            unsigned_last_nbits (Z.lxor u 4294967295) 32 =
            Z.lxor u 4294967295).
  { apply unsigned_last_nbits_lxor_distr_missing; lia. }
  rewrite <- Hxor_range.
  replace 4294967295 with (unsigned_last_nbits (-1) 32) at 1 by reflexivity.
  rewrite <- (unsigned_last_nbits_eq u 32 Hu) at 1.
  rewrite <- unsigned_last_nbits_lxor_distr by lia.
  rewrite Z.lxor_m1_r.
  rewrite unsigned_revolutive by lia.
  apply unsigned_lnot_32; lia.
Qed.

Lemma mpn_invert_qh_range:
  forall u uh,
    UINT_MOD ÷ 2 <= u -> u <= 4294967295 ->
    uh = Z.shiftr u 16 ->
    0 <= (Z.lxor u 4294967295) / uh < 65536.
Proof.
  intros u uh Hlo Hhi Huh.
  pose proof (mpn_invert_u1_range u Hlo Hhi) as Hu.
  pose proof (mpn_invert_u1_split16 u Hlo Hhi)
    as [Hland [[Huh_lo Huh_hi] Hsplit]].
  rewrite lxor_uintmax_sub by lia.
  subst uh.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 16) with 65536.
  split.
  - assert (0 < u / 65536)
      by (change (UINT_MOD ÷ 2) with 2147483648 in Hlo;
          apply Z.div_str_pos; lia).
    apply Z.div_pos; lia.
  - assert (0 < u / 65536)
      by (change (UINT_MOD ÷ 2) with 2147483648 in Hlo;
          apply Z.div_str_pos; lia).
    apply Z.div_lt_upper_bound; [lia |].
    change (UINT_MOD ÷ 2) with 2147483648 in Hlo.
    assert (32768 <= u / 65536)
      by (apply Z.div_le_lower_bound; lia).
    nia.
Qed.

Lemma mpn_invert_qh_quot_range:
  forall u uh,
    UINT_MOD ÷ 2 <= u -> u <= 4294967295 ->
    uh = Z.shiftr u 16 ->
    0 <= (Z.lxor u 4294967295) ÷ uh < 65536.
Proof.
  intros u uh Hlo Hhi Huh.
  pose proof (mpn_invert_u1_range u Hlo Hhi) as Hu.
  pose proof (mpn_invert_u1_split16 u Hlo Hhi) as [_ [[Huh_lo _] _]].
  assert (Hnum: 0 <= Z.lxor u 4294967295).
  { rewrite lxor_uintmax_sub by lia. lia. }
  assert (Hden: 0 <= uh).
  { subst uh; lia. }
  rewrite Z.quot_div_nonneg by lia.
  apply (mpn_invert_qh_range u uh Hlo Hhi Huh).
Qed.

Lemma mpn_invert_qh_rem_bounds:
  forall u uh qh,
    0 <= u < 4294967296 ->
    1 <= uh < 65536 ->
    qh = (Z.lxor u 4294967295) ÷ uh ->
    qh * uh <= 4294967295 - u /\
    0 <= 4294967295 - u - qh * uh < uh.
Proof.
  intros u uh qh Hu Huh Hqh.
  rewrite lxor_uintmax_sub in Hqh by lia.
  rewrite Z.quot_div_nonneg in Hqh by lia.
  subst qh.
  pose proof (Z.div_mod (4294967295 - u) uh ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (4294967295 - u) uh ltac:(lia)) as Hmod.
  split; nia.
Qed.

Lemma mpn_invert_rinit_simpl:
  forall u uh qh,
    0 <= u < 4294967296 ->
    1 <= uh < 65536 ->
    0 <= qh < 65536 ->
    qh * uh <= 4294967295 - u ->
    4294967295 - u - qh * uh < uh ->
    Z.lor
      (unsigned_last_nbits
         (Z.shiftl
            (unsigned_last_nbits
               (unsigned_last_nbits (Z.lnot u) 32 -
                unsigned_last_nbits (qh * uh) 32) 32) 16) 32) 65535 =
      (4294967295 - u - qh * uh) * 65536 + 65535.
Proof.
  intros u uh qh Hu Huh Hqh Hle Hrem_ub.
  rewrite unsigned_lnot_32 by lia.
  rewrite (unsigned_last_nbits_eq (qh * uh) 32)
    by (change (2 ^ 32) with 4294967296; nia).
  rewrite (unsigned_last_nbits_eq (4294967295 - u - qh * uh) 32)
    by (change (2 ^ 32) with 4294967296; lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 16) with 65536.
  replace 65535 with (Z.shiftr 4294967295 (32 - 16)) by reflexivity.
  replace 65536 with (2 ^ 16) by reflexivity.
  rewrite (mpn_lshift_lor_add (4294967295 - u - qh * uh) 4294967295 16).
  - rewrite unsigned_last_nbits_eq
      by (change (2 ^ 32) with 4294967296; nia).
    ring.
  - unfold UINT_MOD; lia.
  - lia.
Qed.

Lemma mpn_invert_first_no_adjust_simpl:
  forall u ul uh qh rem r0 p,
    0 <= ul < 65536 ->
    1 <= uh < 65536 ->
    u = uh * 65536 + ul ->
    0 <= qh < 65536 ->
    0 <= rem < uh ->
    4294967295 - u = qh * uh + rem ->
    r0 = rem * 65536 + 65535 ->
    p = qh * ul ->
    p <= r0 ->
    (qh + 65536) * u + (r0 - p) = Z.pow 65536 3 - 1 /\
    0 <= r0 - p < u.
Proof.
  intros.
  subst u r0 p.
  split; nia.
Qed.

Lemma mpn_invert_first_overflow_simpl:
  forall u ul uh qh rem r0 p,
    0 <= ul < 65536 ->
    1 <= uh < 65536 ->
    u = uh * 65536 + ul ->
    0 <= qh < 65536 ->
    0 <= rem < uh ->
    4294967295 - u = qh * uh + rem ->
    r0 = rem * 65536 + 65535 ->
    p = qh * ul ->
    r0 < p ->
    4294967296 <= r0 + u ->
    (qh - 1 + 65536) * u + (r0 + u - p) = Z.pow 65536 3 - 1 /\
    0 <= r0 + u - p < u /\
    1 <= qh.
Proof.
  intros.
  subst u r0 p.
  repeat split; nia.
Qed.

Lemma mpn_invert_first_one_adjust_simpl:
  forall u ul uh qh rem r0 p,
    0 <= ul < 65536 ->
    1 <= uh < 65536 ->
    u = uh * 65536 + ul ->
    0 <= qh < 65536 ->
    0 <= rem < uh ->
    4294967295 - u = qh * uh + rem ->
    r0 = rem * 65536 + 65535 ->
    p = qh * ul ->
    r0 < p ->
    r0 + u < 4294967296 ->
    p <= r0 + u ->
    (qh - 1 + 65536) * u + (r0 + u - p) = Z.pow 65536 3 - 1 /\
    0 <= r0 + u - p < u /\
    1 <= qh.
Proof.
  intros.
  subst u r0 p.
  repeat split; nia.
Qed.

Lemma mpn_invert_first_two_adjust_simpl:
  forall u ul uh qh rem r0 p,
    0 <= ul < 65536 ->
    1 <= uh < 65536 ->
    u = uh * 65536 + ul ->
    0 <= qh < 65536 ->
    0 <= rem < uh ->
    4294967295 - u = qh * uh + rem ->
    r0 = rem * 65536 + 65535 ->
    p = qh * ul ->
    r0 < p ->
    r0 + u < 4294967296 ->
    u <= r0 + u ->
    r0 + u < p ->
    (qh - 2 + 65536) * u + (r0 + 2 * u - p) = Z.pow 65536 3 - 1 /\
    0 <= r0 + 2 * u - p < u /\
    2 <= qh.
Proof.
  intros.
  subst u r0 p.
  repeat split; nia.
Qed.

Lemma unsigned_last_nbits_overflow_32:
  forall x,
    4294967296 <= x < 2 * 4294967296 ->
    unsigned_last_nbits x 32 = x - 4294967296.
Proof.
  intros x Hx.
  unfold unsigned_last_nbits.
  replace (2 ^ 32) with 4294967296 by reflexivity.
  symmetry.
  apply Z.mod_unique with (q := 1).
  - left; lia.
  - ring.
Qed.

Lemma unsigned_last_nbits_underflow_32:
  forall x,
    0 <= x < 4294967296 ->
    unsigned_last_nbits (x - 4294967296) 32 = x.
Proof.
  intros x Hx.
  unfold unsigned_last_nbits.
  replace (2 ^ 32) with 4294967296 by reflexivity.
  symmetry.
  apply Z.mod_unique with (q := -1).
  - left; lia.
  - ring.
Qed.

Lemma mpn_invert_no_uint_factor_between_32_33:
  forall x,
    4294967296 < x < 8589934592 ->
    Z.divide x 79228162514264337593543950336 ->
    False.
Proof.
  intros x Hx Hdiv.
  change 79228162514264337593543950336 with (2 ^ 96) in Hdiv.
  pose proof (Zdivide_power_2 x 2 96 ltac:(lia) ltac:(lia) prime_2 Hdiv)
    as [m Hm].
  subst x.
  assert (Hm_nonneg: 0 <= m).
  { destruct m; simpl in Hx; lia. }
  destruct (Z_lt_ge_dec m 33) as [Hlt | Hge].
  - assert (2 ^ m <= 2 ^ 32).
    { apply Z.pow_le_mono_r; lia. }
    change (2 ^ 32) with 4294967296 in H.
    lia.
  - assert (2 ^ 33 <= 2 ^ m).
    { apply Z.pow_le_mono_r; lia. }
    change (2 ^ 33) with 8589934592 in H.
    lia.
Qed.

Lemma mpn_invert_final_no_carry:
  forall u0 u1 m r tl th,
    0 <= u0 <= 4294967295 -> u0 > 0 ->
    0 <= u1 <= 4294967295 ->
    0 <= m <= 4294967295 ->
    0 <= r <= 4294967295 ->
    0 <= tl <= 4294967295 ->
    0 <= th <= 4294967295 ->
    th * 4294967296 + tl = u0 * m ->
    (m + 4294967296) * u1 + (4294967296 - 1 - r) =
      18446744073709551616 - 1 - u0 ->
    4294967296 - 1 - r < u1 ->
    r + th < 4294967296 ->
    (m + 4294967296) * (4294967296 * u1 + u0) <=
      79228162514264337593543950336 - 1 /\
    79228162514264337593543950336 - 1 <
      (m + 4294967296 + 1) * (4294967296 * u1 + u0).
Proof.
  intros.
  assert (Hrem:
    79228162514264337593543950336 - 1 -
    (m + 4294967296) * (4294967296 * u1 + u0) =
    4294967296 * (4294967296 - r - th) - tl - 1) by nia.
  assert (Hrem_nonneg:
    0 <= 4294967296 * (4294967296 - r - th) - tl - 1) by nia.
  assert (Hrem_lt_div:
    4294967296 * (4294967296 - r - th) - tl - 1 <
    4294967296 * u1 + u0) by nia.
  split; nia.
Qed.

Lemma mpn_invert_final_carry_one_lt:
  forall u0 u1 m r tl th r2,
    0 <= u0 <= 4294967295 -> u0 > 0 ->
    0 <= u1 <= 4294967295 -> 2147483648 <= u1 ->
    0 <= m <= 4294967295 ->
    0 <= r <= 4294967295 ->
    0 <= tl <= 4294967295 ->
    0 <= th <= 4294967295 ->
    th * 4294967296 + tl = u0 * m ->
    (m + 4294967296) * u1 + (4294967296 - 1 - r) =
      18446744073709551616 - 1 - u0 ->
    4294967296 - 1 - r < u1 ->
    r2 = r + th - 4294967296 ->
    0 <= r2 < 4294967296 ->
    r2 < u1 ->
    1 <= m /\
    (m - 1 + 4294967296) * (4294967296 * u1 + u0) <=
      79228162514264337593543950336 - 1 /\
    79228162514264337593543950336 - 1 <
      (m - 1 + 4294967296 + 1) * (4294967296 * u1 + u0).
Proof.
  intros.
  assert (Hrem1:
    79228162514264337593543950336 - 1 -
    (m - 1 + 4294967296) * (4294967296 * u1 + u0) =
    4294967296 * (u1 - r2) + u0 - tl - 1) by nia.
  assert (Hrem1_nonneg:
    0 <= 4294967296 * (u1 - r2) + u0 - tl - 1) by nia.
  assert (Hrem1_lt_div:
    4294967296 * (u1 - r2) + u0 - tl - 1 <
    4294967296 * u1 + u0) by nia.
  repeat split; nia.
Qed.

Lemma mpn_invert_final_carry_one_eq:
  forall u0 u1 m r tl th r2,
    0 <= u0 <= 4294967295 -> u0 > 0 ->
    0 <= u1 <= 4294967295 -> 2147483648 <= u1 ->
    0 <= m <= 4294967295 ->
    0 <= r <= 4294967295 ->
    0 <= tl <= 4294967295 ->
    0 <= th <= 4294967295 ->
    th * 4294967296 + tl = u0 * m ->
    (m + 4294967296) * u1 + (4294967296 - 1 - r) =
      18446744073709551616 - 1 - u0 ->
    4294967296 - 1 - r < u1 ->
    r2 = r + th - 4294967296 ->
    0 <= r2 < 4294967296 ->
    r2 = u1 ->
    tl <= u0 ->
    1 <= m /\
    (m - 1 + 4294967296) * (4294967296 * u1 + u0) <=
      79228162514264337593543950336 - 1 /\
    79228162514264337593543950336 - 1 <
      (m - 1 + 4294967296 + 1) * (4294967296 * u1 + u0).
Proof.
  intros u0 u1 m r tl th r2 Hu0 Hu0pos Hu1 Hu1half Hm Hr Htl Hth
    Hmul Hinv Hrem Hr2eq Hr2range Hr2u Htle.
  assert (Htl_lt: tl < u0).
  { destruct (Z_lt_ge_dec tl u0) as [Hlt | Hge]; [lia |].
    assert (Htl_eq: tl = u0) by lia.
    assert (Hprod:
      (m - 1 + 4294967296) * (4294967296 * u1 + u0) =
      79228162514264337593543950336) by nia.
    assert (Hfac_bounds:
      4294967296 < m - 1 + 4294967296 < 8589934592) by nia.
    assert (Hdiv:
      Z.divide (m - 1 + 4294967296)
        79228162514264337593543950336).
    { exists (4294967296 * u1 + u0). nia. }
    exfalso.
    eapply mpn_invert_no_uint_factor_between_32_33; eauto. }
  assert (Hrem1:
    79228162514264337593543950336 - 1 -
    (m - 1 + 4294967296) * (4294967296 * u1 + u0) =
    4294967296 * (u1 - r2) + u0 - tl - 1) by nia.
  assert (Hrem1_nonneg:
    0 <= 4294967296 * (u1 - r2) + u0 - tl - 1) by nia.
  assert (Hrem1_lt_div:
    4294967296 * (u1 - r2) + u0 - tl - 1 <
    4294967296 * u1 + u0) by nia.
  repeat split; nia.
Qed.

Lemma mpn_invert_final_carry_two:
  forall u0 u1 m r tl th r2,
    0 <= u0 <= 4294967295 -> u0 > 0 ->
    0 <= u1 <= 4294967295 -> 2147483648 <= u1 ->
    0 <= m <= 4294967295 ->
    0 <= r <= 4294967295 ->
    0 <= tl <= 4294967295 ->
    0 <= th <= 4294967295 ->
    th * 4294967296 + tl = u0 * m ->
    (m + 4294967296) * u1 + (4294967296 - 1 - r) =
      18446744073709551616 - 1 - u0 ->
    4294967296 - 1 - r < u1 ->
    r2 = r + th - 4294967296 ->
    0 <= r2 < 4294967296 ->
    (r2 > u1 \/ (r2 = u1 /\ tl > u0)) ->
    2 <= m /\
    (m - 2 + 4294967296) * (4294967296 * u1 + u0) <=
      79228162514264337593543950336 - 1 /\
    79228162514264337593543950336 - 1 <
      (m - 2 + 4294967296 + 1) * (4294967296 * u1 + u0).
Proof.
  intros.
  assert (Hrem2:
    79228162514264337593543950336 - 1 -
    (m - 2 + 4294967296) * (4294967296 * u1 + u0) =
    4294967296 * (2 * u1 - r2) + 2 * u0 - tl - 1) by nia.
  assert (Hrem2_nonneg:
    0 <= 4294967296 * (2 * u1 - r2) + 2 * u0 - tl - 1) by nia.
  assert (Hrem2_lt_div:
    4294967296 * (2 * u1 - r2) + 2 * u0 - tl - 1 <
    4294967296 * u1 + u0) by nia.
  repeat split; nia.
Qed.

Lemma mpn_invert_second_p_bounds:
  forall u qh r,
    0 <= qh < 65536 ->
    0 <= r < u ->
    (qh + 65536) * u + r = Z.pow 65536 3 - 1 ->
    0 <= Z.shiftr r 16 * qh + r < 4294967296.
Proof.
  intros u qh r Hqh Hr Heq.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 16) with 65536.
  change (65536 ^ 3) with 281474976710656 in Heq.
  split.
  - apply Z.add_nonneg_nonneg; [| lia].
    apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia].
  - assert (Hdiv: 65536 * (r / 65536) <= r).
    { pose proof (Z.div_mod r 65536 ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound r 65536 ltac:(lia)) as Hmod.
      nia. }
    assert (Hrawmul:
              65536 * (r / 65536 * qh + r) <= (qh + 65536) * r).
    { replace (65536 * (r / 65536 * qh + r))
        with (qh * (65536 * (r / 65536)) + 65536 * r) by ring.
      replace ((qh + 65536) * r)
        with (qh * r + 65536 * r) by ring.
      nia. }
    assert ((qh + 65536) * r < (qh + 65536) * u) by nia.
    assert ((qh + 65536) * u < 281474976710656) by nia.
    assert (65536 * (r / 65536 * qh + r) < 65536 * 4294967296) by nia.
    nia.
Qed.

Lemma mpn_invert_second_p_unsigned:
  forall u qh r,
    0 <= qh < 65536 ->
    0 <= r < u ->
    (qh + 65536) * u + r = Z.pow 65536 3 - 1 ->
    unsigned_last_nbits
      (unsigned_last_nbits (Z.shiftr r 16 * qh) 32 + r) 32 =
    Z.shiftr r 16 * qh + r.
Proof.
  intros u qh r Hqh Hr Heq.
  pose proof (mpn_invert_second_p_bounds u qh r Hqh Hr Heq) as Hraw.
  assert (Hprod: 0 <= Z.shiftr r 16 * qh < 4294967296).
  { split.
    - rewrite Z.shiftr_div_pow2 by lia.
      apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia].
    - assert (Z.shiftr r 16 * qh <= Z.shiftr r 16 * qh + r) by lia.
      lia. }
  assert (Hprod_pow: 0 <= Z.shiftr r 16 * qh < 2 ^ 32).
  { change (2 ^ 32) with 4294967296.
    exact Hprod. }
  rewrite (unsigned_last_nbits_eq (Z.shiftr r 16 * qh) 32 Hprod_pow).
  apply unsigned_last_nbits_eq.
  change (2 ^ 32) with 4294967296.
  exact Hraw.
Qed.

Lemma mpn_invert_second_ql_bounds:
  forall p,
    0 <= p < 4294967296 ->
    0 <= Z.shiftr p 16 + 1 <= 65536.
Proof.
  intros p Hp.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 16) with 65536.
  split.
  - apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia | lia].
  - assert (p / 65536 < 65536).
    { apply Z.div_lt_upper_bound; lia. }
    lia.
Qed.

Lemma mpn_invert_second_ql_unsigned:
  forall p,
    0 <= p < 4294967296 ->
    unsigned_last_nbits (Z.shiftr p 16 + 1) 32 =
    Z.shiftr p 16 + 1.
Proof.
  intros p Hp.
  apply unsigned_last_nbits_eq.
  change (2 ^ 32) with 4294967296.
  pose proof (mpn_invert_second_ql_bounds p Hp) as Hq.
  lia.
Qed.

Lemma mpn_invert_second_rout_mod:
  forall r ql u,
    unsigned_last_nbits
      (unsigned_last_nbits (unsigned_last_nbits (Z.shiftl r 16) 32 + 65535) 32 -
       unsigned_last_nbits (ql * u) 32) 32 =
    (65536 * r + 65535 - ql * u) mod 4294967296.
Proof.
  intros r ql u.
  unfold unsigned_last_nbits.
  change (2 ^ 32) with 4294967296.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 16) with 65536.
  replace ((r * 65536 mod 4294967296 + 65535) mod 4294967296)
    with ((r * 65536 + 65535) mod 4294967296).
  2: {
    symmetry.
    rewrite <- (Z.mod_small 65535 4294967296) at 1 by lia.
    rewrite <- Z.add_mod by lia.
    reflexivity.
  }
  rewrite <- Zminus_mod by lia.
  replace (r * 65536 + 65535 - ql * u)
    with (65536 * r + 65535 - ql * u) by ring.
  reflexivity.
Qed.

Lemma mpn_invert_second_low_mask:
  forall p,
    0 <= p < 4294967296 ->
    Z.land 4294967295 (Z.shiftl p 16) = (p mod 65536) * 65536.
Proof.
  intros p Hp.
  rewrite Z.land_comm.
  replace 4294967295 with (Z.ones 32) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite shiftl_16_mod_low by lia.
  apply Z.mod_small.
  pose proof (Z.mod_pos_bound p 65536 ltac:(lia)) as Hmod.
  nia.
Qed.

Lemma mpn_invert_second_core:
  forall qh u r e f ql d t,
    0 <= qh < 65536 ->
    0 <= e < 65536 ->
    0 <= f < 65536 ->
    0 <= d < 65536 ->
    1 <= ql <= 65536 ->
    0 <= r < u ->
    r = e * 65536 + f ->
    e * (qh + 65536) + f = (ql - 1) * 65536 + d ->
    (qh + 65536) * u + r = 65536 ^ 3 - 1 ->
    t = 65536 * r + 65535 - ql * u ->
    0 - 4294967296 < t < 4294967296 /\
    (t < 0 -> d * 65536 <= t + 4294967296) /\
    (0 <= t ->
       0 <= qh * 65536 + ql <= 4294967295 /\
       0 <= t < 2 * u /\
       (qh * 65536 + ql + 4294967296) * u + t = 4294967296 ^ 2 - 1).
Proof.
  intros qh u r e f ql d t Hqh He Hf Hd Hql Hr Hrdef Hpdef Heq Ht.
  change (65536 ^ 3) with 281474976710656 in Heq.
  change (4294967296 ^ 2) with 18446744073709551616.
  split.
  - nia.
  - split.
    + intros; nia.
    + intros; repeat split; nia.
Qed.

Lemma mpn_invert_second_no_adjust_simpl:
  forall u qh r p ql rout,
    0 <= qh < 65536 ->
    0 <= r < u ->
    (qh + 65536) * u + r = 65536 ^ 3 - 1 ->
    0 <= p <= 4294967295 ->
    0 <= ql <= 65536 ->
    p = Z.shiftr r 16 * qh + r ->
    ql = Z.shiftr p 16 + 1 ->
    rout = unsigned_last_nbits
      (unsigned_last_nbits (unsigned_last_nbits (Z.shiftl r 16) 32 + 65535) 32 -
       unsigned_last_nbits (ql * u) 32) 32 ->
    rout < Z.land 4294967295 (Z.shiftl p 16) ->
    0 <= qh * 65536 + ql <= 4294967295 /\
    0 <= rout < 2 * u /\
    (qh * 65536 + ql + 4294967296) * u + rout = 4294967296 ^ 2 - 1.
Proof.
  intros u qh r p ql rout Hqh Hr Heq Hp Hql Hpdef Hqldef Hrout Hbranch.
  set (e := Z.shiftr r 16).
  set (f := r mod 65536).
  set (d := p mod 65536).
  set (t := 65536 * r + 65535 - ql * u).
  assert (He: 0 <= e < 65536).
  { subst e. rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 16) with 65536.
    split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; nia. }
  assert (Hf: 0 <= f < 65536).
  { subst f. apply Z.mod_pos_bound; lia. }
  assert (Hd: 0 <= d < 65536).
  { subst d. apply Z.mod_pos_bound; lia. }
  assert (Hqlpos: 1 <= ql <= 65536).
  { subst ql. rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 16) with 65536.
    assert (0 <= p / 65536) by (apply Z.div_pos; lia).
    assert (p / 65536 < 65536) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  assert (Hrdef: r = e * 65536 + f).
  { subst e f. rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 16) with 65536.
    pose proof (Z.div_mod r 65536 ltac:(lia)) as Hdm.
    nia. }
  assert (Hpdef2: e * (qh + 65536) + f = (ql - 1) * 65536 + d).
  { subst e f d.
    rewrite Z.shiftr_div_pow2 in Hpdef by lia.
    rewrite Z.shiftr_div_pow2 in Hqldef by lia.
    change (2 ^ 16) with 65536 in Hpdef, Hqldef.
    pose proof (Z.div_mod r 65536 ltac:(lia)) as Hrdm.
    pose proof (Z.div_mod p 65536 ltac:(lia)) as Hpdm.
    nia. }
  pose proof (mpn_invert_second_core qh u r e f ql d t
                Hqh He Hf Hd Hqlpos Hr Hrdef Hpdef2 Heq eq_refl)
    as [Ht_range [Hneg Hnonneg]].
  assert (Hrout_mod: rout = t mod 4294967296).
  { subst rout t.
    apply mpn_invert_second_rout_mod. }
  assert (Hmask: Z.land 4294967295 (Z.shiftl p 16) = d * 65536).
  { subst d. apply mpn_invert_second_low_mask. lia. }
  assert (Ht_nonneg: 0 <= t).
  { destruct (Z_lt_ge_dec t 0) as [Htneg|Htge]; [|lia].
    assert (Hrout_eq: rout = t + 4294967296).
    { rewrite Hrout_mod.
      symmetry.
      apply Z.mod_unique with (q := -1).
      - left; lia.
      - ring. }
    rewrite Hrout_eq in Hbranch.
    rewrite Hmask in Hbranch.
    pose proof (Hneg Htneg).
    lia. }
  pose proof (Hnonneg Ht_nonneg) as [Hm [Ht2 Heq2]].
  rewrite Hrout_mod.
  rewrite Z.mod_small by lia.
  split; [exact Hm | split; [exact Ht2 | exact Heq2]].
Qed.

Lemma mpn_invert_second_nonneg_plus_upper:
  forall qh u r e f ql d t,
    0 <= qh < 65536 ->
    0 <= e < 65536 ->
    0 <= f < 65536 ->
    0 <= d < 65536 ->
    1 <= ql <= 65536 ->
    0 <= r < u ->
    r = e * 65536 + f ->
    e * (qh + 65536) + f = (ql - 1) * 65536 + d ->
    (qh + 65536) * u + r = 65536 ^ 3 - 1 ->
    t = 65536 * r + 65535 - ql * u ->
    2147483648 <= u ->
    t < 4294967296 ->
    0 <= t ->
    d * 65536 <= t ->
    t + u < 4294967296.
Proof.
  intros.
  change (65536 ^ 3) with 281474976710656 in *.
  nia.
Qed.

Lemma mpn_invert_second_neg_plus_bounds:
  forall qh u r e f ql d t,
    0 <= qh < 65536 ->
    0 <= e < 65536 ->
    0 <= f < 65536 ->
    0 <= d < 65536 ->
    1 <= ql <= 65536 ->
    0 <= r < u ->
    r = e * 65536 + f ->
    e * (qh + 65536) + f = (ql - 1) * 65536 + d ->
    (qh + 65536) * u + r = 65536 ^ 3 - 1 ->
    t = 65536 * r + 65535 - ql * u ->
    2147483648 <= u ->
    -4294967296 < t ->
    t < 0 ->
    0 <= t + u < 4294967296.
Proof.
  intros.
  change (65536 ^ 3) with 281474976710656 in *.
  nia.
Qed.

Lemma mpn_invert_second_adjust_simpl:
  forall u qh r p ql rout,
    0 <= qh < 65536 ->
    2147483648 <= u ->
    0 <= r < u ->
    (qh + 65536) * u + r = 65536 ^ 3 - 1 ->
    0 <= p <= 4294967295 ->
    0 <= ql <= 65536 ->
    p = Z.shiftr r 16 * qh + r ->
    ql = Z.shiftr p 16 + 1 ->
    rout = unsigned_last_nbits
      (unsigned_last_nbits (unsigned_last_nbits (Z.shiftl r 16) 32 + 65535) 32 -
       unsigned_last_nbits (ql * u) 32) 32 ->
    rout >= Z.land 4294967295 (Z.shiftl p 16) ->
    0 <= qh * 65536 + (ql - 1) <= 4294967295 /\
    0 <= unsigned_last_nbits (rout + u) 32 < 2 * u /\
    (qh * 65536 + (ql - 1) + 4294967296) * u +
      unsigned_last_nbits (rout + u) 32 = 4294967296 ^ 2 - 1 /\
    1 <= ql.
Proof.
  intros u qh r p ql rout Hqh Hu_half Hr Heq Hp Hql Hpdef Hqldef Hrout Hbranch.
  set (e := Z.shiftr r 16).
  set (f := r mod 65536).
  set (d := p mod 65536).
  set (t := 65536 * r + 65535 - ql * u).
  assert (He: 0 <= e < 65536).
  { subst e. rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 16) with 65536.
    split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; nia. }
  assert (Hf: 0 <= f < 65536).
  { subst f. apply Z.mod_pos_bound; lia. }
  assert (Hd: 0 <= d < 65536).
  { subst d. apply Z.mod_pos_bound; lia. }
  assert (Hqlpos: 1 <= ql <= 65536).
  { subst ql. rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 16) with 65536.
    assert (0 <= p / 65536) by (apply Z.div_pos; lia).
    assert (p / 65536 < 65536) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  assert (Hrdef: r = e * 65536 + f).
  { subst e f. rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 16) with 65536.
    pose proof (Z.div_mod r 65536 ltac:(lia)) as Hdm.
    nia. }
  assert (Hpdef2: e * (qh + 65536) + f = (ql - 1) * 65536 + d).
  { subst e f d.
    rewrite Z.shiftr_div_pow2 in Hpdef by lia.
    rewrite Z.shiftr_div_pow2 in Hqldef by lia.
    change (2 ^ 16) with 65536 in Hpdef, Hqldef.
    pose proof (Z.div_mod r 65536 ltac:(lia)) as Hrdm.
    pose proof (Z.div_mod p 65536 ltac:(lia)) as Hpdm.
    nia. }
  pose proof (mpn_invert_second_core qh u r e f ql d t
                Hqh He Hf Hd Hqlpos Hr Hrdef Hpdef2 Heq eq_refl)
    as [Ht_range [_ _]].
  assert (Hrout_mod: rout = t mod 4294967296).
  { subst rout t.
    apply mpn_invert_second_rout_mod. }
  assert (Hmask: Z.land 4294967295 (Z.shiftl p 16) = d * 65536).
  { subst d. apply mpn_invert_second_low_mask. lia. }
  assert (Hadj_eq:
    (qh * 65536 + (ql - 1) + 4294967296) * u + (t + u) =
    4294967296 ^ 2 - 1).
  { change (4294967296 ^ 2) with 18446744073709551616.
    change (65536 ^ 3) with 281474976710656 in Heq.
    nia. }
  assert (Hplus_bounds: 0 <= t + u < 4294967296).
  { destruct (Z_lt_ge_dec t 0) as [Htneg | Htge].
    - exact (mpn_invert_second_neg_plus_bounds
        qh u r e f ql d t Hqh He Hf Hd Hqlpos Hr Hrdef Hpdef2
        Heq eq_refl Hu_half ltac:(lia) Htneg).
    - split; [lia|].
      apply (mpn_invert_second_nonneg_plus_upper
        qh u r e f ql d t Hqh He Hf Hd Hqlpos Hr Hrdef Hpdef2
        Heq eq_refl Hu_half ltac:(lia) ltac:(lia)).
      rewrite Hrout_mod in Hbranch.
      rewrite Z.mod_small in Hbranch by lia.
      rewrite Hmask in Hbranch.
      lia. }
  assert (Hrplus_eq:
    unsigned_last_nbits (rout + u) 32 = t + u).
  { destruct (Z_lt_ge_dec t 0) as [Htneg | Htge].
    - assert (Hrout_eq: rout = t + 4294967296).
      { rewrite Hrout_mod.
        symmetry.
        apply Z.mod_unique with (q := -1).
        + left; lia.
        + ring. }
      rewrite Hrout_eq.
      replace (t + 4294967296 + u) with (t + u + 4294967296) by ring.
      rewrite (unsigned_last_nbits_overflow_32 (t + u + 4294967296)).
      * ring.
      * lia.
    - assert (Hrout_eq: rout = t).
      { rewrite Hrout_mod.
        apply Z.mod_small.
        lia. }
      rewrite Hrout_eq.
      apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      exact Hplus_bounds. }
  rewrite Hrplus_eq.
  repeat split; try lia.
Qed.

Lemma mpz_tdiv_q_2exp_zero_by_limb_bound :
  forall z size bit,
    0 <= bit ->
    Zabs size <= bit ÷ 32 ->
    0 <= z < UINT_MOD ^ Zabs size ->
    Z.quot z (2 ^ bit) = 0.
Proof.
  intros z size bit Hbit Hsize Hbound.
  rewrite Z.quot_div_nonneg.
  2: lia.
  2: { apply Z.pow_pos_nonneg; lia. }
  apply Z.div_small.
  split; [lia|].
  destruct Hbound as [_ Hupper].
  assert (Hpow_le : UINT_MOD ^ Zabs size <= 2 ^ bit).
  {
    change UINT_MOD with (2 ^ 32).
    rewrite <- Z.pow_mul_r by lia.
    apply Z.pow_le_mono_r.
    - lia.
    - pose proof (Z.quot_rem bit 32 ltac:(lia)) as Hqr.
      pose proof (Z.rem_bound_pos bit 32 ltac:(lia) ltac:(lia)) as Hrem.
      nia.
  }
  lia.
Qed.

Lemma mpz_tdiv_q_2exp_suffix_shift0 :
  forall l z bit k n,
    0 <= bit ->
    k = bit ÷ 32 ->
    bit % 32 = 0 ->
    0 < n ->
    Zlength l = n + k ->
    list_to_Z UINT_MOD l = z ->
    list_within_bound UINT_MOD l ->
    last l 1 >= 1 ->
    list_to_Z UINT_MOD (sublist k (k + n) l) = Z.quot z (2 ^ bit) /\
    is_compact_Z UINT_MOD (Z.quot z (2 ^ bit)) n.
Proof.
  intros l z bit k n Hbit Hk Hrem Hn Hlen Hval Hbound Hlast.
  assert (Hk_nonneg : 0 <= k).
  { subst k. apply Z.quot_pos; lia. }
  assert (Hbit_decomp : bit = 32 * k).
  { subst k. pose proof (Z.quot_rem bit 32 ltac:(lia)) as Hqr. lia. }
  assert (Hpow_eq : 2 ^ bit = UINT_MOD ^ k).
  {
    rewrite Hbit_decomp.
    change UINT_MOD with (2 ^ 32).
    rewrite Z.pow_mul_r by lia.
    reflexivity.
  }
  assert (Hsplit : l = sublist 0 k l ++ sublist k (Zlength l) l).
  {
    rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
    rewrite (sublist_split 0 (Zlength l) k l); try lia.
    reflexivity.
  }
  assert (Hbound_split :
    list_within_bound UINT_MOD (sublist 0 k l ++ sublist k (Zlength l) l)).
  { rewrite <- Hsplit. exact Hbound. }
  pose proof (list_to_Z_split UINT_MOD UINT_MOD_pos
    (sublist 0 k l) (sublist k (Zlength l) l) Hbound_split) as [_ Hquot].
  rewrite Zlength_sublist in Hquot by lia.
  replace (k - 0) with k in Hquot by lia.
  assert (Htail_eq : sublist k (k + n) l = sublist k (Zlength l) l).
  { f_equal. lia. }
  assert (Hsuffix_val_div :
    list_to_Z UINT_MOD (sublist k (k + n) l) = z / UINT_MOD ^ k).
  {
    rewrite Htail_eq, Hquot.
    rewrite <- Hsplit.
    rewrite Hval.
    reflexivity.
  }
  pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l Hbound Hlast) as Hz_bounds.
  rewrite Hlen in Hz_bounds.
  rewrite Hval in Hz_bounds.
  assert (Hz_nonneg : 0 <= z).
  {
    rewrite <- Hval.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l Hbound) as Hzb.
    lia.
  }
  assert (Hquot_eq : z ÷ 2 ^ bit = z / UINT_MOD ^ k).
  {
    rewrite Hpow_eq.
    apply Z.quot_div_nonneg.
    - lia.
    - apply Z.pow_pos_nonneg; unfold UINT_MOD; lia.
  }
  assert (Hcompact : is_compact_Z UINT_MOD (z ÷ 2 ^ bit) n).
  {
    rewrite Hquot_eq.
    apply is_compact_Z_from_bounds.
    - unfold UINT_MOD; lia.
    - lia.
    - right.
      assert (Hpow_low :
        UINT_MOD ^ k * UINT_MOD ^ (n - 1) = UINT_MOD ^ (n + k - 1)).
      { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      assert (Hpow_high :
        UINT_MOD ^ k * UINT_MOD ^ n = UINT_MOD ^ (n + k)).
      { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      split; [lia|].
      split.
      + apply Z.div_le_lower_bound.
        * apply Z.pow_pos_nonneg; unfold UINT_MOD; lia.
        * rewrite Hpow_low. lia.
      + apply Z.div_lt_upper_bound.
        * apply Z.pow_pos_nonneg; unfold UINT_MOD; lia.
        * rewrite Hpow_high. lia.
  }
  split.
  - rewrite Hsuffix_val_div.
    symmetry.
    exact Hquot_eq.
  - exact Hcompact.
Qed.

Lemma mpz_tdiv_q_2exp_rshift_high_zero :
  forall l l_out z bit_pre limb bit qn retval,
    0 <= bit_pre ->
    limb = bit_pre ÷ 32 ->
    bit = bit_pre % 32 ->
    1 <= bit < 32 ->
    0 < qn ->
    Zlength l = qn + limb ->
    list_to_Z UINT_MOD l = z ->
    list_within_bound UINT_MOD l ->
    last l 1 >= 1 ->
    Zlength l_out = qn ->
    list_within_bound UINT_MOD l_out ->
    Znth (qn - 1) l_out 0 = 0 ->
    retval = unsigned_last_nbits (Znth limb l 0 * 2 ^ (32 - bit)) 32 ->
    list_to_Z UINT_MOD (sublist limb (limb + qn) l) =
      list_to_Z UINT_MOD l_out * 2 ^ bit + retval ÷ 2 ^ (32 - bit) ->
    list_to_Z UINT_MOD l_out = Z.quot z (2 ^ bit_pre) /\
    is_compact_Z UINT_MOD (Z.quot z (2 ^ bit_pre)) (qn - 1).
Proof.
  intros l l_out z bit_pre limb bit qn retval Hbitpre Hlimb Hbit Hbit_rng
    Hqn Hlen Hval Hbound Hlast Hout_len Hout_bound Hout_high Hretval Hrshift.
  assert (Hlimb_nonneg : 0 <= limb).
  { subst limb. apply Z.quot_pos; lia. }
  assert (Hbit_decomp : bit_pre = 32 * limb + bit).
  {
    subst limb bit.
    pose proof (Z.quot_rem bit_pre 32 ltac:(lia)) as Hqr.
    lia.
  }
  assert (Hpow_eq : 2 ^ bit_pre = UINT_MOD ^ limb * 2 ^ bit).
  {
    rewrite Hbit_decomp.
    rewrite Z.pow_add_r by lia.
    replace (2 ^ (32 * limb)) with (UINT_MOD ^ limb).
    2: {
      change UINT_MOD with (2 ^ 32).
      rewrite Z.pow_mul_r by lia.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hsplit : l = sublist 0 limb l ++ sublist limb (Zlength l) l).
  {
    rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
    rewrite (sublist_split 0 (Zlength l) limb l); try lia.
    reflexivity.
  }
  assert (Hbound_split :
    list_within_bound UINT_MOD (sublist 0 limb l ++ sublist limb (Zlength l) l)).
  { rewrite <- Hsplit. exact Hbound. }
  pose proof (list_to_Z_split UINT_MOD UINT_MOD_pos
    (sublist 0 limb l) (sublist limb (Zlength l) l) Hbound_split) as [_ Hquot].
  rewrite Zlength_sublist in Hquot by lia.
  replace (limb - 0) with limb in Hquot by lia.
  assert (Htail_eq : sublist limb (limb + qn) l = sublist limb (Zlength l) l).
  { f_equal. lia. }
  assert (Hz_nonneg : 0 <= z).
  {
    rewrite <- Hval.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l Hbound) as Hzb.
    lia.
  }
  assert (Hsuffix_div : list_to_Z UINT_MOD (sublist limb (limb + qn) l) = z / UINT_MOD ^ limb).
  {
    rewrite Htail_eq, Hquot.
    rewrite <- Hsplit.
    rewrite Hval.
    reflexivity.
  }
  assert (Hretval_bound : 0 <= retval ÷ 2 ^ (32 - bit) < 2 ^ bit).
  {
    assert (Hretval_range : 0 <= retval < UINT_MOD).
    {
      rewrite Hretval.
      pose proof (unsigned_Lastnbits_range
        (Znth limb l 0 * 2 ^ (32 - bit)) 32 ltac:(lia)) as Hr.
      change (2 ^ 32) with UINT_MOD in Hr.
      exact Hr.
    }
    rewrite Z.quot_div_nonneg.
    2: lia.
    2: { apply Z.pow_pos_nonneg; lia. }
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound.
      + apply Z.pow_pos_nonneg; lia.
      + rewrite <- Z.pow_add_r by lia.
        replace (32 - bit + bit) with 32 by lia.
        change (2 ^ 32) with UINT_MOD.
        lia.
  }
  assert (Hsuffix_quot : z / UINT_MOD ^ limb / 2 ^ bit = list_to_Z UINT_MOD l_out).
  {
    rewrite <- Hsuffix_div.
    rewrite Hrshift.
    rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
    replace ((retval ÷ 2 ^ (32 - bit)) / 2 ^ bit) with 0.
    - lia.
    - symmetry. apply Z.div_small. exact Hretval_bound.
  }
  assert (Hquot_eq : z ÷ 2 ^ bit_pre = list_to_Z UINT_MOD l_out).
  {
    rewrite Z.quot_div_nonneg.
    2: lia.
    2: { apply Z.pow_pos_nonneg; lia. }
    rewrite Hpow_eq.
    rewrite <- Z.div_div.
    2: { apply Z.pow_nonzero; unfold UINT_MOD; lia. }
    2: { apply Z.pow_pos_nonneg; lia. }
    exact Hsuffix_quot.
  }
  assert (Hout_prefix_val :
    list_to_Z UINT_MOD (sublist 0 (qn - 1) l_out) = list_to_Z UINT_MOD l_out).
  {
    apply list_to_Z_high_zero_prefix; try assumption; lia.
  }
  assert (Hcompact : is_compact_Z UINT_MOD (z ÷ 2 ^ bit_pre) (qn - 1)).
  {
    rewrite Hquot_eq.
    destruct (Z.eq_dec (qn - 1) 0) as [Hsize0 | Hsize_pos].
    - apply is_compact_Z_from_bounds.
      + unfold UINT_MOD; lia.
      + lia.
      + left.
        split; [assumption|].
        rewrite <- Hout_prefix_val.
        rewrite Hsize0.
        rewrite Zsublist_nil by lia.
        reflexivity.
    - apply is_compact_Z_from_bounds.
      + unfold UINT_MOD; lia.
      + lia.
      + right.
        assert (Hout_upper :
          list_to_Z UINT_MOD l_out < UINT_MOD ^ (qn - 1)).
        {
          rewrite <- Hout_prefix_val.
          pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos
            (sublist 0 (qn - 1) l_out)) as Hb.
          specialize (Hb (list_within_bound_sublist UINT_MOD l_out 0 (qn - 1)
            ltac:(lia) ltac:(lia) Hout_bound)).
          rewrite Zlength_sublist in Hb by lia.
          replace (qn - 1 - 0) with (qn - 1) in Hb by lia.
          lia.
        }
        assert (Hz_bounds := list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l Hbound Hlast).
        rewrite Hlen in Hz_bounds.
        rewrite Hval in Hz_bounds.
        assert (Hden_pos : 0 < UINT_MOD ^ limb * 2 ^ bit).
        {
          apply Z.mul_pos_pos.
          - apply Z.pow_pos_nonneg; unfold UINT_MOD; lia.
          - apply Z.pow_pos_nonneg; lia.
        }
        assert (Hpow_step :
          UINT_MOD ^ (qn + limb - 2) * UINT_MOD = UINT_MOD ^ (qn + limb - 1)).
        {
          replace (qn + limb - 1) with (qn + limb - 2 + 1) by lia.
          rewrite Z.pow_add_r by lia.
          rewrite Z.pow_1_r.
          reflexivity.
        }
        assert (Hbit_le_uint : 2 ^ bit <= UINT_MOD).
        {
          change UINT_MOD with (2 ^ 32).
          apply Z.pow_le_mono_r; lia.
        }
        assert (Hlow_mul :
          UINT_MOD ^ (qn - 2) * (UINT_MOD ^ limb * 2 ^ bit) <= z).
        {
          replace (UINT_MOD ^ (qn - 2) * (UINT_MOD ^ limb * 2 ^ bit))
            with ((UINT_MOD ^ (qn - 2) * UINT_MOD ^ limb) * 2 ^ bit) by ring.
          rewrite <- Z.pow_add_r by (try unfold UINT_MOD; lia).
          replace (qn - 2 + limb) with (qn + limb - 2) by lia.
          assert (0 <= UINT_MOD ^ (qn + limb - 2)).
          { apply Z.pow_nonneg; unfold UINT_MOD; lia. }
          assert (Hmul_le :
            UINT_MOD ^ (qn + limb - 2) * 2 ^ bit <=
            UINT_MOD ^ (qn + limb - 2) * UINT_MOD) by nia.
          rewrite Hpow_step in Hmul_le.
          lia.
        }
        split; [lia|].
        split.
        * rewrite <- Hquot_eq.
          rewrite Z.quot_div_nonneg.
          2: lia.
          2: { apply Z.pow_pos_nonneg; lia. }
          rewrite Hpow_eq.
          apply Z.div_le_lower_bound.
          -- exact Hden_pos.
          -- replace (qn - 1 - 1) with (qn - 2) by lia.
             replace (UINT_MOD ^ limb * 2 ^ bit * UINT_MOD ^ (qn - 2))
               with (UINT_MOD ^ (qn - 2) * (UINT_MOD ^ limb * 2 ^ bit)) by ring.
             exact Hlow_mul.
        * exact Hout_upper.
  }
  split; [symmetry; exact Hquot_eq | exact Hcompact].
Qed.

Lemma mpz_tdiv_q_2exp_rshift_nonzero :
  forall l l_out z bit_pre limb bit qn retval,
    0 <= bit_pre ->
    limb = bit_pre ÷ 32 ->
    bit = bit_pre % 32 ->
    1 <= bit < 32 ->
    0 < qn ->
    Zlength l = qn + limb ->
    list_to_Z UINT_MOD l = z ->
    list_within_bound UINT_MOD l ->
    last l 1 >= 1 ->
    Zlength l_out = qn ->
    list_within_bound UINT_MOD l_out ->
    Znth (qn - 1) l_out 0 <> 0 ->
    retval = unsigned_last_nbits (Znth limb l 0 * 2 ^ (32 - bit)) 32 ->
    list_to_Z UINT_MOD (sublist limb (limb + qn) l) =
      list_to_Z UINT_MOD l_out * 2 ^ bit + retval ÷ 2 ^ (32 - bit) ->
    list_to_Z UINT_MOD l_out = Z.quot z (2 ^ bit_pre) /\
    is_compact_Z UINT_MOD (Z.quot z (2 ^ bit_pre)) qn.
Proof.
  intros l l_out z bit_pre limb bit qn retval Hbitpre Hlimb Hbit Hbit_rng
    Hqn Hlen Hval Hbound Hlast Hout_len Hout_bound Hout_high_nonzero Hretval Hrshift.
  assert (Hlimb_nonneg : 0 <= limb).
  { subst limb. apply Z.quot_pos; lia. }
  assert (Hbit_decomp : bit_pre = 32 * limb + bit).
  {
    subst limb bit.
    pose proof (Z.quot_rem bit_pre 32 ltac:(lia)) as Hqr.
    lia.
  }
  assert (Hpow_eq : 2 ^ bit_pre = UINT_MOD ^ limb * 2 ^ bit).
  {
    rewrite Hbit_decomp.
    rewrite Z.pow_add_r by lia.
    replace (2 ^ (32 * limb)) with (UINT_MOD ^ limb).
    2: {
      change UINT_MOD with (2 ^ 32).
      rewrite Z.pow_mul_r by lia.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hsplit : l = sublist 0 limb l ++ sublist limb (Zlength l) l).
  {
    rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
    rewrite (sublist_split 0 (Zlength l) limb l); try lia.
    reflexivity.
  }
  assert (Hbound_split :
    list_within_bound UINT_MOD (sublist 0 limb l ++ sublist limb (Zlength l) l)).
  { rewrite <- Hsplit. exact Hbound. }
  pose proof (list_to_Z_split UINT_MOD UINT_MOD_pos
    (sublist 0 limb l) (sublist limb (Zlength l) l) Hbound_split) as [_ Hquot].
  rewrite Zlength_sublist in Hquot by lia.
  replace (limb - 0) with limb in Hquot by lia.
  assert (Htail_eq : sublist limb (limb + qn) l = sublist limb (Zlength l) l).
  { f_equal. lia. }
  assert (Hz_nonneg : 0 <= z).
  {
    rewrite <- Hval.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l Hbound) as Hzb.
    lia.
  }
  assert (Hsuffix_div : list_to_Z UINT_MOD (sublist limb (limb + qn) l) = z / UINT_MOD ^ limb).
  {
    rewrite Htail_eq, Hquot.
    rewrite <- Hsplit.
    rewrite Hval.
    reflexivity.
  }
  assert (Hretval_bound : 0 <= retval ÷ 2 ^ (32 - bit) < 2 ^ bit).
  {
    assert (Hretval_range : 0 <= retval < UINT_MOD).
    {
      rewrite Hretval.
      pose proof (unsigned_Lastnbits_range
        (Znth limb l 0 * 2 ^ (32 - bit)) 32 ltac:(lia)) as Hr.
      change (2 ^ 32) with UINT_MOD in Hr.
      exact Hr.
    }
    rewrite Z.quot_div_nonneg.
    2: lia.
    2: { apply Z.pow_pos_nonneg; lia. }
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound.
      + apply Z.pow_pos_nonneg; lia.
      + rewrite <- Z.pow_add_r by lia.
        replace (32 - bit + bit) with 32 by lia.
        change (2 ^ 32) with UINT_MOD.
        lia.
  }
  assert (Hsuffix_quot : z / UINT_MOD ^ limb / 2 ^ bit = list_to_Z UINT_MOD l_out).
  {
    rewrite <- Hsuffix_div.
    rewrite Hrshift.
    rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
    replace ((retval ÷ 2 ^ (32 - bit)) / 2 ^ bit) with 0.
    - lia.
    - symmetry. apply Z.div_small. exact Hretval_bound.
  }
  assert (Hquot_eq : z ÷ 2 ^ bit_pre = list_to_Z UINT_MOD l_out).
  {
    rewrite Z.quot_div_nonneg.
    2: lia.
    2: { apply Z.pow_pos_nonneg; lia. }
    rewrite Hpow_eq.
    rewrite <- Z.div_div.
    2: { apply Z.pow_nonzero; unfold UINT_MOD; lia. }
    2: { apply Z.pow_pos_nonneg; lia. }
    exact Hsuffix_quot.
  }
  assert (Hout_last : last l_out 1 >= 1).
  {
    assert (Hidx : 0 <= qn - 1 < Zlength l_out) by lia.
    pose proof (list_within_bound_Znth_bound UINT_MOD l_out (qn - 1) Hidx Hout_bound) as Hdigit.
    assert (Hout_nonempty : l_out <> nil).
    { destruct l_out; [rewrite Zlength_nil in Hout_len; lia | discriminate]. }
    rewrite (list_last_to_Znth l_out) by exact Hout_nonempty.
    rewrite Hout_len.
    lia.
  }
  assert (Hcompact : is_compact_Z UINT_MOD (z ÷ 2 ^ bit_pre) qn).
  {
    rewrite Hquot_eq.
    apply is_compact_Z_from_bounds.
    - unfold UINT_MOD; lia.
    - lia.
    - right.
      split; [lia|].
      pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l_out Hout_bound Hout_last) as Hbounds.
      rewrite Hout_len in Hbounds.
      exact Hbounds.
  }
  split; [symmetry; exact Hquot_eq | exact Hcompact].
Qed.
