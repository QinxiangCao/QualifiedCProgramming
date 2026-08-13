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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_gcd_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_gcd_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_gcd_entail_wit_1 : mpz_gcd_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr (Zabs zu) (Zabs size) ltac:(lia)).
  prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr_2 (Zabs zv) (Zabs size_2) ltac:(lia)).
  Intros.
  sep_apply (store_Z_from_fields u_pre ptr size cap zu PreH6 PreH5).
  sep_apply (store_Z_from_fields v_pre ptr_2 size_2 cap_2 zv PreH3 PreH2).
  prop_apply (one_store_Z_implies_headroom u_pre zu).
  Intros.
  assert (Hzu_nonzero : zu <> 0) by lia.
  match goal with
  | Hhead : mpz_one_limb_headroom zu |- _ =>
      pose proof
        (mpz_one_limb_headroom_gcd_l zu zv Hzu_nonzero Hhead)
        as Hgcd_headroom
  end.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try lia.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_2_1 : mpz_gcd_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact ptr (Zabs rv) (Zabs size_3) cap_3).
  prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr (Zabs rv) (Zabs size_3) ltac:(lia)).
  Intros.
  unfold mpz_div_qr_math in PreH4.
  destruct PreH4 as [PreH4 | [PreH4 | PreH4]].
  2,3: unfold mpz_div_qr_math_floor, mpz_div_qr_math_ceil,
      GMP_DIV_TRUNC, GMP_DIV_FLOOR, GMP_DIV_CEIL in PreH4; lia.
  destruct PreH4 as [Hzd [_ [Hdiv [Hrem Hsign]]]].
  assert (Hrvnz : rv <> 0).
  { intro Hzero. subst rv. change (Zabs 0) with 0 in H. lia. }
  assert (Hrvpos : rv > 0).
  { destruct Hsign as [Hzero | Hsame].
    - contradiction.
    - unfold same_sign in Hsame. lia.
  }
  assert (Hrvlt : rv < odd).
  { rewrite Z.abs_eq in Hrem by lia.
    rewrite Z.abs_eq in Hrem by lia.
    lia.
  }
  assert (Hgcd_next :
    Zgcd zu zv = 2 ^ retval_3 * Zgcd rv odd).
  { rewrite Z.gcd_comm.
    apply (gmp_gcd_make_odd_tdiv_left_ge
      zv zu odd_2 odd qv rv retval_4 retval_3);
      try lia; try assumption. }
  assert (Hfit_next :
    mpz_mul_2exp_fits (Zgcd rv odd) retval_3).
  { eapply (mpz_one_limb_headroom_mul_2exp_fits
      (Zgcd rv odd) retval_3 (Zgcd zu zv)).
    - pose proof (Z.gcd_nonneg rv odd).
      destruct (Z.eq_dec (Zgcd rv odd) 0) as [Hg0 | Hg0]; [|lia].
      apply Z.gcd_eq_0_l in Hg0.
      lia.
    - lia.
    - exact Hgcd_next.
    - exact PreH23. }
  Exists odd rv.
  split_pure_spatial.
  - sep_apply (store_Z_from_fields retval ptr size_3 cap_3 rv PreH3 PreH2).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_2_2 : mpz_gcd_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact ptr (Zabs rv) (Zabs size_3) cap_3).
  prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr (Zabs rv) (Zabs size_3) ltac:(lia)).
  Intros.
  unfold mpz_div_qr_math in PreH4.
  destruct PreH4 as [PreH4 | [PreH4 | PreH4]].
  2,3: unfold mpz_div_qr_math_floor, mpz_div_qr_math_ceil,
      GMP_DIV_TRUNC, GMP_DIV_FLOOR, GMP_DIV_CEIL in PreH4; lia.
  destruct PreH4 as [Hzd [_ [Hdiv [Hrem Hsign]]]].
  assert (Hrvnz : rv <> 0).
  { intro Hzero. subst rv. change (Zabs 0) with 0 in H. lia. }
  assert (Hrvpos : rv > 0).
  { destruct Hsign as [Hzero | Hsame].
    - contradiction.
    - unfold same_sign in Hsame. lia.
  }
  assert (Hrvlt : rv < odd).
  { rewrite Z.abs_eq in Hrem by lia.
    rewrite Z.abs_eq in Hrem by lia.
    lia.
  }
  assert (Hgcd_next :
    Zgcd zu zv = 2 ^ retval_3 * Zgcd rv odd).
  { rewrite Z.gcd_comm.
    apply (gmp_gcd_make_odd_tdiv_right_ge
      zv zu odd_2 odd qv rv retval_3 retval_4);
      try lia; try assumption. }
  assert (Hfit_next :
    mpz_mul_2exp_fits (Zgcd rv odd) retval_3).
  { eapply (mpz_one_limb_headroom_mul_2exp_fits
      (Zgcd rv odd) retval_3 (Zgcd zu zv)).
    - pose proof (Z.gcd_nonneg rv odd).
      destruct (Z.eq_dec (Zgcd rv odd) 0) as [Hg0 | Hg0]; [|lia].
      apply Z.gcd_eq_0_l in Hg0.
      lia.
    - lia.
    - exact Hgcd_next.
    - exact PreH23. }
  Exists odd rv.
  split_pure_spatial.
  - sep_apply (store_Z_from_fields retval ptr size_3 cap_3 rv PreH3 PreH2).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_2_3 : mpz_gcd_entail_wit_2_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact ptr (Zabs rv) (Zabs size_3) cap_3).
  prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr (Zabs rv) (Zabs size_3) ltac:(lia)).
  Intros.
  unfold mpz_div_qr_math in PreH4.
  destruct PreH4 as [PreH4 | [PreH4 | PreH4]].
  2,3: unfold mpz_div_qr_math_floor, mpz_div_qr_math_ceil,
      GMP_DIV_TRUNC, GMP_DIV_FLOOR, GMP_DIV_CEIL in PreH4; lia.
  destruct PreH4 as [Hzd [_ [Hdiv [Hrem Hsign]]]].
  assert (Hrvnz : rv <> 0).
  { intro Hzero. subst rv. change (Zabs 0) with 0 in H. lia. }
  assert (Hrvpos : rv > 0).
  { destruct Hsign as [Hzero | Hsame].
    - contradiction.
    - unfold same_sign in Hsame. lia.
  }
  assert (Hrvlt : rv < odd_2).
  { rewrite Z.abs_eq in Hrem by lia.
    rewrite Z.abs_eq in Hrem by lia.
    lia.
  }
  assert (Hgcd_next :
    Zgcd zu zv = 2 ^ retval_3 * Zgcd rv odd_2).
  { apply (gmp_gcd_make_odd_tdiv_right_ge
      zu zv odd odd_2 qv rv retval_3 retval_4);
      try lia; try assumption. }
  assert (Hfit_next :
    mpz_mul_2exp_fits (Zgcd rv odd_2) retval_3).
  { eapply (mpz_one_limb_headroom_mul_2exp_fits
      (Zgcd rv odd_2) retval_3 (Zgcd zu zv)).
    - pose proof (Z.gcd_nonneg rv odd_2).
      destruct (Z.eq_dec (Zgcd rv odd_2) 0) as [Hg0 | Hg0]; [|lia].
      apply Z.gcd_eq_0_l in Hg0.
      lia.
    - lia.
    - exact Hgcd_next.
    - exact PreH23. }
  Exists odd_2 rv.
  split_pure_spatial.
  - sep_apply (store_Z_from_fields retval ptr size_3 cap_3 rv PreH3 PreH2).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_2_4 : mpz_gcd_entail_wit_2_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact ptr (Zabs rv) (Zabs size_3) cap_3).
  prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr (Zabs rv) (Zabs size_3) ltac:(lia)).
  Intros.
  unfold mpz_div_qr_math in PreH4.
  destruct PreH4 as [PreH4 | [PreH4 | PreH4]].
  2,3: unfold mpz_div_qr_math_floor, mpz_div_qr_math_ceil,
      GMP_DIV_TRUNC, GMP_DIV_FLOOR, GMP_DIV_CEIL in PreH4; lia.
  destruct PreH4 as [Hzd [_ [Hdiv [Hrem Hsign]]]].
  assert (Hrvnz : rv <> 0).
  { intro Hzero. subst rv. change (Zabs 0) with 0 in H. lia. }
  assert (Hrvpos : rv > 0).
  { destruct Hsign as [Hzero | Hsame].
    - contradiction.
    - unfold same_sign in Hsame. lia.
  }
  assert (Hrvlt : rv < odd_2).
  { rewrite Z.abs_eq in Hrem by lia.
    rewrite Z.abs_eq in Hrem by lia.
    lia.
  }
  assert (Hgcd_next :
    Zgcd zu zv = 2 ^ retval_3 * Zgcd rv odd_2).
  { apply (gmp_gcd_make_odd_tdiv_left_ge
      zu zv odd odd_2 qv rv retval_4 retval_3);
      try lia; try assumption. }
  assert (Hfit_next :
    mpz_mul_2exp_fits (Zgcd rv odd_2) retval_3).
  { eapply (mpz_one_limb_headroom_mul_2exp_fits
      (Zgcd rv odd_2) retval_3 (Zgcd zu zv)).
    - pose proof (Z.gcd_nonneg rv odd_2).
      destruct (Z.eq_dec (Zgcd rv odd_2) 0) as [Hg0 | Hg0]; [|lia].
      apply Z.gcd_eq_0_l in Hg0.
      lia.
    - lia.
    - exact Hgcd_next.
    - exact PreH23. }
  Exists odd_2 rv.
  split_pure_spatial.
  - sep_apply (store_Z_from_fields retval ptr size_3 cap_3 rv PreH3 PreH2).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_4_1 : mpz_gcd_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_bound ptr (Zabs odd) (Zabs size)).
  Intros.
  assert (Hgcd_next :
    Zgcd zu zv = 2 ^ gz_v * Zgcd tv_v_2 odd).
  { rewrite PreH19.
    f_equal.
    rewrite PreH11.
    rewrite gmp_gcd_mul_pow2_odd_l; try lia.
    apply Z.gcd_comm. }
  assert (Hfit_next :
    mpz_mul_2exp_fits (Zgcd tv_v_2 odd) gz_v).
  { replace (Zgcd tv_v_2 odd) with (Zgcd tu_v_2 tv_v_2).
    - exact PreH18.
    - rewrite PreH11.
      rewrite (Z.gcd_comm tv_v_2 odd).
      symmetry.
      rewrite gmp_gcd_mul_pow2_odd_l; lia. }
  assert (Hodd_bound : odd <= UINT_MAX).
  { match goal with
    | Hbound : 0 <= Zabs odd < UINT_MOD ^ Zabs size |- _ =>
        change UINT_MOD with 4294967296 in Hbound;
        rewrite PreH1 in Hbound;
        change (Zabs 1) with 1 in Hbound;
        change (4294967296 ^ 1) with 4294967296 in Hbound
    end.
    change UINT_MAX with 4294967295.
    lia. }
  Exists odd tv_v_2.
  split_pure_spatial.
  - sep_apply (store_Z_from_fields tv ptr size cap odd PreH3 PreH2).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_4_2 : mpz_gcd_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_bound ptr (Zabs tv_v_2) (Zabs size)).
  Intros.
  assert (Hgcd_next :
    Zgcd zu zv = 2 ^ gz_v * Zgcd odd tv_v_2).
  { rewrite PreH19.
    f_equal.
    rewrite PreH11.
    rewrite gmp_gcd_mul_pow2_odd_l; lia. }
  assert (Hfit_next :
    mpz_mul_2exp_fits (Zgcd odd tv_v_2) gz_v).
  { replace (Zgcd odd tv_v_2) with (Zgcd tu_v_2 tv_v_2).
    - exact PreH18.
    - rewrite PreH11.
      symmetry.
      rewrite gmp_gcd_mul_pow2_odd_l; lia. }
  assert (Htv_bound : tv_v_2 <= UINT_MAX).
  { match goal with
    | Hbound : 0 <= Zabs tv_v_2 < UINT_MOD ^ Zabs size |- _ =>
        change UINT_MOD with 4294967296 in Hbound;
        rewrite PreH1 in Hbound;
        change (Zabs 1) with 1 in Hbound;
        change (4294967296 ^ 1) with 4294967296 in Hbound
    end.
    change UINT_MAX with 4294967295.
    lia. }
  Exists tv_v_2 odd.
  split_pure_spatial.
  - sep_apply (store_Z_from_fields tv ptr size cap tv_v_2 PreH3 PreH2).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_5 : mpz_gcd_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z at 2.
  Intros gptr gsize gcap.
  prop_apply (store_int_range (&(g_pre # "__mpz_struct" ->ₛ"_mp_alloc")) gcap).
  Intros.
  Exists gptr gsize gcap tu_v_2 tv_v_2 qv_2 rv_2.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial.
    all: try assumption; try reflexivity.
    all: change Int.min_signed with (-2147483648) in *.
    all: change Int.max_signed with 2147483647 in *.
    all: pose proof (Z.abs_nonneg gsize).
    all: lia.
Qed.

Lemma proof_of_mpz_gcd_entail_wit_6 : mpz_gcd_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z_read0 at 1.
  Intros tptr tsize tcap.
  unfold mpd_store_Z_compact_read0 at 1.
  Intros tdata.
  destruct H1 as [Htval [Htlast [Htbound Htsize]]].
  unfold store_Z at 1.
  Intros vptr vsize vcap.
  unfold mpd_store_Z_compact at 1.
  Intros vdata.
  destruct H3 as [Hvval [Hvlast Hvbound]].
  rename H4 into Hvsize_abs.
  unfold mpz_div_qr_math in PreH5.
  destruct PreH5 as [Hdivmath | [Hdivmath | Hdivmath]].
  2,3: unfold mpz_div_qr_math_floor, mpz_div_qr_math_ceil,
      GMP_DIV_TRUNC, GMP_DIV_FLOOR, GMP_DIV_CEIL in Hdivmath; lia.
  destruct Hdivmath as [Hzd [_ [Hdiv [Hrem Hsign]]]].
  assert (Hrv_nonneg : 0 <= rv).
  {
    destruct Hsign as [Hrvzero | Hrvsign].
    - subst rv. lia.
    - destruct Hrvsign as [[Hrvge _] | [Hrvlt Htu_lt]]; lia.
  }
  assert (Hrv_lt_tv : rv < tv_v).
  {
    rewrite Z.abs_eq in Hrem by lia.
    rewrite Z.abs_eq in Hrem by lia.
    exact Hrem.
  }
  assert (Hrv_bound : Zabs rv <= 4294967295).
  {
    rewrite Z.abs_eq by lia.
    eapply Z.le_trans.
    - apply Z.lt_le_incl. exact Hrv_lt_tv.
    - exact PreH9.
  }
  pose proof (mpd_read0_data_uint_props tdata (Zabs rv) (Zabs tsize)
    Htval Htlast Htbound Htsize ltac:(split; [apply Z.abs_nonneg | exact Hrv_bound]))
    as [Htlen [Htbound0 [Htval0 Htznth]]].
  assert (Hvcompact : is_compact_Z UINT_MOD (Zabs tv_v) (Zlength vdata)).
  {
    unfold is_compact_Z.
    exists vdata.
    split; [exact Hvval |].
    split; [reflexivity |].
    split; [exact Hvbound | exact Hvlast].
  }
  assert (Hvcompact1 : is_compact_Z UINT_MOD (Zabs tv_v) 1).
  {
    apply (is_compact_Z_from_bounds UINT_MOD UINT_MOD_pos); [lia |].
    right.
    split; [lia |].
    change (1 - 1) with 0.
    change (UINT_MOD ^ 0) with 1.
    rewrite Z.abs_eq by lia.
    unfold UINT_MOD in *; lia.
  }
  assert (Hzabstv_pos : Zabs tv_v > 0) by (rewrite Z.abs_eq by lia; lia).
  pose proof (is_compact_Z_same_value_size_eq (Zabs tv_v) (Zlength vdata) 1
    Hzabstv_pos Hvcompact Hvcompact1) as Hvlen1.
  assert (Hsize1 : vsize = 1).
  {
    assert (Hsize_nonneg : 0 <= vsize).
    { unfold same_sign in H2. lia. }
    rewrite Z.abs_eq in Hvsize_abs by exact Hsize_nonneg.
    rewrite Hvlen1 in Hvsize_abs.
    lia.
  }
  destruct vdata as [|vd0 vdtail].
  - rewrite Zlength_nil in Hvlen1. discriminate.
  - assert (Htail0 : Zlength vdtail = 0).
    {
      rewrite Zlength_cons in Hvlen1.
      unfold Z.succ in Hvlen1.
      lia.
    }
    apply Zlength_nil_inv in Htail0.
    subst vdtail.
    rewrite list_to_Z_single in Hvval.
    subst vd0.
    assert (Hgcd_rem : Zgcd tu_v tv_v = Zgcd (Zabs rv) (Zabs tv_v)).
    {
      assert (Hmod : tu_v mod tv_v = rv).
      {
        rewrite Hdiv.
        replace (qv * tv_v + rv) with (rv + qv * tv_v) by ring.
        rewrite Z.mod_add by lia.
        apply Z.mod_small. lia.
      }
      rewrite Z.gcd_comm.
      rewrite <- (Z.gcd_mod tu_v tv_v) by lia.
      rewrite Hmod.
      rewrite Z.gcd_comm.
      rewrite Z.abs_eq by lia.
      rewrite Z.abs_eq by lia.
      apply Z.gcd_comm.
    }
    rewrite Hsize1.
    change (Zabs 1) with 1.
    change (Zlength (Zabs tv_v :: nil)) with 1.
    unfold mpd_store_list.
    rewrite Hvlen1.
    Exists z_callee__mp_alloc.
    Exists vptr.
    Exists vcap.
    Exists tptr.
    Exists tcap.
    Exists tsize.
    Exists (Zabs tv_v :: nil).
    Exists tdata.
    Exists (Zabs rv).
    Exists gsize_2.
    Exists gcap_2.
    Exists 1.
    Exists (Zabs tv_v).
    Exists retval.
    split_pure_spatial.
    + rewrite Htsize.
      normalize.
      repeat cancel.
    + repeat split_pures; dump_pre_spatial;
        try assumption; try reflexivity; try lia.
      all: try solve [rewrite PreH2; reflexivity].
      all: try solve [
        change (Znth 0 (Zabs tv_v :: nil) 0) with (Zabs tv_v);
        rewrite Z.abs_eq by lia; lia
      ].
      all: try solve [rewrite Htznth; apply Z.abs_nonneg].
      all: try solve [rewrite Htznth; exact Hrv_bound].
      all: try solve [exact Htlast].
      all: try solve [exact Htbound].
      all: try solve [exact Hvbound].
      all: try solve [rewrite Htval, Htznth; reflexivity].
      all: try solve [rewrite list_to_Z_single; reflexivity].
      all: try solve [
        rewrite PreH12;
        rewrite Htznth;
        change (Znth 0 (Zabs tv_v :: nil) 0) with (Zabs tv_v);
        rewrite Hgcd_rem;
        rewrite Z.abs_eq by lia;
        rewrite Z.abs_eq by lia;
        reflexivity
      ].
      all: try solve [
        rewrite Htznth;
        change (Znth 0 (Zabs tv_v :: nil) 0) with (Zabs tv_v);
        rewrite <- Hgcd_rem;
        exact PreH11
      ].
      rewrite <- Hgcd_rem.
      exact PreH11.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_7 : mpz_gcd_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (UIntArray.full_to_seg tptr_2 (Zmax (Zabs tsize_2) 1) (mpd_read0_data tdata_2)).
  sep_apply_l_atomic (UIntArray.seg_split_to_seg tptr_2 0 1 (Zmax (Zabs tsize_2) 1)
    (mpd_read0_data tdata_2)).
  - dump_pre_spatial.
    split; [lia | apply Z.le_max_r].
  - replace (1 - 0) with 1 by lia.
    replace (Zmax (Zabs tsize_2) 1 - 0) with (Zmax (Zabs tsize_2) 1) by lia.
    sep_apply_l_atomic (UIntArray.full_to_seg vptr_2 1 vdata_2).
    sep_apply_l_atomic (mpd_store_Z_compact_undef_tail_to_undef_split
      gp (Zabs old) (Zabs gsize_2) 1 (Z.max 1 gcap_2)).
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      transitivity gcap_2; [exact PreH9 | apply Z.le_max_r].
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      transitivity 1; [lia | apply Z.le_max_l].
    + rewrite (UIntArray.undef_full_unfold gp 0 (@nil Z)) by lia.
      replace (0 + 1) with 1 by lia.
      replace (gp + 0 * sizeof(UINT)) with gp by lia.
      rewrite (UIntArray.undef_seg_empty gp 1).
      replace (sublist 0 1 vdata_2) with vdata_2.
      2:{
        rewrite <- PreH18.
        rewrite sublist_self; reflexivity.
      }
      Exists g__mp_alloc_2 vptr_2 vcap_2 tptr_2 tcap_2 tsize_2
        vdata_2 tdata_2 rem_2 gsize_2 gcap_2 vsize_2 tv_val_2 g__mp_d_2.
      split_pure_spatial.
      * Intros.
        replace (sublist 0 1 vdata_2) with vdata_2.
        2:{
          rewrite <- PreH18.
          rewrite sublist_self; reflexivity.
        }
        normalize.
        repeat cancel.
      * repeat split_pures; dump_pre_spatial;
          try lia; try assumption; try reflexivity.
        all: try solve [rewrite PreH15; lia].
        all: try solve [rewrite PreH16; lia].
        all: try solve [rewrite PreH22, PreH15; reflexivity].
        all: try solve [rewrite PreH23, PreH16; reflexivity].
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_8_1 : mpz_gcd_entail_wit_8_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists odd (tv_v_2 - odd).
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try lia; try assumption; try reflexivity.
    + replace (Zgcd (tv_v_2 - odd) odd) with (Zgcd tu_v_2 tv_v_2).
      * exact PreH18.
      * rewrite PreH11.
        rewrite gmp_gcd_mul_pow2_odd_l; try lia; try assumption.
        rewrite <- (Z.gcd_sub_diag_r odd tv_v_2).
        rewrite (Z.gcd_comm odd (tv_v_2 - odd)).
        reflexivity.
    + rewrite PreH19.
      f_equal.
      rewrite PreH11.
      rewrite gmp_gcd_mul_pow2_odd_l; try lia; try assumption.
      rewrite <- (Z.gcd_sub_diag_r odd tv_v_2).
      rewrite (Z.gcd_comm odd (tv_v_2 - odd)).
      reflexivity.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_8_2 : mpz_gcd_entail_wit_8_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists tv_v_2 (odd - tv_v_2).
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try lia; try assumption; try reflexivity.
    + replace (Zgcd (odd - tv_v_2) tv_v_2) with (Zgcd tu_v_2 tv_v_2).
      * exact PreH18.
      * rewrite PreH11.
        rewrite gmp_gcd_mul_pow2_odd_l; try lia; try assumption.
        rewrite Z.gcd_comm.
        rewrite <- (Z.gcd_sub_diag_r tv_v_2 odd).
        rewrite (Z.gcd_comm tv_v_2 (odd - tv_v_2)).
        reflexivity.
    + rewrite PreH19.
      f_equal.
      rewrite PreH11.
      rewrite gmp_gcd_mul_pow2_odd_l; try lia; try assumption.
      rewrite Z.gcd_comm.
      rewrite <- (Z.gcd_sub_diag_r tv_v_2 odd).
      rewrite (Z.gcd_comm tv_v_2 (odd - tv_v_2)).
      reflexivity.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_9_1 : mpz_gcd_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact ptr (Zabs rv) (Zabs size_3) cap_3).
  rewrite PreH1.
  change (Zabs 0) with 0.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs rv)).
  Intros.
  assert (Hrv0 : rv = 0) by lia.
  assert (Hgcd_final : Zgcd zu zv = 2 ^ retval_3 * odd).
  {
    unfold mpz_div_qr_math in PreH4.
    destruct PreH4 as [Hmath | [Hmath | Hmath]].
    - destruct Hmath as [Hd [Hmode [Hdiv [Hrem Hsign]]]].
      rewrite Z.gcd_comm.
      rewrite (gmp_gcd_make_odd_tdiv_left_ge zv zu odd_2 odd qv rv retval_4 retval_3); try lia; try assumption.
      subst rv.
      rewrite Z.gcd_0_l.
      rewrite Z.abs_eq by lia.
      ring.
    - unfold mpz_div_qr_math_floor, GMP_DIV_FLOOR, GMP_DIV_TRUNC in Hmath; lia.
    - unfold mpz_div_qr_math_ceil, GMP_DIV_CEIL, GMP_DIV_TRUNC in Hmath; lia.
  }
  assert (Hfit : mpz_mul_2exp_fits odd retval_3).
  {
    eapply (mpz_one_limb_headroom_mul_2exp_fits odd retval_3 (Zgcd zu zv)).
    - lia.
    - lia.
    - rewrite Hgcd_final. ring.
    - exact PreH23.
  }
  assert (Hgcd_post : Zgcd zu zv = odd * 2 ^ retval_3) by (rewrite Hgcd_final; ring).
  subst rv.
  Exists old 0 odd.
  split_pure_spatial.
  - cancel (store_Z g_pre odd).
    cancel (store_Z retval_2 old).
    cancel (store_Z u_pre zu).
    cancel (store_Z v_pre zv).
    unfold store_Z at 1.
    Exists ptr 0 cap_3.
    split_pure_spatial.
    + cancel (mpd_store_Z_compact UINT_MOD ptr (Zabs 0) 0).
      cancel (UIntArray.undef_seg ptr 0 cap_3).
      cancel (&(retval # "__mpz_struct" ->ₛ "_mp_size") # Int |-> 0).
      cancel (&(retval # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap_3).
      cancel (&(retval # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr).
    + repeat split_pures; dump_pre_spatial;
        try lia; try apply same_sign_refl.
  - repeat split_pures; dump_pre_spatial;
      try lia; try assumption; try reflexivity.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_9_2 : mpz_gcd_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH1.
  change (Zabs 0) with 0.
  sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact ptr (Zabs rv) 0 cap_3).
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs rv)).
  Intros.
  assert (Hrv0 : rv = 0) by lia.
  assert (Hgcd_final : Zgcd zu zv = 2 ^ retval_3 * odd).
  {
    unfold mpz_div_qr_math in PreH4.
    destruct PreH4 as [Hmath | [Hmath | Hmath]].
    - destruct Hmath as [Hd [Hmode [Hdiv [Hrem Hsign]]]].
      rewrite Z.gcd_comm.
      rewrite (gmp_gcd_make_odd_tdiv_right_ge zv zu odd_2 odd qv rv retval_3 retval_4); try lia; try assumption.
      subst rv.
      rewrite Z.gcd_0_l.
      rewrite Z.abs_eq by lia.
      ring.
    - unfold mpz_div_qr_math_floor, GMP_DIV_FLOOR, GMP_DIV_TRUNC in Hmath; lia.
    - unfold mpz_div_qr_math_ceil, GMP_DIV_CEIL, GMP_DIV_TRUNC in Hmath; lia.
  }
  assert (Hfit : mpz_mul_2exp_fits odd retval_3).
  {
    eapply (mpz_one_limb_headroom_mul_2exp_fits odd retval_3 (Zgcd zu zv)).
    - lia.
    - lia.
    - rewrite Hgcd_final. ring.
    - exact PreH23.
  }
  subst rv.
  Exists old 0 odd.
  split_pure_spatial.
  - cancel (store_Z g_pre odd).
    cancel (store_Z retval_2 old).
    cancel (store_Z u_pre zu).
    cancel (store_Z v_pre zv).
    unfold store_Z at 1.
    Exists ptr 0 cap_3.
    split_pure_spatial.
    + cancel (mpd_store_Z_compact UINT_MOD ptr (Zabs 0) 0).
      cancel (UIntArray.undef_seg ptr 0 cap_3).
      cancel (&(retval # "__mpz_struct" ->ₛ "_mp_size") # Int |-> 0).
      cancel (&(retval # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap_3).
      cancel (&(retval # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr).
    + repeat split_pures; dump_pre_spatial;
        try lia; try apply same_sign_refl.
  - repeat split_pures; dump_pre_spatial;
      try lia; try assumption; try reflexivity.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_9_3 : mpz_gcd_entail_wit_9_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH1.
  change (Zabs 0) with 0.
  sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact ptr (Zabs rv) 0 cap_3).
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs rv)).
  Intros.
  assert (Hrv0 : rv = 0) by lia.
  assert (Hgcd_final : Zgcd zu zv = 2 ^ retval_3 * odd_2).
  {
    unfold mpz_div_qr_math in PreH4.
    destruct PreH4 as [Hmath | [Hmath | Hmath]].
    - destruct Hmath as [Hd [Hmode [Hdiv [Hrem Hsign]]]].
      rewrite (gmp_gcd_make_odd_tdiv_right_ge zu zv odd odd_2 qv rv retval_3 retval_4); try lia; try assumption.
      subst rv.
      rewrite Z.gcd_0_l.
      rewrite Z.abs_eq by lia.
      ring.
    - unfold mpz_div_qr_math_floor, GMP_DIV_FLOOR, GMP_DIV_TRUNC in Hmath; lia.
    - unfold mpz_div_qr_math_ceil, GMP_DIV_CEIL, GMP_DIV_TRUNC in Hmath; lia.
  }
  assert (Hfit : mpz_mul_2exp_fits odd_2 retval_3).
  {
    eapply (mpz_one_limb_headroom_mul_2exp_fits odd_2 retval_3 (Zgcd zu zv)).
    - lia.
    - lia.
    - rewrite Hgcd_final. ring.
    - exact PreH23.
  }
  subst rv.
  Exists old 0 odd_2.
  split_pure_spatial.
  - cancel (store_Z g_pre odd_2).
    cancel (store_Z retval_2 old).
    cancel (store_Z u_pre zu).
    cancel (store_Z v_pre zv).
    unfold store_Z at 1.
    Exists ptr 0 cap_3.
    split_pure_spatial.
    + cancel (mpd_store_Z_compact UINT_MOD ptr (Zabs 0) 0).
      cancel (UIntArray.undef_seg ptr 0 cap_3).
      cancel (&(retval # "__mpz_struct" ->ₛ "_mp_size") # Int |-> 0).
      cancel (&(retval # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap_3).
      cancel (&(retval # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr).
    + repeat split_pures; dump_pre_spatial;
        try lia; try apply same_sign_refl.
  - repeat split_pures; dump_pre_spatial;
      try lia; try assumption; try reflexivity.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_9_4 : mpz_gcd_entail_wit_9_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact ptr (Zabs rv) (Zabs size_3) cap_3).
  rewrite PreH1.
  change (Zabs 0) with 0.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs rv)).
  Intros.
  assert (Hrv0 : rv = 0) by lia.
  assert (Hgcd_final : Zgcd zu zv = 2 ^ retval_3 * odd_2).
  {
    unfold mpz_div_qr_math in PreH4.
    destruct PreH4 as [Hmath | [Hmath | Hmath]].
    - destruct Hmath as [Hd [Hmode [Hdiv [Hrem Hsign]]]].
      rewrite (gmp_gcd_make_odd_tdiv_left_ge zu zv odd odd_2 qv rv retval_4 retval_3); try lia; try assumption.
      subst rv.
      rewrite Z.gcd_0_l.
      rewrite Z.abs_eq by lia.
      ring.
    - unfold mpz_div_qr_math_floor, GMP_DIV_FLOOR, GMP_DIV_TRUNC in Hmath; lia.
    - unfold mpz_div_qr_math_ceil, GMP_DIV_CEIL, GMP_DIV_TRUNC in Hmath; lia.
  }
  assert (Hfit : mpz_mul_2exp_fits odd_2 retval_3).
  {
    eapply (mpz_one_limb_headroom_mul_2exp_fits odd_2 retval_3 (Zgcd zu zv)).
    - exact PreH12.
    - lia.
    - rewrite Hgcd_final. ring.
    - exact PreH23.
  }
  assert (Hgcd_post : Zgcd zu zv = odd_2 * 2 ^ retval_3) by (rewrite Hgcd_final; ring).
  subst rv.
  assert (Hsame_zero : same_sign 0 0) by apply same_sign_refl.
  Exists old 0 odd_2.
  split_pure_spatial.
  - normalize.
    repeat cancel.
    unfold store_Z at 1.
    Exists ptr 0 cap_3.
    split_pure_spatial.
    + change (Zabs 0) with 0.
      repeat cancel.
    + repeat split_pures; dump_pre_spatial;
        try lia; try assumption; try apply same_sign_refl.
  - repeat split_pures; dump_pre_spatial;
      try lia; try assumption; try reflexivity.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_9_5_split_goal_1 :
  mpz_gcd_entail_wit_9_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hgcd_inner : Z.gcd tu_v tv_v = odd).
  {
    rewrite PreH7, <- PreH2.
    rewrite gmp_gcd_mul_pow2_odd_l; try lia; try assumption.
    rewrite Z.gcd_diag_nonneg; lia.
  }
  rewrite PreH15, Hgcd_inner, PreH2; ring.
Qed.

Lemma proof_of_mpz_gcd_entail_wit_9_5_split_goal_2 :
  mpz_gcd_entail_wit_9_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hgcd_inner : Z.gcd tu_v tv_v = odd).
  {
    rewrite PreH7, <- PreH2.
    rewrite gmp_gcd_mul_pow2_odd_l; try lia; try assumption.
    rewrite Z.gcd_diag_nonneg; lia.
  }
  rewrite <- PreH2.
  rewrite <- Hgcd_inner.
  exact PreH14.
Qed.

Lemma proof_of_mpz_gcd_entail_wit_9_5 : mpz_gcd_entail_wit_9_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_gcd_entail_wit_9_5_split_goal_1.
  - Goal_apply proof_of_mpz_gcd_entail_wit_9_5_split_goal_2.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_9_6 : mpz_gcd_entail_wit_9_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  change (0 - 0) with 0 in PreH2.
  assert (Htv_head : Znth 0 (sublist 0 1 vdata) 0 = tv_val).
  {
    rewrite Znth_sublist by lia.
    exact PreH18.
  }
  rewrite Htv_head in PreH2.
  assert (Hgpos : Zgcd (Znth 0 (sublist 0 1 (mpd_read0_data tdata)) 0) tv_val > 0).
  {
    pose proof (Z.gcd_nonneg (Znth 0 (sublist 0 1 (mpd_read0_data tdata)) 0) tv_val) as Hg_nonneg.
    assert (Zgcd (Znth 0 (sublist 0 1 (mpd_read0_data tdata)) 0) tv_val <> 0).
    {
      intros Hg0.
      pose proof Z.gcd_eq_0_r (Znth 0 (sublist 0 1 (mpd_read0_data tdata)) 0) tv_val.
      lia.
    }
    lia.
  }
  assert (False) by lia.
  contradiction.
Qed. 

Lemma proof_of_mpz_gcd_entail_wit_9_7 : mpz_gcd_entail_wit_9_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  change (0 - 0) with 0 in PreH2.
  assert (Ht_head : Znth 0 (sublist 0 1 (mpd_read0_data tdata)) 0 = rem).
  {
    rewrite Znth_sublist by (unfold mpd_read0_data; destruct tdata; simpl; lia).
    exact PreH17.
  }
  assert (Htv_head : Znth 0 (sublist 0 1 vdata) 0 = tv_val).
  {
    rewrite Znth_sublist by lia.
    exact PreH18.
  }
  assert (Hretval_gcd : retval = Zgcd rem tv_val).
  { rewrite PreH2, Ht_head, Htv_head. reflexivity. }
  assert (Hgcd_post : Zgcd zu zv = retval * 2 ^ gz_v).
  { rewrite PreH27, Hretval_gcd; ring. }
  assert (Hfit : mpz_mul_2exp_fits retval gz_v).
  { rewrite Hretval_gcd. exact PreH26. }
  pose proof (mpd_read0_signed_abs_same_sign rem tsize tdata
    PreH24 PreH21 PreH22 PreH19 PreH13) as [Ht_abs Ht_sign].
  prop_apply (UIntArray.undef_seg_valid vptr 1 vcap).
  Intros.
  prop_apply (UIntArray.undef_seg_valid tptr (Zmax (Zabs tsize) 1) tcap).
  Intros.
  match goal with
  | Hcap : Zmax (Zabs tsize) 1 <= tcap |- _ =>
      rename Hcap into Ht_capmax
  end.
  sep_apply (UIntArray_read0_split_to_full tptr (Zabs tsize) tdata); try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_read0 tptr rem (Zabs tsize) tdata);
    try assumption; try lia.
  sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact tptr rem (Zabs tsize) tcap).
  replace (sublist 0 1 vdata) with vdata.
  2:{
    rewrite <- PreH20.
    rewrite sublist_self; reflexivity.
  }
  sep_apply (UIntArray.seg_to_full vptr 0 1 vdata).
  replace (vptr + 0 * sizeof(UINT)) with vptr by lia.
  replace (1 - 0) with 1 by lia.
  sep_apply_l_atomic (UIntArray_full_to_mpd_store_Z_compact vptr 1 vdata tv_val).
  - dump_pre_spatial. exact PreH20.
  - dump_pre_spatial. exact PreH25.
  - dump_pre_spatial. exact PreH23.
  - dump_pre_spatial.
    apply (is_compact_Z_from_bounds UINT_MOD UINT_MOD_pos); [lia|].
    right. split; [lia|].
    change (1 - 1) with 0.
    change (UINT_MOD ^ 0) with 1.
    unfold UINT_MOD in *; lia.
  - assert (Hretval_range : 0 < retval <= UINT_MAX).
    { split.
      - rewrite Hretval_gcd in PreH1 |- *.
        pose proof (Z.gcd_nonneg rem tv_val).
        lia.
      - change UINT_MAX with 4294967295.
        rewrite Hretval_gcd.
        apply gmp_gcd_bound_32; assumption. }
    sep_apply (UInt_cell_to_mpd_store_Z_compact_1 gp retval Hretval_range).
    rewrite PreH5, PreH28.
    Exists tv_val (if Z_lt_dec tsize 0 then - rem else rem) retval.
    split_pure_spatial.
    + rewrite PreH8.
      cancel (store_Z u_pre zu).
      cancel (store_Z v_pre zv).
      unfold store_Z at 1.
      Exists g__mp_d.
      Exists 1.
      Exists (Z.max 1 gcap).
      unfold store_Z at 1.
      Exists tptr.
      Exists tsize.
      Exists tcap.
      unfold store_Z at 1.
      Exists vptr.
      Exists 1.
      Exists vcap.
      split_pure_spatial.
      * rewrite Ht_abs.
        change (Zabs 1) with 1.
        replace (Zabs tv_val) with tv_val by lia.
        replace (Zabs retval) with retval by
          (rewrite Hretval_gcd; rewrite Z.abs_eq by apply Z.gcd_nonneg; reflexivity).
        normalize.
        repeat cancel.
      * repeat split_pures; dump_pre_spatial.
        all: try assumption; try reflexivity; try lia.
        all: try solve [unfold same_sign; apply or_introl; lia].
        eapply Z.le_trans; [apply Z.le_max_l | exact Ht_capmax].
    + repeat split_pures; dump_pre_spatial;
        try lia; try assumption; try reflexivity.
Qed. 

Lemma proof_of_mpz_gcd_return_wit_1_split_goal_spatial :
  mpz_gcd_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst size_2.
  change (Zabs 0) with 0.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs zv)).
  Intros.
  assert (Hzv: zv = 0).
  { lia. }
  subst zv.
  rewrite Z.gcd_0_r.
  normalize.
  repeat cancel.
Qed.

Lemma proof_of_mpz_gcd_return_wit_1 : mpz_gcd_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_gcd_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_gcd_return_wit_2_split_goal_spatial :
  mpz_gcd_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst size.
  change (Zabs 0) with 0.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs zu)).
  Intros.
  assert (Hzu: zu = 0).
  { lia. }
  subst zu.
  replace (Zgcd 0 zv) with (Zabs zv) by apply Z.gcd_0_l.
  normalize.
  repeat cancel.
Qed.

Lemma proof_of_mpz_gcd_return_wit_2 : mpz_gcd_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_gcd_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpz_gcd_return_wit_3_split_goal_spatial :
  mpz_gcd_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH5.
  cancel.
Qed.

Lemma proof_of_mpz_gcd_return_wit_3 : mpz_gcd_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_gcd_return_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_mpz_gcd_partial_solve_wit_41_pure_split_goal_1 :
  mpz_gcd_partial_solve_wit_41_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (0 - 0) with 0 by lia.
  rewrite (@Znth_sublist0 Z 0 0 1 (mpd_read0_data tdata));
    [rewrite PreH34; dump_pre_spatial; exact PreH30 | lia].
Qed.

Lemma proof_of_mpz_gcd_partial_solve_wit_41_pure_split_goal_2 :
  mpz_gcd_partial_solve_wit_41_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (0 - 0) with 0 by lia.
  rewrite (@Znth_sublist0 Z 0 0 1 (mpd_read0_data tdata));
    [rewrite PreH34; dump_pre_spatial; exact PreH31 | lia].
Qed.

Lemma proof_of_mpz_gcd_partial_solve_wit_41_pure_split_goal_3 :
  mpz_gcd_partial_solve_wit_41_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (0 - 0) with 0 by lia.
  rewrite (@Znth_sublist0 Z 0 0 1 vdata);
    [rewrite PreH35; dump_pre_spatial; exact PreH32 | lia].
Qed.

Lemma proof_of_mpz_gcd_partial_solve_wit_41_pure_split_goal_4 :
  mpz_gcd_partial_solve_wit_41_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (0 - 0) with 0 by lia.
  rewrite (@Znth_sublist0 Z 0 0 1 vdata);
    [rewrite PreH35; dump_pre_spatial; exact PreH33 | lia].
Qed.

Lemma proof_of_mpz_gcd_partial_solve_wit_41_pure_split_goal_5 :
  mpz_gcd_partial_solve_wit_41_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (0 - 0) with 0 by lia.
  rewrite (@Znth_sublist0 Z 0 0 1 (mpd_read0_data tdata));
    [ | lia].
  rewrite (@Znth_sublist0 Z 0 0 1 vdata);
    [rewrite PreH34, PreH35; dump_pre_spatial; lia | lia].
Qed.

Lemma proof_of_mpz_gcd_partial_solve_wit_41_pure :
  mpz_gcd_partial_solve_wit_41_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_gcd_partial_solve_wit_41_pure_split_goal_1.
  - Goal_apply proof_of_mpz_gcd_partial_solve_wit_41_pure_split_goal_2.
  - Goal_apply proof_of_mpz_gcd_partial_solve_wit_41_pure_split_goal_3.
  - Goal_apply proof_of_mpz_gcd_partial_solve_wit_41_pure_split_goal_4.
  - Goal_apply proof_of_mpz_gcd_partial_solve_wit_41_pure_split_goal_5.
Qed. 
