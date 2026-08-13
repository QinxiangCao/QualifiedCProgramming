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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_mul_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_mul_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_mul_safety_wit_16 : mpz_mul_safety_wit_16.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1 z2 size size_2 cap cap_2
    PreH10 PreH9 PreH8 PreH7).
  Intros.
  subst retval retval_2.
  repeat split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_17 : mpz_mul_safety_wit_17.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1 z2 size size_2 cap cap_2
    PreH11 PreH10 PreH9 PreH8).
  Intros.
  subst retval retval_2.
  repeat split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_18 : mpz_mul_safety_wit_18.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1 z2 size size_2 cap cap_2
    PreH11 PreH10 PreH9 PreH8).
  Intros.
  subst retval retval_2.
  repeat split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_mpz_mul_safety_wit_19 : mpz_mul_safety_wit_19.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1 z2 size size_2 cap cap_2
    PreH11 PreH10 PreH9 PreH8).
  Intros.
  subst retval retval_2.
  repeat split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_1_1 : mpz_mul_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1 z2 size size_2 cap cap_2
    PreH10 PreH9 PreH8 PreH7).
  Intros.
  unfold store_Z.
  Intros rptr rsize rcap.
  prop_apply (store_int_range (&(rop_pre # "__mpz_struct" ->ₛ"_mp_alloc")) rcap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros rdata data_1 data_2.
  Exists cap_2 ptr_2 cap ptr rptr data_2 data_1 rcap rsize size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_1 = Zabs z1 /\ last data_1 1 >= 1 /\ list_within_bound UINT_MOD data_1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_2 = Zabs z2 /\ last data_2 1 >= 1 /\ list_within_bound UINT_MOD data_2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  Exists rdata.
  split_pure_spatial.
  - match goal with H: Zabs rsize = Zlength rdata |- _ => rewrite H end.
    match goal with H: Zabs size = Zlength data_1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto); cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_1_2 : mpz_mul_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1 z2 size size_2 cap cap_2
    PreH11 PreH10 PreH9 PreH8).
  Intros.
  unfold store_Z.
  Intros rptr rsize rcap.
  prop_apply (store_int_range (&(rop_pre # "__mpz_struct" ->ₛ"_mp_alloc")) rcap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros rdata data_1 data_2.
  Exists cap_2 ptr_2 cap ptr rptr data_2 data_1 rcap rsize size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_1 = Zabs z1 /\ last data_1 1 >= 1 /\ list_within_bound UINT_MOD data_1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_2 = Zabs z2 /\ last data_2 1 >= 1 /\ list_within_bound UINT_MOD data_2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  Exists rdata.
  split_pure_spatial.
  - match goal with H: Zabs rsize = Zlength rdata |- _ => rewrite H end.
    match goal with H: Zabs size = Zlength data_1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto); cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_1_3 : mpz_mul_entail_wit_1_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1 z2 size size_2 cap cap_2
    PreH11 PreH10 PreH9 PreH8).
  Intros.
  unfold store_Z.
  Intros rptr rsize rcap.
  prop_apply (store_int_range (&(rop_pre # "__mpz_struct" ->ₛ"_mp_alloc")) rcap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros rdata data_1 data_2.
  Exists cap_2 ptr_2 cap ptr rptr data_2 data_1 rcap rsize size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_1 = Zabs z1 /\ last data_1 1 >= 1 /\ list_within_bound UINT_MOD data_1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_2 = Zabs z2 /\ last data_2 1 >= 1 /\ list_within_bound UINT_MOD data_2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  Exists rdata.
  split_pure_spatial.
  - match goal with H: Zabs rsize = Zlength rdata |- _ => rewrite H end.
    match goal with H: Zabs size = Zlength data_1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto); cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_1_4 : mpz_mul_entail_wit_1_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Intros.
  prop_apply (two_store_Z_fields_total_limb_bound
    op1_pre op2_pre ptr ptr_2 z1 z2 size size_2 cap cap_2
    PreH11 PreH10 PreH9 PreH8).
  Intros.
  unfold store_Z.
  Intros rptr rsize rcap.
  prop_apply (store_int_range (&(rop_pre # "__mpz_struct" ->ₛ"_mp_alloc")) rcap).
  Intros.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros rdata data_1 data_2.
  Exists cap_2 ptr_2 cap ptr rptr data_2 data_1 rcap rsize size size_2.
  subst retval retval_2.
  match goal with
  | H: list_to_Z UINT_MOD data_1 = Zabs z1 /\ last data_1 1 >= 1 /\ list_within_bound UINT_MOD data_1 |- _ =>
      destruct H as [Hdata1_val [Hdata1_last Hdata1_bound]]
  end.
  match goal with
  | H: list_to_Z UINT_MOD data_2 = Zabs z2 /\ last data_2 1 >= 1 /\ list_within_bound UINT_MOD data_2 |- _ =>
      destruct H as [Hdata2_val [Hdata2_last Hdata2_bound]]
  end.
  Exists rdata.
  split_pure_spatial.
  - match goal with H: Zabs rsize = Zlength rdata |- _ => rewrite H end.
    match goal with H: Zabs size = Zlength data_1 |- _ => rewrite H end.
    match goal with H: Zabs size_2 = Zlength data_2 |- _ => rewrite H end.
    LLM_pre_process ltac:(int_auto); cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_mul_sign, same_sign.
    first
      [ left; split; [lia | left; lia]
      | left; split; [lia | right; lia]
      | right; split; [lia | left; lia]
      | right; split; [lia | right; lia] ].
    all: match goal with
    | H: Int.min_signed <= ?x <= Int.max_signed |- ?x <= 2147483647 =>
        change Int.max_signed with 2147483647 in H; lia
    end.
Qed.

Lemma proof_of_mpz_mul_entail_wit_3 : mpz_mul_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists op2cap_2 op1cap_2 rp (un + vn) 0 rptr_2 l2_2 l1_2 rcap_2 rsize_2 op1size_2 op2size_2.
  replace (vn + un) with (un + vn) by lia.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size_2 t__mp_alloc_2 t__mp_d_2.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_4_1 : mpz_mul_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1 * z2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1 * list_to_Z UINT_MOD l2,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2 * list_to_Z UINT_MOD l1,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1 * z2)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    eapply (is_compact_Z_mul_high_zero l1 l2 l_out un vn); try assumption; try lia.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1) un).
  { eapply (is_compact_Z_from_full_last l1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2) vn).
  { eapply (is_compact_Z_from_full_last l2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1).
  {
    match goal with
    | Hbound: list_within_bound UINT_MOD l1,
      Hlast: last l1 1 >= 1,
      Hlen: Zlength l1 = un,
      Hval: list_to_Z UINT_MOD l1 = Zabs z1 |- _ =>
        pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1 Hbound Hlast) as [Hlo _];
        rewrite Hlen in Hlo;
        rewrite Hval in Hlo;
        pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia));
        lia
    end.
  }
  assert (Hz2abs_pos: 0 < Zabs z2).
  {
    match goal with
    | Hbound: list_within_bound UINT_MOD l2,
      Hlast: last l2 1 >= 1,
      Hlen: Zlength l2 = vn,
      Hval: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2 Hbound Hlast) as [Hlo _];
        rewrite Hlen in Hlo;
        rewrite Hval in Hlo;
        pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia));
        lia
    end.
  }
  assert (Hsame_prod: same_sign (z1 * z2) (-(un + vn - 1))).
  {
    unfold mpz_mul_sign in PreH12.
    destruct PreH12 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr un op1cap).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr vn op2cap).
  Intros.
  unfold store_Z.
  Exists rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap rp (-(un + vn - 1)) (un + vn).
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size) with un by lia.
  replace (Zabs op2size) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1 * z2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr un l1 (Zabs z1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr vn l2 (Zabs z2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn - 1))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_4_2 : mpz_mul_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1 * z2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1 * list_to_Z UINT_MOD l2,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2 * list_to_Z UINT_MOD l1,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1 * z2)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    replace (un + vn - 1) with (vn + un - 1) by lia.
    eapply (is_compact_Z_mul_high_zero l2 l1 l_out vn un); try assumption; try lia.
    replace (vn + un - 1) with (un + vn - 1) by lia.
    exact PreH1.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1) un).
  { eapply (is_compact_Z_from_full_last l1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2) vn).
  { eapply (is_compact_Z_from_full_last l2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1 PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2 PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1 * z2) (-(un + vn - 1))).
  {
    unfold mpz_mul_sign in PreH12.
    destruct PreH12 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr un op1cap).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr vn op2cap).
  Intros.
  unfold store_Z.
  Exists rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap rp (-(un + vn - 1)) (un + vn).
  replace (Zabs (-(un + vn - 1))) with (un + vn - 1) by lia.
  replace (Zabs op1size) with un by lia.
  replace (Zabs op2size) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1 * z2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr un l1 (Zabs z1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr vn l2 (Zabs z2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn - 1))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_4_3 : mpz_mul_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1 * z2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1 * list_to_Z UINT_MOD l2,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2 * list_to_Z UINT_MOD l1,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1 * z2)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1) un).
  { eapply (is_compact_Z_from_full_last l1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2) vn).
  { eapply (is_compact_Z_from_full_last l2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1 PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2 PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1 * z2) (-(un + vn))).
  {
    unfold mpz_mul_sign in PreH12.
    destruct PreH12 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr un op1cap).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr vn op2cap).
  Intros.
  unfold store_Z.
  Exists rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap rp (-(un + vn)) (un + vn).
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size) with un by lia.
  replace (Zabs op2size) with vn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1 * z2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr un l1 (Zabs z1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr vn l2 (Zabs z2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_4_4 : mpz_mul_entail_wit_4_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  assert (Hsign1: sign = 1) by lia.
  subst sign.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1 * z2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1 * list_to_Z UINT_MOD l2,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2 * list_to_Z UINT_MOD l1,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1 * z2)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1) un).
  { eapply (is_compact_Z_from_full_last l1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2) vn).
  { eapply (is_compact_Z_from_full_last l2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1 PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2 PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_prod: same_sign (z1 * z2) (-(un + vn))).
  {
    unfold mpz_mul_sign in PreH12.
    destruct PreH12 as [[Hzero _] | [_ Hcases]]; [lia |].
    destruct Hcases as [[Hop1neg Hop2pos] | [Hop1pos Hop2neg]].
    - eapply same_sign_mul_neg_pos_abs; eauto; lia.
    - eapply same_sign_mul_pos_neg_abs; eauto; lia.
  }
  prop_apply (UIntArray.undef_seg_valid op1ptr un op1cap).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr vn op2cap).
  Intros.
  unfold store_Z.
  Exists rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap rp (-(un + vn)) (un + vn).
  replace (Zabs (-(un + vn))) with (un + vn) by lia.
  replace (Zabs op1size) with un by lia.
  replace (Zabs op2size) with vn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1 * z2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr un l1 (Zabs z1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr vn l2 (Zabs z2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (-(un + vn))).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 1).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_4_5 : mpz_mul_entail_wit_4_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1 * z2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1 * list_to_Z UINT_MOD l2,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2 * list_to_Z UINT_MOD l1,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1 * z2)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    eapply (is_compact_Z_mul_high_zero l1 l2 l_out un vn); try assumption; try lia.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1) un).
  { eapply (is_compact_Z_from_full_last l1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2) vn).
  { eapply (is_compact_Z_from_full_last l2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1 PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2 PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size op2size).
  { unfold mpz_mul_sign in PreH12. destruct PreH12 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1 * z2) (un + vn - 1)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr un op1cap).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr vn op2cap).
  Intros.
  unfold store_Z.
  Exists rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap rp (un + vn - 1) (un + vn).
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size) with un by lia.
  replace (Zabs op2size) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1 * z2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr un l1 (Zabs z1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr vn l2 (Zabs z2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (un + vn - 1)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_4_6 : mpz_mul_entail_wit_4_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  replace (vn + un) with (un + vn) in * by lia.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1 * z2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1 * list_to_Z UINT_MOD l2,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2 * list_to_Z UINT_MOD l1,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1 * z2)) (un + vn - 1)).
  {
    rewrite <- Hout_abs.
    replace (un + vn - 1) with (vn + un - 1) by lia.
    eapply (is_compact_Z_mul_high_zero l2 l1 l_out vn un); try assumption; try lia.
    replace (vn + un - 1) with (un + vn - 1) by lia.
    exact PreH1.
  }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1) un).
  { eapply (is_compact_Z_from_full_last l1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2) vn).
  { eapply (is_compact_Z_from_full_last l2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1 PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2 PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size op2size).
  { unfold mpz_mul_sign in PreH12. destruct PreH12 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1 * z2) (un + vn - 1)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr un op1cap).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr vn op2cap).
  Intros.
  unfold store_Z.
  Exists rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap rp (un + vn - 1) (un + vn).
  replace (Zabs (un + vn - 1)) with (un + vn - 1) by lia.
  replace (Zabs op1size) with un by lia.
  replace (Zabs op2size) with vn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1 * z2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr un l1 (Zabs z1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr vn l2 (Zabs z2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (un + vn - 1)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_4_7 : mpz_mul_entail_wit_4_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  subst sign.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1 * z2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1 * list_to_Z UINT_MOD l2,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2 * list_to_Z UINT_MOD l1,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1 * z2)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1) un).
  { eapply (is_compact_Z_from_full_last l1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2) vn).
  { eapply (is_compact_Z_from_full_last l2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1 PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2 PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size op2size).
  { unfold mpz_mul_sign in PreH12. destruct PreH12 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1 * z2) (un + vn)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr un op1cap).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr vn op2cap).
  Intros.
  unfold store_Z.
  Exists rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap rp (un + vn) (un + vn).
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size) with un by lia.
  replace (Zabs op2size) with vn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1 * z2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr un l1 (Zabs z1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr vn l2 (Zabs z2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (un + vn)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_entail_wit_4_8 : mpz_mul_entail_wit_4_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  LLM_pre_process ltac:(int_auto).
  subst t__mp_size t__mp_alloc t__mp_d.
  subst sign.
  replace (vn + un) with (un + vn) in * by lia.
  assert (Hout_abs: list_to_Z UINT_MOD l_out = Zabs (z1 * z2)).
  {
    match goal with
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l1 * list_to_Z UINT_MOD l2,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl1, Hl2
    | Hout: list_to_Z UINT_MOD l_out = val_out,
      Hmul: val_out = list_to_Z UINT_MOD l2 * list_to_Z UINT_MOD l1,
      Hl1: list_to_Z UINT_MOD l1 = Zabs z1,
      Hl2: list_to_Z UINT_MOD l2 = Zabs z2 |- _ =>
        rewrite Hout, Hmul, Hl2, Hl1
    end.
    rewrite Z.abs_mul.
    ring.
  }
  assert (Hrop_compact: is_compact_Z UINT_MOD (Zabs (z1 * z2)) (un + vn)).
  { rewrite <- Hout_abs. eapply is_compact_Z_full_high_nonzero; try eassumption; lia. }
  assert (Hop1_compact: is_compact_Z UINT_MOD (Zabs z1) un).
  { eapply (is_compact_Z_from_full_last l1); eauto; lia. }
  assert (Hop2_compact: is_compact_Z UINT_MOD (Zabs z2) vn).
  { eapply (is_compact_Z_from_full_last l2); eauto; lia. }
  assert (Hz1abs_pos: 0 < Zabs z1).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l1 PreH26 PreH30) as [Hlo _]; rewrite PreH24 in Hlo; rewrite PreH28 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (un - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hz2abs_pos: 0 < Zabs z2).
  { pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos l2 PreH27 PreH31) as [Hlo _]; rewrite PreH25 in Hlo; rewrite PreH29 in Hlo; pose proof (Z.pow_pos_nonneg UINT_MOD (vn - 1) UINT_MOD_pos ltac:(lia)); lia. }
  assert (Hsame_sizes: same_sign op1size op2size).
  { unfold mpz_mul_sign in PreH12. destruct PreH12 as [[_ Hsame] | [Hbad _]]; [exact Hsame | lia]. }
  assert (Hsame_prod: same_sign (z1 * z2) (un + vn)).
  { eapply same_sign_mul_same_abs; eauto; lia. }
  prop_apply (UIntArray.undef_seg_valid op1ptr un op1cap).
  Intros.
  prop_apply (UIntArray.undef_seg_valid op2ptr vn op2cap).
  Intros.
  unfold store_Z.
  Exists rptr rsize rcap op1ptr op1size op1cap op2ptr op2size op2cap rp (un + vn) (un + vn).
  replace (Zabs (un + vn)) with (un + vn) by lia.
  replace (Zabs op1size) with un by lia.
  replace (Zabs op2size) with vn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact rp (un + vn) l_out (Zabs (z1 * z2))); try assumption; try lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op1ptr un l1 (Zabs z1)); try assumption.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact op2ptr vn l2 (Zabs z2)); try assumption.
  sep_apply (store_int_undef_store_int &("rn") (un + vn)).
  sep_apply (store_int_undef_store_int &("un") un).
  sep_apply (store_int_undef_store_int &("vn") vn).
  sep_apply (store_int_undef_store_int &("sign") 0).
  sep_apply (store_ptr_undef_store_ptr &("rp") rp).
  sep_apply (store_ptr_undef_store_ptr &("up") op1ptr).
  sep_apply (store_ptr_undef_store_ptr &("vp") op2ptr).
  sep_apply (store_uint_undef_store_uint &("high") (Znth (un + vn - 1) l_out 0)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_mul_return_wit_1 : mpz_mul_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst size.
  replace (Zabs 0) with 0 by lia.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs z1)).
  Intros.
  assert (z1 = 0) by lia.
  subst z1.
  rewrite Z.mul_0_l.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split ptr_3 (Zabs old) (Zabs size_3) 0 cap_3).
  all: try lia.
  Intros.
  unfold store_Z.
  Exists ptr_3 0 cap_3 ptr 0 cap ptr_2 size_2 cap_2.
  replace (Zabs 0) with 0 by lia.
  rewrite UIntArray.undef_full_empty.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  Intros op1data.
  Exists op1data data (@nil Z).
  rewrite UIntArray.full_empty.
  LLM_pre_process ltac:(int_auto).
  simpl.
  destruct H5 as [Hop1_val [Hop1_last Hop1_bound]].
  destruct H7 as [Hop2_val [Hop2_last Hop2_bound]].
  split_pure_spatial.
  - repeat cancel.
  - unfold same_sign in *.
    repeat split; try assumption; try lia.
Qed.

Lemma proof_of_mpz_mul_return_wit_2 : mpz_mul_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst size_2.
  replace (Zabs 0) with 0 by lia.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr_2 (Zabs z2)).
  Intros.
  assert (z2 = 0) by lia.
  subst z2.
  rewrite Z.mul_0_r.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split ptr_3 (Zabs old) (Zabs size_3) 0 cap_3).
  all: try lia.
  Intros.
  unfold store_Z.
  Exists ptr_3 0 cap_3 ptr size cap ptr_2 0 cap_2.
  replace (Zabs 0) with 0 by lia.
  rewrite UIntArray.undef_full_empty.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  Intros op2data.
  Exists data op2data (@nil Z).
  rewrite UIntArray.full_empty.
  LLM_pre_process ltac:(int_auto).
  simpl.
  destruct H5 as [Hop2_val [Hop2_last Hop2_bound]].
  destruct H7 as [Hop1_val [Hop1_last Hop1_bound]].
  split_pure_spatial.
  - repeat cancel.
  - unfold same_sign in *.
    repeat split; try assumption; try lia.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_5_pure_split_goal_1 :
  mpz_mul_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_5_pure :
  mpz_mul_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_5_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_8_pure_split_goal_1 :
  mpz_mul_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_8_pure :
  mpz_mul_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_8_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_10_pure_split_goal_1 :
  mpz_mul_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_10_pure :
  mpz_mul_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_mul_partial_solve_wit_10_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_12_pure_split_goal_1 :
  mpz_mul_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_mul_partial_solve_wit_12_pure :
  mpz_mul_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
Goal_apply proof_of_mpz_mul_partial_solve_wit_12_pure_split_goal_1.
Qed.
