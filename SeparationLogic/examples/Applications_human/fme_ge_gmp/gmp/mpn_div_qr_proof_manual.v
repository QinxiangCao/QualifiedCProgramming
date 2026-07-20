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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_div_qr_entail_wit_2 : mpn_div_qr_entail_wit_2.
Proof.
  unfold mpn_div_qr_entail_wit_2.
  intros.
  unfold store_div_inverse, div_inverse_store.
  Intros shift d1 d0 di.
  destruct (Z.eq_dec dn0 1) as [Hdn|Hdn].
  - Left.
    Exists shift d1 d0 di.
    split_pure_spatial.
    + cancel (optional_q_undef qp0 (nn0 - dn0 + 1)).
      cancel (UIntArray.full np0 nn0 l_np).
      cancel (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0).
      cancel (&(inv # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift).
      cancel (&(inv # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1).
      cancel (&(inv # "gmp_div_inverse" ->ₛ"d0") # UInt |->_).
      cancel (&(inv # "gmp_div_inverse" ->ₛ"di") # UInt |-> di).
    + repeat split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
  - Right.
    Exists shift d1 d0 di.
    split_pure_spatial.
    + cancel (optional_q_undef qp0 (nn0 - dn0 + 1)).
      cancel (UIntArray.full np0 nn0 l_np).
      cancel (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0).
      cancel (&(inv # "gmp_div_inverse" ->ₛ"shift") # UInt |-> shift).
      cancel (&(inv # "gmp_div_inverse" ->ₛ"d1") # UInt |-> d1).
      cancel (&(inv # "gmp_div_inverse" ->ₛ"d0") # UInt |-> d0).
      cancel (&(inv # "gmp_div_inverse" ->ₛ"di") # UInt |-> di).
    + repeat split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_3 : mpn_div_qr_entail_wit_3.
Proof.
  unfold mpn_div_qr_entail_wit_3.
  right.
  intros.
  unfold mpd_store_Z_compact.
  Intros l_dp.
  Exists l_dp.
  entailer!.
  - rewrite H0. pre_process.
  - unfold gmp_div_inverse_valid in *. lia.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_4 : mpn_div_qr_entail_wit_4.
Proof.
  unfold mpn_div_qr_entail_wit_4.
  right.
  intros.
  assert (Hout_nonneg : 0 <= list_to_Z UINT_MOD l_out).
  { pose proof (list_to_Z_pos UINT_MOD UINT_MOD_pos l_out PreH15) as Hpos. lia. }
  assert (Hnorm_bound : list_to_Z UINT_MOD l_dp * 2 ^ shift < UINT_MOD ^ dn0).
  { rewrite PreH28. unfold gmp_div_inverse_valid in PreH30. tauto. }
  assert (Hnorm_nonneg : 0 <= list_to_Z UINT_MOD l_dp * 2 ^ shift).
  { assert (0 <= list_to_Z UINT_MOD l_dp).
    { pose proof (list_to_Z_pos UINT_MOD UINT_MOD_pos l_dp PreH27) as Hpos. lia. }
    assert (0 < 2 ^ shift).
    { apply Z.pow_pos_nonneg; lia. }
    nia. }
  assert (Hout_bound : list_to_Z UINT_MOD l_out < UINT_MOD ^ dn0).
  { pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH15) as [_ Hb].
    rewrite PreH14 in Hb. exact Hb. }
  assert (Hpow_pos : 0 < UINT_MOD ^ dn0).
  { apply Z.pow_pos_nonneg; unfold UINT_MOD; lia. }
  assert (retval = 0) by nia.
  subst retval.
  pre_process.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_5 : mpn_div_qr_entail_wit_5.
Proof.
  unfold mpn_div_qr_entail_wit_5.
  right.
  intros.
  assert (Hout_nonneg : 0 <= list_to_Z UINT_MOD l_out).
  { pose proof (list_to_Z_pos UINT_MOD UINT_MOD_pos l_out PreH13) as Hpos. lia. }
  assert (Hout_bound : list_to_Z UINT_MOD l_out < UINT_MOD ^ dn0).
  { pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH13) as [_ Hb].
    rewrite PreH12 in Hb. exact Hb. }
  assert (Hnorm_bound : list_to_Z UINT_MOD l_dp_2 * 2 ^ shift_2 < UINT_MOD ^ dn0).
  { rewrite PreH26. unfold gmp_div_inverse_valid in PreH28. tauto. }
  assert (Hnorm_nonneg : 0 <= list_to_Z UINT_MOD l_dp_2 * 2 ^ shift_2).
  { assert (0 <= list_to_Z UINT_MOD l_dp_2).
    { pose proof (list_to_Z_pos UINT_MOD UINT_MOD_pos l_dp_2 PreH25) as Hpos. lia. }
    assert (0 < 2 ^ shift_2).
    { apply Z.pow_pos_nonneg; lia. }
    nia. }
  assert (Hpow_pos : 0 < UINT_MOD ^ dn0).
  { apply Z.pow_pos_nonneg; unfold UINT_MOD; lia. }
  assert (retval = 0) by nia.
  subst retval.
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_6_1 : mpn_div_qr_entail_wit_6_1.
Proof.
  unfold mpn_div_qr_entail_wit_6_1.
  left.
  intros.
  Exists dp_2 shift_2 d1_2 d0_2 di_2.
  assert (Hlast_nonzero : Znth (dn0 - 1) l_dp 0 <> 0).
  { rewrite <- (list_last_eq_Znth_last l_dp dn0 PreH10 ltac:(lia)).
    lia. }
  assert (Hdcompact : is_compact_Z UINT_MOD d_orig dn0).
  { rewrite <- PreH15.
    eapply is_compact_Z_full_high_nonzero; eauto; lia. }
  sep_apply (UIntArray_full_to_mpd_store_Z_compact dp0 dn0 l_dp d_orig);
    try assumption.
  unfold store_preinv_divisor.
  Exists l_norm shift_2 d1_2 d0_2 di_2.
  unfold preinv_dp_value.
  destruct (Z.gtb_spec dn0 2); [|lia].
  unfold div_inverse_store.
  destruct (Z.eq_dec dn0 1) as [Heq|Hneq]; [lia|].
  entailer!;
    try rewrite PreH17;
    try lia.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_6_2 : mpn_div_qr_entail_wit_6_2.
Proof.
  unfold mpn_div_qr_entail_wit_6_2.
  intros.
  Right.
  Exists shift_2 d1_2 d0_2 di_2.
  unfold mpd_store_Z_compact.
  Intros l_dp.
  unfold mpd_store_list.
  unfold store_preinv_divisor.
  Exists l_dp shift_2 d1_2 d0_2 di_2.
  unfold preinv_dp_value.
  destruct (Z.gtb_spec dn0 2); [lia|].
  unfold div_inverse_store.
  destruct (Z.eq_dec dn0 1) as [Heq|Hneq]; [lia|].
  entailer!;
    try rewrite H0;
    try lia.
  cancel (UIntArray.full dp0 (Zlength l_dp) l_dp).
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_6_3 : mpn_div_qr_entail_wit_6_3.
Proof.
  unfold mpn_div_qr_entail_wit_6_3.
  intros.
  Right.
  Exists shift_2 d1_2 d0_2 di_2.
  unfold mpd_store_Z_compact.
  Intros l_dp.
  unfold mpd_store_list.
  unfold store_preinv_divisor.
  Exists l_dp shift_2 d1_2 d0_2 di_2.
  unfold preinv_dp_value.
  destruct (Z.gtb_spec dn0 2); [lia|].
  unfold div_inverse_store.
  destruct (Z.eq_dec dn0 1) as [Heq|Hneq]; [|lia].
  rewrite H0.
  entailer!.
  all: rewrite <- H0; exact PreH9.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_6_4 : mpn_div_qr_entail_wit_6_4.
Proof.
  unfold mpn_div_qr_entail_wit_6_4.
  left.
  intros.
  Exists shift_2 d1_2 d0_2 di_2.
  unfold mpd_store_Z_compact.
  Intros l_dp.
  unfold mpd_store_list.
  assert (Hshift0 : shift_2 = 0).
  { unfold gmp_div_inverse_valid in PreH10.
    repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
    lia. }
  unfold store_preinv_divisor.
  Exists l_dp shift_2 d1_2 d0_2 di_2.
  unfold preinv_dp_value.
  destruct (Z.gtb_spec dn0 2); [|lia].
  unfold div_inverse_store.
  destruct (Z.eq_dec dn0 1) as [Heq|Hneq]; [lia|].
  rewrite Hshift0.
  change (2 ^ 0) with 1.
  replace (d_orig * 1) with d_orig by ring.
  entailer!.
  - rewrite H0.
    cancel (UIntArray.full dp0 (Zlength l_dp) l_dp).
  - rewrite <- Hshift0.
    exact PreH10.
  - rewrite <- Hshift0.
    exact PreH10.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_7_1 : mpn_div_qr_entail_wit_7_1.
Proof.
  unfold mpn_div_qr_entail_wit_7_1.
  left.
  intros.
  Exists dp_2 shift_2 d1_2 d0_2 di_2 rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_7_2 : mpn_div_qr_entail_wit_7_2.
Proof.
  unfold mpn_div_qr_entail_wit_7_2.
  intros.
  Left.
  Exists shift_2 d1_2 d0_2 di_2 rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_7_3 : mpn_div_qr_entail_wit_7_3.
Proof.
  unfold mpn_div_qr_entail_wit_7_3.
  intros.
  Right.
  Exists shift_2 d1_2 d0_2 di_2 rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_10 : mpn_div_qr_entail_wit_10.
Proof.
  unfold mpn_div_qr_entail_wit_10.
  right.
  intros.
  sep_apply (store_preinv_divisor_gt2_project dp inv dn0 d_orig ltac:(lia)).
  Intros di l_dp shift.
  unfold div_inverse_fields.
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists di (Znth (dn0 - 2) l_dp 0) (Znth (dn0 - 1) l_dp 0) shift l_dp l_q_2.
  Intros data_dp0.
  Exists data_dp0 l_dp.
  assert (Hlast_l_dp : last l_dp 1 >= 1).
  {
    rewrite (list_last_eq_Znth_last l_dp dn0 H2 ltac:(lia)).
    unfold UINT_MOD in H5.
    change (4294967296 / 2) with 2147483648 in H5.
    lia.
  }
  entailer!.
  - rewrite PreH18.
    rewrite H2.
    entailer!.
  - apply is_compact_Z_from_full_last with (data := l_dp); try assumption; try lia.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_11_1 : mpn_div_qr_entail_wit_11_1.
Proof.
  unfold mpn_div_qr_entail_wit_11_1.
  left.
  intros.
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  unfold div_inverse_slot.
  entailer!.
  sep_apply (store_uint_undef_store_uint (&(inv # "gmp_div_inverse" ->ₛ"shift")) shift).
  sep_apply (store_uint_undef_store_uint (&(inv # "gmp_div_inverse" ->ₛ"d1")) d1).
  sep_apply (store_uint_undef_store_uint (&(inv # "gmp_div_inverse" ->ₛ"d0")) d0).
  sep_apply (store_uint_undef_store_uint (&(inv # "gmp_div_inverse" ->ₛ"di")) di).
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_11_2 : mpn_div_qr_entail_wit_11_2.
Proof.
  unfold mpn_div_qr_entail_wit_11_2.
  right.
  intros.
  rewrite PreH18 in PreH16.
  sep_apply (store_preinv_divisor_shift0_valid_project
    dp0 inv dn0 d_orig d1 d0 di PreH16).
  sep_apply (store_div_inverse_to_slot inv dn0 d_orig).
  Exists l_q_2.
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_11_3 : mpn_div_qr_entail_wit_11_3.
Proof.
  unfold mpn_div_qr_entail_wit_11_3.
  left.
  intros.
  assert (Hdn_cases : dn0 = 1 \/ dn0 = 2) by lia.
  destruct Hdn_cases as [Hdn | Hdn].
  - rewrite Hdn.
    sep_apply (store_preinv_divisor_dn1_project dp0 inv d_orig).
    sep_apply (store_div_inverse_to_slot inv 1 d_orig).
    Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
    entailer!.
  - rewrite Hdn.
    sep_apply (store_preinv_divisor_dn2_project dp0 inv d_orig).
    sep_apply (store_div_inverse_to_slot inv 2 d_orig).
    Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
    entailer!.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_12 : mpn_div_qr_entail_wit_12.
Proof.
  unfold mpn_div_qr_entail_wit_12.
  right.
  intros.
  Exists l_q_2.
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_return_wit_1 : mpn_div_qr_return_wit_1.
Proof.
  unfold mpn_div_qr_return_wit_1.
  right.
  intros.
  Exists l_q_2.
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_partial_solve_wit_4_pure : mpn_div_qr_partial_solve_wit_4_pure.
Proof.
  unfold mpn_div_qr_partial_solve_wit_4_pure.
  right.
  intros.
  prop_apply_p (UIntArray_undef_full_full_base_neq tp dp0 dn0 l_dp ltac:(lia) ltac:(assumption)).
  Intros.
  entailer!.
Qed.
