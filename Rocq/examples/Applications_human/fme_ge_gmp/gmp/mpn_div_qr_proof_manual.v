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
  LLM_pre_process ltac:(int_auto).
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
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  Intros l_dp.
  unfold mpd_store_list.
  rewrite H0.
  destruct H as [Hdp_value [Hdp_last Hdp_bound]].
  Exists d1_2 d0_2 di_2 l_dp shift_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + pose proof PreH11 as Hvalid.
      unfold gmp_div_inverse_valid in Hvalid.
      tauto.
    + solve [assumption | symmetry; assumption | rewrite H0 in PreH11; exact PreH11].
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_4_split_goal_1 :
  mpn_div_qr_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  nia.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_4 : mpn_div_qr_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_div_qr_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_5_split_goal_1 :
  mpn_div_qr_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  lia.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_5 : mpn_div_qr_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_div_qr_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_6_1 : mpn_div_qr_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  split_pure_spatial.
  - cancel.
    repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try lia;
      try rewrite PreH17; try symmetry; try assumption; try reflexivity.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_6_2 : mpn_div_qr_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Right.
  Exists shift_2 d1_2 d0_2 di_2.
  unfold mpd_store_Z_compact.
  Intros l_dp.
  unfold mpd_store_list.
  destruct H as [Hdp_value [Hdp_last Hdp_bound]].
  unfold store_preinv_divisor.
  Exists l_dp shift_2 d1_2 d0_2 di_2.
  unfold preinv_dp_value.
  destruct (Z.gtb_spec dn0 2); [lia|].
  unfold div_inverse_store.
  destruct (Z.eq_dec dn0 1) as [Heq|Hneq]; [lia|].
  split_pure_spatial.
  - rewrite H0.
    cancel (UIntArray.full dp0 (Zlength l_dp) l_dp).
    repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try lia;
      try rewrite H0; try rewrite <- H0; try assumption.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_6_3 : mpn_div_qr_entail_wit_6_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Right.
  Exists shift_2 d1_2 d0_2 di_2.
  unfold mpd_store_Z_compact.
  Intros l_dp.
  unfold mpd_store_list.
  destruct H as [Hdp_value [Hdp_last Hdp_bound]].
  unfold store_preinv_divisor.
  Exists l_dp shift_2 d1_2 d0_2 di_2.
  unfold preinv_dp_value.
  destruct (Z.gtb_spec dn0 2); [lia|].
  unfold div_inverse_store.
  destruct (Z.eq_dec dn0 1) as [Heq|Hneq]; [|lia].
  rewrite H0.
  split_pure_spatial.
  - cancel.
    repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try lia; try rewrite <- H0; try assumption.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_6_4 : mpn_div_qr_entail_wit_6_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists shift_2 d1_2 d0_2 di_2.
  unfold mpd_store_Z_compact.
  Intros l_dp.
  unfold mpd_store_list.
  destruct H as [Hdp_value [Hdp_last Hdp_bound]].
  pose proof PreH10 as Hvalid_orig.
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
  split_pure_spatial.
  - rewrite H0.
    cancel (UIntArray.full dp0 (Zlength l_dp) l_dp).
    repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try lia;
      try rewrite <- Hshift0; try exact Hvalid_orig.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_7_1 : mpn_div_qr_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists dp_2 shift_2 d1_2 d0_2 di_2 rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_7_2 : mpn_div_qr_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Left.
  Exists shift_2 d1_2 d0_2 di_2 rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

(* Already discharged by mpn_div_qr_proof_auto after solver regeneration.
Lemma proof_of_mpn_div_qr_entail_wit_7_3 : mpn_div_qr_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Right.
  Exists shift_2 d1_2 d0_2 di_2 rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.
*)

Lemma proof_of_mpn_div_qr_entail_wit_10 : mpn_div_qr_entail_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (store_preinv_divisor_gt2_project dp inv dn0 d_orig ltac:(lia)).
  Intros di l_dp shift.
  unfold div_inverse_fields.
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists di (Znth (dn0 - 2) l_dp 0) (Znth (dn0 - 1) l_dp 0) shift
    (list_to_Z UINT_MOD l_dp) rv_2 qv_2 l_dp l_tail_2 l_rem_2 l_q_2.
  Intros data_dp0.
  Exists data_dp0 l_dp.
  assert (Hlast_l_dp : last l_dp 1 >= 1).
  {
    rewrite (list_last_eq_Znth_last l_dp dn0 H2 ltac:(lia)).
    unfold UINT_MOD in H5.
    change (4294967296 / 2) with 2147483648 in H5.
    lia.
  }
  split_pure_spatial.
  - rewrite PreH18.
    rewrite H2.
    rewrite UIntArray.undef_seg_empty.
    normalize.
    cancel (optional_q_full qp0 ((nn0 - dn0) + 1) l_q_2).
    cancel (UIntArray.seg np0 0 dn0 l_rem_2).
    cancel (UIntArray.seg np0 dn0 nn0 l_tail_2).
    cancel (UIntArray.full dp0 (Zlength data_dp0) data_dp0).
    cancel (UIntArray.full tp dn0 l_dp).
    cancel ((&((inv) # "gmp_div_inverse" ->ₛ "shift")) # UInt |-> shift).
    cancel ((&((inv) # "gmp_div_inverse" ->ₛ "d1")) # UInt
      |-> Znth (dn0 - 1) l_dp 0).
    cancel ((&((inv) # "gmp_div_inverse" ->ₛ "d0")) # UInt
      |-> Znth (dn0 - 2) l_dp 0).
    cancel ((&((inv) # "gmp_div_inverse" ->ₛ "di")) # UInt |-> di).
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    apply is_compact_Z_from_full_last with (data := l_dp);
      try assumption; try reflexivity; try lia.
    split; [reflexivity | split; assumption].
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_11_1 : mpn_div_qr_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  unfold div_inverse_slot.
  split_pure_spatial.
  - sep_apply (store_uint_undef_store_uint
      (&(inv # "gmp_div_inverse" ->ₛ"shift")) shift).
    sep_apply (store_uint_undef_store_uint
      (&(inv # "gmp_div_inverse" ->ₛ"d1")) d1).
    sep_apply (store_uint_undef_store_uint
      (&(inv # "gmp_div_inverse" ->ₛ"d0")) d0).
    sep_apply (store_uint_undef_store_uint
      (&(inv # "gmp_div_inverse" ->ₛ"di")) di).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_11_2 : mpn_div_qr_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH18 in PreH16.
  sep_apply (store_preinv_divisor_shift0_valid_project
    dp0 inv dn0 d_orig d1 d0 di PreH16).
  sep_apply (store_div_inverse_to_slot inv dn0 d_orig).
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  split_pure_spatial.
  - cancel (optional_q_full qp0 ((nn0 - dn0) + 1) l_q_2).
    cancel (UIntArray.seg np0 0 dn0 l_rem_2).
    cancel (UIntArray.seg np0 dn0 nn0 l_tail_2).
    cancel (mpd_store_Z_compact UINT_MOD dp0 d_orig dn0).
    cancel (div_inverse_slot inv).
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_div_qr_entail_wit_11_3 : mpn_div_qr_entail_wit_11_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hdn_cases : dn0 = 1 \/ dn0 = 2) by lia.
  destruct Hdn_cases as [Hdn | Hdn].
  - rewrite Hdn.
    sep_apply (store_preinv_divisor_dn1_project dp0 inv d_orig).
    sep_apply (store_div_inverse_to_slot inv 1 d_orig).
    Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
    split_pure_spatial.
    + repeat cancel.
    + split_pures; dump_pre_spatial; try assumption; try reflexivity; lia.
  - rewrite Hdn.
    sep_apply (store_preinv_divisor_dn2_project dp0 inv d_orig).
    sep_apply (store_div_inverse_to_slot inv 2 d_orig).
    Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
    split_pure_spatial.
    + repeat cancel.
    + split_pures; dump_pre_spatial; try assumption; try reflexivity; lia.
Qed.

(*
Lemma proof_of_mpn_div_qr_entail_wit_12_split_goal_1 :
  mpn_div_qr_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

(* Already discharged by mpn_div_qr_proof_auto after solver regeneration.
Lemma proof_of_mpn_div_qr_entail_wit_12 : mpn_div_qr_entail_wit_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; lia.
Qed.
*)

(*
Lemma proof_of_mpn_div_qr_return_wit_1_split_goal_1 :
  mpn_div_qr_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

(* Already discharged by mpn_div_qr_proof_auto after solver regeneration.
Lemma proof_of_mpn_div_qr_return_wit_1 : mpn_div_qr_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; lia.
Qed.
*)

Lemma proof_of_mpn_div_qr_partial_solve_wit_4_pure_split_goal_1 :
  mpn_div_qr_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (UIntArray_undef_full_full_base_neq tp dp0 dn0 l_dp ltac:(lia) ltac:(assumption)).
  Intros Hbase_neq.
  dump_pre_spatial.
  rewrite <- PreH12.
  exact H.
Qed.

Lemma proof_of_mpn_div_qr_partial_solve_wit_4_pure_split_goal_2 :
  mpn_div_qr_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (UIntArray_undef_full_full_base_neq tp dp0 dn0 l_dp ltac:(lia) ltac:(assumption)).
  Intros Hbase_neq.
  dump_pre_spatial.
  rewrite <- PreH12.
  exact H.
Qed.

Lemma proof_of_mpn_div_qr_partial_solve_wit_4_pure :
  mpn_div_qr_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (UIntArray_undef_full_full_base_neq tp dp0 dn0 l_dp ltac:(lia) ltac:(assumption)).
  Intros Hbase_neq.
  split_pures; dump_pre_spatial;
    try solve
      [ rewrite <- PreH12; exact H
      | rewrite PreH12; exact H
      | intro Heq; apply H; rewrite PreH12; congruence
      | exact H
      | assumption
      | lia ].
Qed.
