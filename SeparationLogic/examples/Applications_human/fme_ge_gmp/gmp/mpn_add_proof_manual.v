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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_add_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_add_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_add_partial_solve_wit_5_rp_eq_bp_pure : mpn_add_partial_solve_wit_5_rp_eq_bp_pure.
Proof.
  unfold mpn_add_partial_solve_wit_5_rp_eq_bp_pure.
  right.
  intros.
  subst.
  unfold mpd_store_Z, mpd_store_list.
  Intros data_a_low data_r_low data_a_high.
  replace (an_pre - bn_pre) with (Zlength data_a_high) by lia.
  sep_apply_l_atomic (UIntArray_undef_full_full_base_neq
    (bp_pre + bn_pre * sizeof(UINT))
    (ap_pre + bn_pre * sizeof(UINT))
    (Zlength data_a_high) data_a_high ltac:(lia) ltac:(reflexivity)).
  Intros.
  entailer!.
Qed.

Lemma proof_of_mpn_add_entail_wit_3_rp_eq_bp : mpn_add_entail_wit_3_rp_eq_bp.
Proof.
  unfold mpn_add_entail_wit_3_rp_eq_bp.
  left.
  intros.
  Exists val_r_out.
  sep_apply_l_atomic (UIntArray.undef_seg_to_undef_full rp_pre bn_pre an_pre).
  entailer!.
Qed.

Lemma proof_of_mpn_add_entail_wit_9_1_rp_eq_bp : mpn_add_entail_wit_9_1_rp_eq_bp.
Proof.
  unfold mpn_add_entail_wit_9_1_rp_eq_bp.
  left.
  intros.
  Exists (val_r_low + val' * Z.pow UINT_MOD bn_pre).
  unfold mpd_store_Z, mpd_store_list.
  Intros data_ah data_rh data_al data_rl.
  Exists (data_al ++ data_ah).
  Exists (data_rl ++ data_rh).
  replace (ap_pre + bn_pre * sizeof(UINT))
    with (ap_pre + Zlength data_al * sizeof(UINT)) by lia.
  replace (rp_pre + bn_pre * sizeof(UINT))
    with (rp_pre + Zlength data_rl * sizeof(UINT)) by lia.
  replace (Zlength data_ah)
    with (Zlength data_al + Zlength data_ah - Zlength data_al) by lia.
  replace (Zlength data_rh)
    with (Zlength data_rl + Zlength data_rh - Zlength data_rl) by lia.
  sep_apply_l_atomic
    (UIntArray.full_merge_to_full ap_pre (Zlength data_al)
       (Zlength data_al + Zlength data_ah) data_al data_ah).
  { apply derivable1s_coq_prop_r.
    pose proof (Zlength_nonneg data_al).
    pose proof (Zlength_nonneg data_ah).
    lia. }
  sep_apply_l_atomic
    (UIntArray.full_merge_to_full rp_pre (Zlength data_rl)
       (Zlength data_rl + Zlength data_rh) data_rl data_rh).
  { apply derivable1s_coq_prop_r.
    pose proof (Zlength_nonneg data_rl).
    pose proof (Zlength_nonneg data_rh).
    lia. }
  rewrite !Zlength_app.
  entailer!.
  all: repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  all: try (apply list_within_bound_concat; assumption).
  all: try (rewrite Zlength_app; lia).
  - rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite H5, H1, <- H6.
    lia.
  - rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite H3, H, <- H4.
    lia.
  - assert (Hpow : UINT_MOD ^ (an_pre - bn_pre) * UINT_MOD ^ bn_pre =
                   UINT_MOD ^ an_pre).
    { replace (UINT_MOD ^ an_pre)
        with (UINT_MOD ^ ((an_pre - bn_pre) + bn_pre)) by (f_equal; lia).
      rewrite Z.pow_add_r; try (unfold UINT_MOD; lia). }
    rewrite PreH16.
    replace (val_a_low + val_a_high * UINT_MOD ^ bn_pre + val_b_rp_eq_bp)
      with ((val_a_low + val_b_rp_eq_bp) + val_a_high * UINT_MOD ^ bn_pre)
      by ring.
    rewrite <- PreH15.
    replace (val_r_low + cy * UINT_MOD ^ bn_pre +
               val_a_high * UINT_MOD ^ bn_pre)
      with (val_r_low + (val_a_high + cy) * UINT_MOD ^ bn_pre) by ring.
    replace (val_a_high + cy)
      with (val' + retval * UINT_MOD ^ (an_pre - bn_pre)) by lia.
    rewrite Z.mul_add_distr_r.
    replace (retval * UINT_MOD ^ (an_pre - bn_pre) * UINT_MOD ^ bn_pre)
      with (retval * UINT_MOD ^ an_pre) by (rewrite <- Hpow; ring).
    ring.
Qed.

Lemma proof_of_mpn_add_entail_wit_9_2_rp_eq_bp : mpn_add_entail_wit_9_2_rp_eq_bp.
Proof.
  unfold mpn_add_entail_wit_9_2_rp_eq_bp.
  left.
  intros.
  Exists val_r_low.
  unfold mpd_store_Z, mpd_store_list.
  Intros data_al data_rl data_ah.
  destruct H as [Hal_val Hal_bound].
  destruct H1 as [Hrl_val Hrl_bound].
  destruct H3 as [Hah_val Hah_bound].
  assert (Han : an_pre = bn_pre) by lia.
  assert (Hah_len0 : Zlength data_ah = 0) by lia.
  apply Zlength_nil_inv in Hah_len0.
  subst data_ah.
  simpl in Hah_val.
  rewrite list_to_Z_nil in Hah_val.
  subst val_a_high.
  Exists data_al.
  Exists data_rl.
  rewrite (UIntArray.full_empty (ap_pre + bn_pre * sizeof(UINT)) 0).
  replace (an_pre - bn_pre) with 0 by lia.
  rewrite (UIntArray.undef_full_empty (rp_pre + bn_pre * sizeof(UINT))).
  entailer!.
  rewrite Han.
  rewrite PreH9.
  rewrite Z.mul_0_l, Z.add_0_r.
  exact PreH8.
Qed.

Lemma proof_of_mpn_add_entail_wit_10_1_rp_eq_ap : mpn_add_entail_wit_10_1_rp_eq_ap.
Proof.
  unfold mpn_add_entail_wit_10_1_rp_eq_ap.
  left.
  intros.
  Exists (val_r_low + val' * Z.pow UINT_MOD bn_pre).
  unfold mpd_store_Z, mpd_store_list.
  Intros data_rh data_rl data_b.
  Exists (data_rl ++ data_rh).
  replace (rp_pre + bn_pre * sizeof(UINT))
    with (rp_pre + Zlength data_rl * sizeof(UINT)) by lia.
  replace (Zlength data_rh)
    with (Zlength data_rl + Zlength data_rh - Zlength data_rl) by lia.
  sep_apply_l_atomic
    (UIntArray.full_merge_to_full rp_pre (Zlength data_rl)
       (Zlength data_rl + Zlength data_rh) data_rl data_rh).
  { apply derivable1s_coq_prop_r.
    pose proof (Zlength_nonneg data_rl).
    pose proof (Zlength_nonneg data_rh).
    lia. }
  rewrite !Zlength_app.
  replace ap_pre with rp_pre by lia.
  entailer!.
  all: repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  all: try (apply list_within_bound_concat; assumption).
  all: try (rewrite Zlength_app; lia).
  Exists data_b.
  entailer!.
  - rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite H1, H, <- H2.
    lia.
  - apply list_within_bound_concat; assumption.
  - assert (Hpow : UINT_MOD ^ (an_pre - bn_pre) * UINT_MOD ^ bn_pre =
                   UINT_MOD ^ an_pre).
    { replace (UINT_MOD ^ an_pre)
        with (UINT_MOD ^ ((an_pre - bn_pre) + bn_pre)) by (f_equal; lia).
      rewrite Z.pow_add_r; try (unfold UINT_MOD; lia). }
    replace (retval * UINT_MOD ^ an_pre)
      with (retval * UINT_MOD ^ (an_pre - bn_pre) * UINT_MOD ^ bn_pre)
      by (rewrite <- Hpow; ring).
    replace (val_r_low + val' * UINT_MOD ^ bn_pre +
               retval * UINT_MOD ^ (an_pre - bn_pre) * UINT_MOD ^ bn_pre)
      with (val_r_low + (val' + retval * UINT_MOD ^ (an_pre - bn_pre)) *
               UINT_MOD ^ bn_pre) by ring.
    rewrite PreH7.
    replace (val_r_low + (val_a_high + cy) * UINT_MOD ^ bn_pre)
      with ((val_r_low + cy * UINT_MOD ^ bn_pre) +
            val_a_high * UINT_MOD ^ bn_pre) by ring.
    rewrite PreH16.
    rewrite PreH17.
    ring.
Qed.

Lemma proof_of_mpn_add_entail_wit_10_2_rp_eq_ap : mpn_add_entail_wit_10_2_rp_eq_ap.
Proof.
  unfold mpn_add_entail_wit_10_2_rp_eq_ap.
  left.
  intros.
  Exists val_r_low.
  unfold mpd_store_Z, mpd_store_list.
  Intros data_rl data_b data_ah.
  destruct H as [Hrl_val Hrl_bound].
  destruct H1 as [Hb_val Hb_bound].
  destruct H3 as [Hah_val Hah_bound].
  assert (Han : an_pre = bn_pre) by lia.
  assert (Hah_len0 : Zlength data_ah = 0) by lia.
  apply Zlength_nil_inv in Hah_len0.
  subst data_ah.
  simpl in Hah_val.
  rewrite list_to_Z_nil in Hah_val.
  subst val_a_high.
  Exists data_rl.
  Exists data_b.
  rewrite (UIntArray.full_empty (ap_pre + bn_pre * sizeof(UINT)) 0).
  replace ap_pre with rp_pre by lia.
  entailer!.
  rewrite Han.
  rewrite PreH9.
  rewrite Z.mul_0_l, Z.add_0_r.
  exact PreH8.
Qed.

Lemma proof_of_mpn_add_which_implies_wit_1 : mpn_add_which_implies_wit_1.
Proof.
  unfold mpn_add_which_implies_wit_1.
  left.
  intros.
  unfold mpd_store_Z, mpd_store_list.
  Intros data.
  destruct H as [Hval Hbound].
  Exists (list_to_Z UINT_MOD (sublist bn an data)).
  Exists (list_to_Z UINT_MOD (sublist 0 bn data)).
  sep_apply_l_atomic (UIntArray.full_split_to_full ap bn (Zlength data) data).
  - apply derivable1s_coq_prop_r.
    rewrite <- H0.
    lia.
  - Exists (sublist 0 bn data).
    Exists (sublist bn an data).
    replace (sublist bn an data) with (sublist bn (Zlength data) data)
      by (rewrite <- H0; reflexivity).
    replace (Zlength (sublist bn (Zlength data) data)) with (an - bn)
      by (rewrite Zlength_sublist by lia; lia).
    replace (Zlength (sublist 0 bn data)) with bn
      by (rewrite Zlength_sublist by lia; lia).
    replace (Zlength data - bn) with (an - bn) by lia.
    entailer!.
    + apply list_within_bound_sublist; try lia; assumption.
    + apply list_within_bound_sublist; try lia; assumption.
    + rewrite <- Hval.
      pose proof (sublist_self data (Zlength data)) as Hself.
      specialize (Hself ltac:(lia)).
      pose proof (sublist_split 0 (Zlength data) bn data) as Hsplit.
      specialize (Hsplit ltac:(lia) ltac:(lia)).
      rewrite <- Hself at 1.
      rewrite Hsplit.
      rewrite list_to_Z_concat; try exact UINT_MOD_pos;
        try (apply list_within_bound_sublist; try lia; assumption).
      rewrite Zlength_sublist by lia.
      replace (bn - 0) with bn by lia.
      lia.
Qed.

Lemma proof_of_mpn_add_which_implies_wit_2 : mpn_add_which_implies_wit_2.
Proof.
  unfold mpn_add_which_implies_wit_2.
  left.
  intros.
  unfold mpd_store_Z, mpd_store_list.
  Intros data.
  destruct H as [Hval Hbound].
  Exists (list_to_Z UINT_MOD (sublist bn an data)).
  Exists (list_to_Z UINT_MOD (sublist 0 bn data)).
  sep_apply_l_atomic (UIntArray.full_split_to_full ap bn (Zlength data) data).
  - apply derivable1s_coq_prop_r.
    rewrite <- H0.
    lia.
  - Exists (sublist 0 bn data).
    Exists (sublist bn an data).
    replace (sublist bn an data) with (sublist bn (Zlength data) data)
      by (rewrite <- H0; reflexivity).
    replace (Zlength (sublist bn (Zlength data) data)) with (an - bn)
      by (rewrite Zlength_sublist by lia; lia).
    replace (Zlength (sublist 0 bn data)) with bn
      by (rewrite Zlength_sublist by lia; lia).
    replace (Zlength data - bn) with (an - bn) by lia.
    entailer!.
    + apply list_within_bound_sublist; try lia; assumption.
    + apply list_within_bound_sublist; try lia; assumption.
    + rewrite <- Hval.
      pose proof (sublist_self data (Zlength data)) as Hself.
      specialize (Hself ltac:(lia)).
      pose proof (sublist_split 0 (Zlength data) bn data) as Hsplit.
      specialize (Hsplit ltac:(lia) ltac:(lia)).
      rewrite <- Hself at 1.
      rewrite Hsplit.
      rewrite list_to_Z_concat; try exact UINT_MOD_pos;
        try (apply list_within_bound_sublist; try lia; assumption).
      rewrite Zlength_sublist by lia.
      replace (bn - 0) with bn by lia.
      lia.
Qed.
