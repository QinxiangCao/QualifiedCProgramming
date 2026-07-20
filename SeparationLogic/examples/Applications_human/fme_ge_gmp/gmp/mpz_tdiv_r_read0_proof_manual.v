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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_normalized_size_entail_wit_1 : mpn_normalized_size_entail_wit_1.
Proof.
  pre_process.
  unfold normalized_size_read0_guard.
  rewrite sublist_self; try lia.
  entailer!.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_2 : mpn_normalized_size_entail_wit_2.
Proof.
  unfold mpn_normalized_size_entail_wit_2.
  right.
  intros n_pre val_read0 l n Hlast Hnpos Hnprepos Hnnonneg Hle
    Hguard_old Hval Hbound Hlen Hfullval Hfullbound Hfulllen Hnprepos_again.
  assert (Hval_prefix :
    list_to_Z UINT_MOD (sublist 0 (n - 1) l) = val_read0).
  { pose proof Hval as Hcalc.
    rewrite (sublist_split 0 n (n - 1)) in Hcalc; try lia.
    set (m := n - 1) in Hcalc.
    replace n with (m + 1) in Hcalc by (unfold m; lia).
    rewrite (sublist_single 0 m l) in Hcalc; try lia.
    change (Znth m l 0 = 0) in Hlast.
    rewrite Hlast in Hcalc.
    unfold UINT_MOD in Hcalc.
    rewrite list_to_Z_concat in Hcalc;
      [ | lia
        | apply list_within_bound_sublist; try lia; tauto
        | simpl; lia ].
    simpl in Hcalc.
    rewrite Z.add_0_r in Hcalc.
    change (list_to_Z UINT_MOD (sublist 0 (n - 1) l) = val_read0) in Hcalc.
    exact Hcalc. }
  assert (Hguard : normalized_size_read0_guard (n - 1) l).
  { unfold normalized_size_read0_guard.
    destruct (Z.eq_dec (n - 1) 0) as [Hm | Hm].
    - right.
      replace (Znth 0 l 0) with (Znth (n - 1) l 0) by
        (rewrite Hm; reflexivity).
      exact Hlast.
    - left; lia. }
  pre_process.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3_1 : mpn_normalized_size_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  assert (n = 0) by lia.
  subst n.
  rewrite Zsublist_nil; try lia.
  simpl.
  entailer!.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3_2 : mpn_normalized_size_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  rewrite list_last_to_Znth.
  - rewrite Zlength_sublist; try lia.
    replace (n - 0 - 1) with (n - 1) by lia.
    pose proof (list_within_bound_sublist UINT_MOD l 0 n (ltac:(lia)) (ltac:(lia)) (ltac:(tauto))) as Hbound.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos (sublist 0 n l) (n - 1) (ltac:(lia)) Hbound) as Hznth.
    rewrite Znth_sublist in Hznth; try lia.
    replace (n - 1 + 0) with (n - 1) in Hznth by lia.
    entailer!.
    rewrite Znth_sublist; try lia.
    replace (n - 1 + 0) with (n - 1) by lia.
    lia.
  - intro Hnil.
    pose proof (Zlength_sublist 0 n l) as Hlen.
    rewrite Hnil in Hlen.
    rewrite Zlength_nil in Hlen.
    lia.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_1 : mpn_normalized_size_return_wit_1.
Proof.
  aggressive_pre_process.
  assert (n = 0 \/ n > 0) as Hncase by lia.
  destruct Hncase as [Hn0 | Hnpos].
  - subst n.
    unfold normalized_size_read0_guard in PreH4.
    destruct PreH4 as [Hbad | Hzero]; try lia.
    rewrite Zsublist_nil in PreH5; try lia.
    rewrite list_to_Z_nil in PreH5.
    subst val_read0.
    sep_apply (UIntArray.full_split_to_seg xp_pre 1 n_pre l); try lia.
    sep_apply (UIntArray.seg_to_full xp_pre 0 1 (sublist 0 1 l)).
    sep_apply (UIntArray.seg_to_undef_seg xp_pre 1 n_pre (sublist 1 n_pre l)).
    unfold mpd_store_Z_compact_read0.
    Exists (@nil Z).
    simpl.
    unfold Zmax.
    replace (Z.max 0 1) with 1 by lia.
    replace (sublist 0 1 l) with (Znth 0 l 0 :: nil).
    2:{ replace 1 with (0 + 1) by lia. rewrite (sublist_single 0 0 l ltac:(lia)). reflexivity. }
    rewrite Hzero.
    replace (xp_pre + 0) with xp_pre by lia.
    entailer!.
  - sep_apply (UIntArray.full_split_to_seg xp_pre n n_pre l); try lia.
    sep_apply (UIntArray.seg_to_full xp_pre 0 n (sublist 0 n l)).
    sep_apply (UIntArray.seg_to_undef_seg xp_pre n n_pre (sublist n n_pre l)).
    unfold mpd_store_Z_compact_read0.
    Exists (sublist 0 n l).
    rewrite Zlength_sublist; try lia.
    replace (n - 0) with n by lia.
    assert (Hbound : list_within_bound UINT_MOD (sublist 0 n l)).
    { apply list_within_bound_sublist; try lia; tauto. }
    destruct (sublist 0 n l) eqn:Hsub.
    + pose proof (Zlength_sublist 0 n l) as Hlen.
      rewrite Hsub in Hlen.
      rewrite Zlength_nil in Hlen.
      lia.
    + change (mpd_read0_data (z :: l0)) with (z :: l0).
      unfold Zmax.
      replace (Z.max n 1) with n by lia.
      replace (xp_pre + 0 * sizeof(UINT)) with xp_pre by lia.
      replace (n - 0) with n by lia.
      entailer!.
Qed.

Lemma proof_of_mpn_normalized_size_which_implies_wit_1 : mpn_normalized_size_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z.
  unfold mpd_store_list.
  Intros l.
  Exists l.
  rewrite <- H0.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_35_nonalias : mpz_div_qr_safety_wit_35_nonalias.
Proof.
  pre_process.
  prop_apply (store_int_range (&("nn")) retval).
  Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr (Zabs zd_nonalias) (Zabs size_2)).
  Intros.
  assert (Hdn_pos : retval_2 >= 1).
  { subst retval_2.
    pose proof (is_compact_Z_positive_size (Zabs zd_nonalias) (Zabs size_2)
      H0 ltac:(lia)); lia. }
  entailer!.
  change Int.max_signed with 2147483647 in H.
  lia.
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_36_nonalias : mpz_div_qr_safety_wit_36_nonalias.
Proof.
  pre_process.
  prop_apply (store_int_range (&("nn")) retval).
  Intros.
  entailer!.
  change Int.max_signed with 2147483647 in H.
  lia.
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_38_r_eq_n_read0 : mpz_div_qr_safety_wit_38_r_eq_n_read0.
Proof.
  pre_process.
  prop_apply (store_int_range (&("nn")) retval).
  Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr (Zabs zd_r_eq_n_read0) (Zabs size_2)).
  Intros.
  assert (Hdn_pos : retval_2 >= 1).
  { subst retval_2.
    pose proof (is_compact_Z_positive_size
      (Zabs zd_r_eq_n_read0) (Zabs size_2) H0 ltac:(lia)); lia. }
  entailer!.
  change Int.max_signed with 2147483647 in H.
  lia.
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_39_r_eq_n_read0 : mpz_div_qr_safety_wit_39_r_eq_n_read0.
Proof.
  pre_process.
  prop_apply (store_int_range (&("nn")) retval).
  Intros.
  entailer!.
  change Int.max_signed with 2147483647 in H.
  lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_3_nonalias : mpz_div_qr_entail_wit_3_nonalias.
Proof.
  unfold mpz_div_qr_entail_wit_3_nonalias.
  left.
  intros; Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs zd_nonalias) (Zabs size_2)).
  Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_4_r_eq_n_read0 : mpz_div_qr_entail_wit_4_r_eq_n_read0.
Proof.
  unfold mpz_div_qr_entail_wit_4_r_eq_n_read0.
  left.
  intros; Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr_2
      (Zabs zd_r_eq_n_read0) (Zabs size_2)).
  Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr
      (Zabs zn_r_eq_n_read0) (Zabs size)).
  Intros.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_9_nonalias_q : mpz_div_qr_entail_wit_9_nonalias_q.
Proof.
  unfold mpz_div_qr_entail_wit_9_nonalias_q.
  left; intros.
  pre_process.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size_3)).
  Intros.
  pose proof H as Htr_compact.
  assert (Hzn_abs_pos : 0 < Zabs zn_nonalias).
  { eapply is_compact_Z_size_pos_value_pos.
    - exact PreH11.
    - apply Z.abs_pos; exact PreH10. }
  assert (Hzn_nz : zn_nonalias <> 0) by
    (intro Hzero; subst zn_nonalias; cbn in Hzn_abs_pos; lia).
  pose proof (is_compact_Z_abs_same_value_size_eq
    zn_nonalias size_3 size Hzn_nz Htr_compact PreH11) as Habs_size.
  pose proof (same_sign_same_abs_eq
    zn_nonalias size_3 size Hzn_nz PreH4 PreH15 Habs_size) as Hsize.
  subst size_3.
  assert (Hdn_pos : retval_2 > 0).
  { rewrite PreH8.
    eapply is_compact_Z_positive_size.
    - exact PreH12.
    - pose proof (proj2 (Z.abs_pos zd_nonalias) PreH17); lia. }
  prop_apply (store_int_range
    (&(retval_3 # "__mpz_struct" ->ₛ"_mp_alloc")) cap_3).
  Intros.
  pose proof H0 as Hcap_range.
  change Int.max_signed with 2147483647 in Hcap_range.
  change Int.min_signed with (-2147483648) in Hcap_range.
  assert (Hretval_max : retval <= INT_MAX).
  { change INT_MAX with 2147483647; lia. }
  assert (Hq_undef :
    UIntArray.undef_full ptr_2 ((retval - retval_2) + 1) |--
    optional_q_undef ptr_2 ((retval - retval_2) + 1)).
  { unfold optional_q_undef; Right; entailer!. }
  sep_apply Hq_undef.
  sep_apply
    (mpd_store_Z_compact_view ptr (Zabs zn_nonalias) (Zabs size)).
  Intros l_np.
  subst retval retval_2 x_callee__mp_size.
  Exists ptr_3 cap_2 cap_3 l_np zd_nonalias.
  entailer!.
  sep_apply
    (store_Z_to_optional_store_Z_nonzero q0_nonalias old_q_nonalias);
    [entailer! | entailer!].
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_10_nonalias_noq : mpz_div_qr_entail_wit_10_nonalias_noq.
Proof.
  unfold mpz_div_qr_entail_wit_10_nonalias_noq.
  left; intros.
  pre_process.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size_3)).
  Intros.
  pose proof H as Htr_compact.
  assert (Hzn_abs_pos : 0 < Zabs zn_nonalias).
  { eapply is_compact_Z_size_pos_value_pos.
    - exact PreH8.
    - apply Z.abs_pos; exact PreH7. }
  assert (Hzn_nz : zn_nonalias <> 0) by
    (intro Hzero; subst zn_nonalias; cbn in Hzn_abs_pos; lia).
  pose proof (is_compact_Z_abs_same_value_size_eq
    zn_nonalias size_3 size Hzn_nz Htr_compact PreH8) as Habs_size.
  pose proof (same_sign_same_abs_eq
    zn_nonalias size_3 size Hzn_nz PreH1 PreH12 Habs_size) as Hsize.
  subst size_3.
  assert (Hdn_pos : retval_2 > 0).
  { rewrite PreH5.
    eapply is_compact_Z_positive_size.
    - exact PreH9.
    - pose proof (proj2 (Z.abs_pos zd_nonalias) PreH14); lia. }
  prop_apply (store_int_range
    (&(retval_3 # "__mpz_struct" ->ₛ"_mp_alloc")) cap_3).
  Intros.
  pose proof H0 as Hcap_range.
  change Int.max_signed with 2147483647 in Hcap_range.
  change Int.min_signed with (-2147483648) in Hcap_range.
  assert (Hretval_max : retval <= INT_MAX).
  { change INT_MAX with 2147483647; lia. }
  sep_apply
    (mpd_store_Z_compact_view ptr (Zabs zn_nonalias) (Zabs size)).
  Intros l_np.
  subst retval retval_2.
  Exists ptr_2 cap_2 cap_3 l_np zd_nonalias.
  unfold optional_q_undef.
  entailer!.
  Left; entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_11_r_eq_n_q : mpz_div_qr_entail_wit_11_r_eq_n_q.
Proof.
  unfold mpz_div_qr_entail_wit_11_r_eq_n_q.
  left; intros.
  pre_process.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_r_eq_n_read0) (Zabs size_3)).
  Intros.
  pose proof H as Htr_compact.
  assert (Hzn_abs_pos : 0 < Zabs zn_r_eq_n_read0).
  { eapply is_compact_Z_size_pos_value_pos.
    - exact PreH11.
    - apply Z.abs_pos; exact PreH10. }
  assert (Hzn_nz : zn_r_eq_n_read0 <> 0) by
    (intro Hzero; subst zn_r_eq_n_read0; cbn in Hzn_abs_pos; lia).
  pose proof (is_compact_Z_abs_same_value_size_eq
    zn_r_eq_n_read0 size_3 size Hzn_nz Htr_compact PreH11) as Habs_size.
  pose proof (same_sign_same_abs_eq
    zn_r_eq_n_read0 size_3 size Hzn_nz PreH4 PreH15 Habs_size) as Hsize.
  subst size_3.
  assert (Hdn_pos : retval_2 > 0).
  { rewrite PreH8.
    eapply is_compact_Z_positive_size.
    - exact PreH12.
    - pose proof (proj2 (Z.abs_pos zd_r_eq_n_read0) PreH20); lia. }
  prop_apply (store_int_range
    (&(retval_3 # "__mpz_struct" ->ₛ"_mp_alloc")) cap_3).
  Intros.
  pose proof H0 as Hcap_range.
  change Int.max_signed with 2147483647 in Hcap_range.
  change Int.min_signed with (-2147483648) in Hcap_range.
  assert (Hretval_max : retval <= INT_MAX).
  { change INT_MAX with 2147483647; lia. }
  assert (Hq_undef :
    UIntArray.undef_full ptr_2 ((retval - retval_2) + 1) |--
    optional_q_undef ptr_2 ((retval - retval_2) + 1)).
  { unfold optional_q_undef; Right; entailer!. }
  sep_apply Hq_undef.
  sep_apply
    (mpd_store_Z_compact_view ptr (Zabs zn_r_eq_n_read0) (Zabs size)).
  Intros l_np.
  subst retval retval_2 x_callee__mp_size.
  Exists ptr_3 cap_2 cap_3 l_np zd_r_eq_n_read0.
  entailer!.
  sep_apply
    (store_Z_to_optional_store_Z_nonzero q0_r_eq_n_read0 old_q_r_eq_n_read0);
    [entailer! | entailer!].
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_12_r_eq_n_noq : mpz_div_qr_entail_wit_12_r_eq_n_noq.
Proof.
  unfold mpz_div_qr_entail_wit_12_r_eq_n_noq.
  left; intros.
  pre_process.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_r_eq_n_read0) (Zabs size_3)).
  Intros.
  pose proof H as Htr_compact.
  assert (Hzn_abs_pos : 0 < Zabs zn_r_eq_n_read0).
  { eapply is_compact_Z_size_pos_value_pos.
    - exact PreH8.
    - apply Z.abs_pos; exact PreH7. }
  assert (Hzn_nz : zn_r_eq_n_read0 <> 0) by
    (intro Hzero; subst zn_r_eq_n_read0; cbn in Hzn_abs_pos; lia).
  pose proof (is_compact_Z_abs_same_value_size_eq
    zn_r_eq_n_read0 size_3 size Hzn_nz Htr_compact PreH8) as Habs_size.
  pose proof (same_sign_same_abs_eq
    zn_r_eq_n_read0 size_3 size Hzn_nz PreH1 PreH12 Habs_size) as Hsize.
  subst size_3.
  assert (Hdn_pos : retval_2 > 0).
  { rewrite PreH5.
    eapply is_compact_Z_positive_size.
    - exact PreH9.
    - pose proof (proj2 (Z.abs_pos zd_r_eq_n_read0) PreH17); lia. }
  prop_apply (store_int_range
    (&(retval_3 # "__mpz_struct" ->ₛ"_mp_alloc")) cap_3).
  Intros.
  pose proof H0 as Hcap_range.
  change Int.max_signed with 2147483647 in Hcap_range.
  change Int.min_signed with (-2147483648) in Hcap_range.
  assert (Hretval_max : retval <= INT_MAX).
  { change INT_MAX with 2147483647; lia. }
  sep_apply
    (mpd_store_Z_compact_view ptr (Zabs zn_r_eq_n_read0) (Zabs size)).
  Intros l_np.
  subst retval retval_2.
  Exists ptr_2 cap_2 cap_3 l_np zd_r_eq_n_read0.
  unfold optional_q_undef.
  split_pure_spatial.
  - Left; entailer!.
  - entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_15_1_nonalias_q : mpz_div_qr_entail_wit_15_1_nonalias_q.
Proof.
  unfold mpz_div_qr_entail_wit_15_1_nonalias_q.
  right; intros.
  Exists (- qv).
  pre_process.
  assert (Hqn_pos : qn > 0) by lia.
  assert (Hqcompact : is_compact_Z UINT_MOD qv qn).
  { rewrite <- PreH9.
    eapply is_compact_Z_full_high_nonzero; eauto; lia. }
  assert (Hqv_pos : 0 < qv).
  { eapply is_compact_Z_size_pos_value_pos.
    - exact Hqcompact.
    - lia. }
  assert (Hqprefix :
    list_to_Z UINT_MOD (sublist 0 qn l_q) = qv).
  { rewrite sublist_self by lia; exact PreH9. }
  assert (Hsame_size : same_sign (- qv) (-(qn - 0))).
  { unfold same_sign; right; lia. }
  assert (Hsame_qs : same_sign_or_zero (- qv) qs).
  { unfold same_sign_or_zero, same_sign; right; right; lia. }
  replace (Zabs (- qv)) with qv by
    (rewrite Z.abs_opp, Z.abs_eq; lia).
  replace (Zabs (-(qn - 0))) with qn by lia.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_15_2_nonalias_q : mpz_div_qr_entail_wit_15_2_nonalias_q.
Proof.
  unfold mpz_div_qr_entail_wit_15_2_nonalias_q.
  right; intros.
  Exists qv.
  pre_process.
  assert (Hqn_pos : qn > 0) by lia.
  assert (Hqcompact : is_compact_Z UINT_MOD qv qn).
  { rewrite <- PreH9.
    eapply is_compact_Z_full_high_nonzero; eauto; lia. }
  assert (Hqv_pos : 0 < qv).
  { eapply is_compact_Z_size_pos_value_pos.
    - exact Hqcompact.
    - lia. }
  assert (Hqprefix :
    list_to_Z UINT_MOD (sublist 0 qn l_q) = qv).
  { rewrite sublist_self by lia; exact PreH9. }
  assert (Hsame_size : same_sign qv (qn - 0)).
  { unfold same_sign; left; lia. }
  assert (Hsame_qs : same_sign_or_zero qv qs).
  { unfold same_sign_or_zero, same_sign; right; left; lia. }
  replace (Zabs qv) with qv by (symmetry; apply Z.abs_eq; lia).
  replace (Zabs (qn - 0)) with qn by lia.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_15_3_nonalias_q : mpz_div_qr_entail_wit_15_3_nonalias_q.
Proof.
  unfold mpz_div_qr_entail_wit_15_3_nonalias_q.
  right; intros.
  Exists (- qv).
  pre_process.
  assert (Hqn_pos : qn > 0) by lia.
  assert (Hq_nonneg : 0 <= qv).
  { rewrite <- PreH9.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_q PreH6) as Hb.
    lia. }
  assert (Hd_pos : 0 < Zabs zd_g).
  { apply Z.abs_pos; exact PreH35. }
  assert (Hdiv : Zabs zn_nonalias = qv * Zabs zd_g + rv) by lia.
  assert (Hqcompact : is_compact_Z UINT_MOD qv (qn - 1)).
  { eapply (div_quotient_high_zero_compact l_q qv rv
      (Zabs zn_nonalias) (Zabs zd_g) nn_g dn_g qn);
      eauto; lia. }
  assert (Hqprefix :
    list_to_Z UINT_MOD (sublist 0 (qn - 1) l_q) = qv).
  { transitivity (list_to_Z UINT_MOD l_q).
    - eapply list_to_Z_high_zero_prefix; eauto; lia.
    - exact PreH9. }
  assert (Hqsign : same_sign qv (qn - 1)).
  { unfold same_sign; left; lia. }
  assert (Hsame_size : same_sign (- qv) (-(qn - 1))).
  { eapply same_sign_opp_compact_abs.
    - exact Hqsign.
    - replace (Zabs qv) with qv by (symmetry; apply Z.abs_eq; lia).
      replace (Zabs (qn - 1)) with (qn - 1) by
        (symmetry; apply Z.abs_eq; lia).
      exact Hqcompact. }
  assert (Hsame_qs : same_sign_or_zero (- qv) qs).
  { unfold same_sign_or_zero, same_sign.
    destruct (Z.eq_dec qv 0) as [Hq0 | Hq0].
    - left; lia.
    - right; right; lia. }
  replace (Zabs (- qv)) with qv by
    (rewrite Z.abs_opp, Z.abs_eq; lia).
  replace (Zabs (-(qn - 1))) with (qn - 1) by lia.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_15_4_nonalias_q : mpz_div_qr_entail_wit_15_4_nonalias_q.
Proof.
  unfold mpz_div_qr_entail_wit_15_4_nonalias_q.
  left; intros.
  Exists qv.
  pre_process.
  assert (Hqn_pos : qn > 0) by lia.
  assert (Hq_nonneg : 0 <= qv).
  { rewrite <- PreH9.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_q PreH6) as Hb.
    lia. }
  assert (Hd_pos : 0 < Zabs zd_g).
  { apply Z.abs_pos; exact PreH35. }
  assert (Hdiv : Zabs zn_nonalias = qv * Zabs zd_g + rv) by lia.
  assert (Hqcompact : is_compact_Z UINT_MOD qv (qn - 1)).
  { eapply (div_quotient_high_zero_compact l_q qv rv
      (Zabs zn_nonalias) (Zabs zd_g) nn_g dn_g qn);
      eauto; lia. }
  assert (Hqprefix :
    list_to_Z UINT_MOD (sublist 0 (qn - 1) l_q) = qv).
  { transitivity (list_to_Z UINT_MOD l_q).
    - eapply list_to_Z_high_zero_prefix; eauto; lia.
    - exact PreH9. }
  assert (Hsame_size : same_sign qv (qn - 1)).
  { unfold same_sign; left; lia. }
  assert (Hsame_qs : same_sign_or_zero qv qs).
  { unfold same_sign_or_zero, same_sign.
    destruct (Z.eq_dec qv 0) as [Hq0 | Hq0].
    - left; lia.
    - right; left; lia. }
  replace (Zabs qv) with qv by (symmetry; apply Z.abs_eq; lia).
  replace (Zabs (qn - 1)) with (qn - 1) by lia.
  replace ((nn_g - dn_g) + 1) with qn in * by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact
    qp qn l_q qv); try assumption; try lia.
  entailer!.
  - unfold store_Z at 1.
    Exists qp (qn - 1) qn.
    replace (Zabs qv) with qv by (symmetry; apply Z.abs_eq; lia).
    replace (Zabs (qn - 1)) with (qn - 1) by lia.
    entailer!.
    apply store_int_undef_store_int.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_16_1_r_eq_n_q : mpz_div_qr_entail_wit_16_1_r_eq_n_q.
Proof.
  unfold mpz_div_qr_entail_wit_16_1_r_eq_n_q.
  left; intros.
  Exists (- qv).
  pre_process.
  assert (Hqn_pos : qn > 0) by lia.
  assert (Hqcompact : is_compact_Z UINT_MOD qv qn).
  { rewrite <- PreH9.
    eapply is_compact_Z_full_high_nonzero; eauto; lia. }
  assert (Hqv_pos : 0 < qv).
  { eapply is_compact_Z_size_pos_value_pos.
    - exact Hqcompact.
    - lia. }
  assert (Hqprefix :
    list_to_Z UINT_MOD (sublist 0 qn l_q) = qv).
  { rewrite sublist_self by lia; exact PreH9. }
  assert (Hsame_size : same_sign (- qv) (-(qn - 0))).
  { unfold same_sign; right; lia. }
  assert (Hsame_qs : same_sign_or_zero (- qv) qs).
  { unfold same_sign_or_zero, same_sign; right; right; lia. }
  replace (Zabs (- qv)) with qv by
    (rewrite Z.abs_opp, Z.abs_eq; lia).
  replace (Zabs (-(qn - 0))) with qn by lia.
  replace ((nn_g - dn_g) + 1) with qn in * by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact qp qn l_q qv);
    try assumption; try lia.
  entailer!.
  - unfold store_Z at 1.
    Exists qp (-(qn - 0)) qn.
    replace (Zabs (- qv)) with qv by
      (rewrite Z.abs_opp, Z.abs_eq; lia).
    replace (Zabs (-(qn - 0))) with qn by lia.
    entailer!.
    apply store_int_undef_store_int.
  Unshelve.
  all: try solve [assumption | lia | unfold same_sign; lia | entailer!].
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_16_2_r_eq_n_q : mpz_div_qr_entail_wit_16_2_r_eq_n_q.
Proof.
  unfold mpz_div_qr_entail_wit_16_2_r_eq_n_q.
  left; intros.
  Exists qv.
  pre_process.
  assert (Hqn_pos : qn > 0) by lia.
  assert (Hqcompact : is_compact_Z UINT_MOD qv qn).
  { rewrite <- PreH9.
    eapply is_compact_Z_full_high_nonzero; eauto; lia. }
  assert (Hqv_pos : 0 < qv).
  { eapply is_compact_Z_size_pos_value_pos.
    - exact Hqcompact.
    - lia. }
  assert (Hqprefix :
    list_to_Z UINT_MOD (sublist 0 qn l_q) = qv).
  { rewrite sublist_self by lia; exact PreH9. }
  assert (Hsame_size : same_sign qv (qn - 0)).
  { unfold same_sign; left; lia. }
  assert (Hsame_qs : same_sign_or_zero qv qs).
  { unfold same_sign_or_zero, same_sign; right; left; lia. }
  replace (Zabs qv) with qv by (symmetry; apply Z.abs_eq; lia).
  replace (Zabs (qn - 0)) with qn by lia.
  replace ((nn_g - dn_g) + 1) with qn in * by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact qp qn l_q qv);
    try assumption; try lia.
  entailer!.
  - unfold store_Z at 1.
    Exists qp (qn - 0) qn.
    replace (Zabs qv) with qv by (symmetry; apply Z.abs_eq; lia).
    replace (Zabs (qn - 0)) with qn by lia.
    entailer!.
    apply store_int_undef_store_int.
  Unshelve.
  all: try solve [assumption | lia | unfold same_sign; lia | entailer!].
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_16_3_r_eq_n_q : mpz_div_qr_entail_wit_16_3_r_eq_n_q.
Proof.
  unfold mpz_div_qr_entail_wit_16_3_r_eq_n_q.
  right; intros.
  Exists (- qv).
  pre_process.
  assert (Hqn_pos : qn > 0) by lia.
  assert (Hq_nonneg : 0 <= qv).
  { rewrite <- PreH9.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_q PreH6) as Hb.
    lia. }
  assert (Hd_pos : 0 < Zabs zd_g).
  { apply Z.abs_pos; exact PreH38. }
  assert (Hdiv : Zabs zn_r_eq_n_read0 = qv * Zabs zd_g + rv) by lia.
  assert (Hqcompact : is_compact_Z UINT_MOD qv (qn - 1)).
  { eapply (div_quotient_high_zero_compact l_q qv rv
      (Zabs zn_r_eq_n_read0) (Zabs zd_g) nn_g dn_g qn);
      eauto; lia. }
  assert (Hqprefix :
    list_to_Z UINT_MOD (sublist 0 (qn - 1) l_q) = qv).
  { transitivity (list_to_Z UINT_MOD l_q).
    - eapply list_to_Z_high_zero_prefix; eauto; lia.
    - exact PreH9. }
  assert (Hqsign : same_sign qv (qn - 1)).
  { unfold same_sign; left; lia. }
  assert (Hsame_size : same_sign (- qv) (-(qn - 1))).
  { eapply same_sign_opp_compact_abs.
    - exact Hqsign.
    - replace (Zabs qv) with qv by (symmetry; apply Z.abs_eq; lia).
      replace (Zabs (qn - 1)) with (qn - 1) by
        (symmetry; apply Z.abs_eq; lia).
      exact Hqcompact. }
  assert (Hsame_qs : same_sign_or_zero (- qv) qs).
  { unfold same_sign_or_zero, same_sign.
    destruct (Z.eq_dec qv 0) as [Hq0 | Hq0].
    - left; lia.
    - right; right; lia. }
  replace (Zabs (- qv)) with qv by
    (rewrite Z.abs_opp, Z.abs_eq; lia).
  replace (Zabs (-(qn - 1))) with (qn - 1) by lia.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_16_4_r_eq_n_q : mpz_div_qr_entail_wit_16_4_r_eq_n_q.
Proof.
  unfold mpz_div_qr_entail_wit_16_4_r_eq_n_q.
  right; intros.
  Exists qv.
  pre_process.
  assert (Hqn_pos : qn > 0) by lia.
  assert (Hq_nonneg : 0 <= qv).
  { rewrite <- PreH9.
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_q PreH6) as Hb.
    lia. }
  assert (Hd_pos : 0 < Zabs zd_g).
  { apply Z.abs_pos; exact PreH38. }
  assert (Hdiv : Zabs zn_r_eq_n_read0 = qv * Zabs zd_g + rv) by lia.
  assert (Hqcompact : is_compact_Z UINT_MOD qv (qn - 1)).
  { eapply (div_quotient_high_zero_compact l_q qv rv
      (Zabs zn_r_eq_n_read0) (Zabs zd_g) nn_g dn_g qn);
      eauto; lia. }
  assert (Hqprefix :
    list_to_Z UINT_MOD (sublist 0 (qn - 1) l_q) = qv).
  { transitivity (list_to_Z UINT_MOD l_q).
    - eapply list_to_Z_high_zero_prefix; eauto; lia.
    - exact PreH9. }
  assert (Hsame_size : same_sign qv (qn - 1)).
  { unfold same_sign; left; lia. }
  assert (Hsame_qs : same_sign_or_zero qv qs).
  { unfold same_sign_or_zero, same_sign.
    destruct (Z.eq_dec qv 0) as [Hq0 | Hq0].
    - left; lia.
    - right; left; lia. }
  replace (Zabs qv) with qv by (symmetry; apply Z.abs_eq; lia).
  replace (Zabs (qn - 1)) with (qn - 1) by lia.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_19_1_nonalias_q_done : mpz_div_qr_entail_wit_19_1_nonalias_q_done.
Proof.
  pre_process.
  assert (Hdecomp :
    Zabs zn_nonalias = Zabs zd_nonalias * qv + rv).
  {
    rewrite <- PreH17, <- PreH25, PreH14.
    ring.
  }
  assert (Hmod :
    rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  {
    apply Z.mod_unique with (q := qv).
    - rewrite <- PreH17. lia.
    - exact Hdecomp.
  }
  assert (Habs_r :
    Zabs (- rv) = list_to_Z UINT_MOD l_rem).
  {
    rewrite Z.abs_opp, Z.abs_eq by lia.
    symmetry; exact PreH13.
  }
  assert (Habs_mod :
    Zabs (- rv) = Zabs zn_nonalias mod Zabs zd_nonalias).
  {
    rewrite Z.abs_opp, Z.abs_eq by lia.
    exact Hmod.
  }
  assert (Hsame_tr : same_sign_or_zero (- rv) tr_size).
  {
    unfold same_sign_or_zero, same_sign.
    destruct (Z.eq_dec rv 0) as [Hrv | Hrv].
    - left; lia.
    - right; right; split; lia.
  }
  prop_apply
    (mpd_store_Z_compact_ret_ok
      np (list_to_Z UINT_MOD l_rem) retval (- rv) Habs_r).
  Intros.
  assert (Hsame_field : same_sign (- rv) (- retval)).
  {
    unfold mpz_div_qr_ret_ok in H.
    unfold same_sign.
    destruct (Z.eq_dec retval 0) as [Hretval | Hretval].
    - left; lia.
    - right; lia.
  }
  assert (Habs_size : Zabs (- retval) = retval).
  {
    rewrite Z.abs_opp, Z.abs_eq by lia.
    reflexivity.
  }
  assert (Hdn_nn : dn_g <= nn_g) by lia.
  assert (Hnn_cap : nn_g <= tr_cap) by lia.
  sep_apply
    (mpz_div_qr_pack_remainder_store
      tr np (list_to_Z UINT_MOD l_rem)
      (- retval) retval dn_g nn_g tr_cap l_tail (- rv)
      Habs_r Habs_size Hsame_field PreH3 Hdn_nn Hnn_cap).
  Exists (- rv).
  entailer!.
  all: try exact Hsame_tr.
  all: try (rewrite Z.abs_opp, Z.abs_eq by lia;
            rewrite Z.rem_mod_nonneg by lia;
            exact Hmod).
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_19_2_nonalias_q_done : mpz_div_qr_entail_wit_19_2_nonalias_q_done.
Proof.
  pre_process.
  assert (Hdecomp :
    Zabs zn_nonalias = Zabs zd_nonalias * qv + rv).
  {
    rewrite <- PreH17, <- PreH25, PreH14.
    ring.
  }
  assert (Hmod :
    rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  {
    apply Z.mod_unique with (q := qv).
    - rewrite <- PreH17. lia.
    - exact Hdecomp.
  }
  assert (Habs_r :
    Zabs rv = list_to_Z UINT_MOD l_rem).
  {
    rewrite Z.abs_eq by lia.
    symmetry; exact PreH13.
  }
  assert (Habs_mod :
    Zabs rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  {
    rewrite Z.abs_eq by lia.
    exact Hmod.
  }
  assert (Hsame_tr : same_sign_or_zero rv tr_size).
  {
    unfold same_sign_or_zero, same_sign.
    right; left; split; lia.
  }
  prop_apply
    (mpd_store_Z_compact_ret_ok
      np (list_to_Z UINT_MOD l_rem) retval rv Habs_r).
  Intros.
  assert (Hsame_field : same_sign rv retval).
  {
    unfold same_sign.
    left; split; lia.
  }
  assert (Habs_size : Zabs retval = retval).
  {
    rewrite Z.abs_eq by lia.
    reflexivity.
  }
  assert (Hdn_nn : dn_g <= nn_g) by lia.
  assert (Hnn_cap : nn_g <= tr_cap) by lia.
  sep_apply
    (mpz_div_qr_pack_remainder_store
      tr np (list_to_Z UINT_MOD l_rem)
      retval retval dn_g nn_g tr_cap l_tail rv
      Habs_r Habs_size Hsame_field PreH3 Hdn_nn Hnn_cap).
  Exists rv.
  entailer!.
  all: try exact Hsame_tr.
  all: try (rewrite Z.abs_eq by lia;
            rewrite Z.rem_mod_nonneg by lia;
            exact Hmod).
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_20_1_nonalias_noq : mpz_div_qr_entail_wit_20_1_nonalias_noq.
Proof.
  pre_process.
  assert (Hdecomp :
    Zabs zn_nonalias = Zabs zd_nonalias * qv + rv).
  {
    rewrite <- PreH15, <- PreH24, PreH12.
    ring.
  }
  assert (Hmod :
    rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  {
    apply Z.mod_unique with (q := qv).
    - rewrite <- PreH15. lia.
    - exact Hdecomp.
  }
  assert (Habs_r :
    Zabs (- rv) = list_to_Z UINT_MOD l_rem).
  {
    rewrite Z.abs_opp, Z.abs_eq by lia.
    symmetry; exact PreH11.
  }
  assert (Habs_mod :
    Zabs (- rv) = Zabs zn_nonalias mod Zabs zd_nonalias).
  {
    rewrite Z.abs_opp, Z.abs_eq by lia.
    exact Hmod.
  }
  assert (Hsame_tr : same_sign_or_zero (- rv) tr_size).
  {
    unfold same_sign_or_zero, same_sign.
    destruct (Z.eq_dec rv 0) as [Hrv | Hrv].
    - left; lia.
    - right; right; split; lia.
  }
  prop_apply
    (mpd_store_Z_compact_ret_ok
      np (list_to_Z UINT_MOD l_rem) retval (- rv) Habs_r).
  Intros.
  assert (Hsame_field : same_sign (- rv) (- retval)).
  {
    unfold mpz_div_qr_ret_ok in H.
    unfold same_sign.
    destruct (Z.eq_dec retval 0) as [Hretval | Hretval].
    - left; lia.
    - right; lia.
  }
  assert (Habs_size : Zabs (- retval) = retval).
  {
    rewrite Z.abs_opp, Z.abs_eq by lia.
    reflexivity.
  }
  assert (Hdn_nn : dn_g <= nn_g) by lia.
  assert (Hnn_cap : nn_g <= tr_cap) by lia.
  sep_apply
    (mpz_div_qr_pack_remainder_store
      tr np (list_to_Z UINT_MOD l_rem)
      (- retval) retval dn_g nn_g tr_cap l_tail (- rv)
      Habs_r Habs_size Hsame_field PreH3 Hdn_nn Hnn_cap).
  Exists (- rv).
  entailer!.
  all: try exact Hsame_tr.
  all: try (rewrite Z.abs_opp, Z.abs_eq by lia;
            rewrite Z.rem_mod_nonneg by lia;
            exact Hmod).
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_20_2_nonalias_noq : mpz_div_qr_entail_wit_20_2_nonalias_noq.
Proof.
  pre_process.
  assert (Hdecomp :
    Zabs zn_nonalias = Zabs zd_nonalias * qv + rv).
  {
    rewrite <- PreH15, <- PreH24, PreH12.
    ring.
  }
  assert (Hmod :
    rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  {
    apply Z.mod_unique with (q := qv).
    - rewrite <- PreH15. lia.
    - exact Hdecomp.
  }
  assert (Habs_r :
    Zabs rv = list_to_Z UINT_MOD l_rem).
  {
    rewrite Z.abs_eq by lia.
    symmetry; exact PreH11.
  }
  assert (Habs_mod :
    Zabs rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  {
    rewrite Z.abs_eq by lia.
    exact Hmod.
  }
  assert (Hsame_tr : same_sign_or_zero rv tr_size).
  {
    unfold same_sign_or_zero, same_sign.
    right; left; split; lia.
  }
  prop_apply
    (mpd_store_Z_compact_ret_ok
      np (list_to_Z UINT_MOD l_rem) retval rv Habs_r).
  Intros.
  assert (Hsame_field : same_sign rv retval).
  {
    unfold same_sign.
    left; split; lia.
  }
  assert (Habs_size : Zabs retval = retval).
  {
    rewrite Z.abs_eq by lia.
    reflexivity.
  }
  assert (Hdn_nn : dn_g <= nn_g) by lia.
  assert (Hnn_cap : nn_g <= tr_cap) by lia.
  sep_apply
    (mpz_div_qr_pack_remainder_store
      tr np (list_to_Z UINT_MOD l_rem)
      retval retval dn_g nn_g tr_cap l_tail rv
      Habs_r Habs_size Hsame_field PreH3 Hdn_nn Hnn_cap).
  Exists rv.
  entailer!.
  all: try exact Hsame_tr.
  all: try (rewrite Z.abs_eq by lia;
            rewrite Z.rem_mod_nonneg by lia;
            exact Hmod).
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_21_1_r_eq_n_q_done : mpz_div_qr_entail_wit_21_1_r_eq_n_q_done.
Proof.
  pre_process.
  assert (Hdecomp :
    Zabs zn_r_eq_n_read0 = Zabs zd_r_eq_n_read0 * qv + rv).
  {
    rewrite <- PreH17, <- PreH27, PreH14.
    ring.
  }
  assert (Hmod :
    rv = Zabs zn_r_eq_n_read0 mod Zabs zd_r_eq_n_read0).
  {
    apply Z.mod_unique with (q := qv).
    - rewrite <- PreH17. lia.
    - exact Hdecomp.
  }
  assert (Habs_r :
    Zabs (- rv) = list_to_Z UINT_MOD l_rem).
  {
    rewrite Z.abs_opp, Z.abs_eq by lia.
    symmetry; exact PreH13.
  }
  assert (Hsame_tr : same_sign_or_zero (- rv) tr_size).
  {
    unfold same_sign_or_zero, same_sign.
    destruct (Z.eq_dec rv 0) as [Hrv | Hrv].
    - left; lia.
    - right; right; split; lia.
  }
  prop_apply
    (mpd_store_Z_compact_read0_ret_ok
      np (list_to_Z UINT_MOD l_rem) retval (- rv) Habs_r).
  Intros.
  assert (Hsame_field : same_sign (- rv) (- retval)).
  {
    unfold mpz_div_qr_ret_ok in H.
    unfold same_sign.
    destruct (Z.eq_dec retval 0) as [Hretval | Hretval].
    - left; lia.
    - right; lia.
  }
  assert (Habs_size : Zabs (- retval) = retval).
  {
    rewrite Z.abs_opp, Z.abs_eq by lia.
    reflexivity.
  }
  assert (Hdn_nn : dn_g <= nn_g) by lia.
  assert (Hnn_cap : nn_g <= tr_cap) by lia.
  assert (Hused_mid : Zmax retval 1 <= dn_g).
  { unfold Zmax; lia. }
  sep_apply
    (store_Z_read0_from_compact_read0_tail
      tr np (- rv) (- retval) (list_to_Z UINT_MOD l_rem) retval
      tr_cap dn_g nn_g l_tail
      (eq_sym Habs_r) (eq_sym Habs_size) Hused_mid
      Hdn_nn Hnn_cap Hsame_field).
  Exists (- rv).
  entailer!.
  all: try exact Hsame_tr.
  all: try (rewrite Z.abs_opp, Z.abs_eq by lia;
            rewrite Z.rem_mod_nonneg by lia;
            exact Hmod).
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_21_2_r_eq_n_q_done : mpz_div_qr_entail_wit_21_2_r_eq_n_q_done.
Proof.
  pre_process.
  assert (Hdecomp :
    Zabs zn_r_eq_n_read0 = Zabs zd_r_eq_n_read0 * qv + rv).
  {
    rewrite <- PreH17, <- PreH27, PreH14.
    ring.
  }
  assert (Hmod :
    rv = Zabs zn_r_eq_n_read0 mod Zabs zd_r_eq_n_read0).
  {
    apply Z.mod_unique with (q := qv).
    - rewrite <- PreH17. lia.
    - exact Hdecomp.
  }
  assert (Habs_r :
    Zabs rv = list_to_Z UINT_MOD l_rem).
  {
    rewrite Z.abs_eq by lia.
    symmetry; exact PreH13.
  }
  assert (Hsame_tr : same_sign_or_zero rv tr_size).
  {
    unfold same_sign_or_zero, same_sign.
    right; left; split; lia.
  }
  prop_apply
    (mpd_store_Z_compact_read0_ret_ok
      np (list_to_Z UINT_MOD l_rem) retval rv Habs_r).
  Intros.
  assert (Hsame_field : same_sign rv retval).
  {
    unfold same_sign.
    left; split; lia.
  }
  assert (Habs_size : Zabs retval = retval).
  {
    rewrite Z.abs_eq by lia.
    reflexivity.
  }
  assert (Hdn_nn : dn_g <= nn_g) by lia.
  assert (Hnn_cap : nn_g <= tr_cap) by lia.
  assert (Hused_mid : Zmax retval 1 <= dn_g).
  { unfold Zmax; lia. }
  sep_apply
    (store_Z_read0_from_compact_read0_tail
      tr np rv retval (list_to_Z UINT_MOD l_rem) retval
      tr_cap dn_g nn_g l_tail
      (eq_sym Habs_r) (eq_sym Habs_size) Hused_mid
      Hdn_nn Hnn_cap Hsame_field).
  Exists rv.
  entailer!.
  all: try exact Hsame_tr.
  all: try (rewrite Z.abs_eq by lia;
            rewrite Z.rem_mod_nonneg by lia;
            exact Hmod).
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_22_1_r_eq_n_noq : mpz_div_qr_entail_wit_22_1_r_eq_n_noq.
Proof.
  pre_process.
  assert (Hdecomp :
    Zabs zn_r_eq_n_read0 = Zabs zd_r_eq_n_read0 * qv + rv).
  {
    rewrite <- PreH15, <- PreH27, PreH12.
    ring.
  }
  assert (Hmod :
    rv = Zabs zn_r_eq_n_read0 mod Zabs zd_r_eq_n_read0).
  {
    apply Z.mod_unique with (q := qv).
    - rewrite <- PreH15. lia.
    - exact Hdecomp.
  }
  assert (Habs_r :
    Zabs (- rv) = list_to_Z UINT_MOD l_rem).
  {
    rewrite Z.abs_opp, Z.abs_eq by lia.
    symmetry; exact PreH11.
  }
  assert (Hsame_tr : same_sign_or_zero (- rv) tr_size).
  {
    unfold same_sign_or_zero, same_sign.
    destruct (Z.eq_dec rv 0) as [Hrv | Hrv].
    - left; lia.
    - right; right; split; lia.
  }
  prop_apply
    (mpd_store_Z_compact_read0_ret_ok
      np (list_to_Z UINT_MOD l_rem) retval (- rv) Habs_r).
  Intros.
  assert (Hsame_field : same_sign (- rv) (- retval)).
  {
    unfold mpz_div_qr_ret_ok in H.
    unfold same_sign.
    destruct (Z.eq_dec retval 0) as [Hretval | Hretval].
    - left; lia.
    - right; lia.
  }
  assert (Habs_size : Zabs (- retval) = retval).
  {
    rewrite Z.abs_opp, Z.abs_eq by lia.
    reflexivity.
  }
  assert (Hdn_nn : dn_g <= nn_g) by lia.
  assert (Hnn_cap : nn_g <= tr_cap) by lia.
  assert (Hused_mid : Zmax retval 1 <= dn_g).
  { unfold Zmax; lia. }
  sep_apply
    (store_Z_read0_from_compact_read0_tail
      tr np (- rv) (- retval) (list_to_Z UINT_MOD l_rem) retval
      tr_cap dn_g nn_g l_tail
      (eq_sym Habs_r) (eq_sym Habs_size) Hused_mid
      Hdn_nn Hnn_cap Hsame_field).
  Exists (- rv).
  entailer!.
  all: try exact Hsame_tr.
  all: try (rewrite Z.abs_opp, Z.abs_eq by lia;
            rewrite Z.rem_mod_nonneg by lia;
            exact Hmod).
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_22_2_r_eq_n_noq : mpz_div_qr_entail_wit_22_2_r_eq_n_noq.
Proof.
  pre_process.
  assert (Hdecomp :
    Zabs zn_r_eq_n_read0 = Zabs zd_r_eq_n_read0 * qv + rv).
  {
    rewrite <- PreH15, <- PreH27, PreH12.
    ring.
  }
  assert (Hmod :
    rv = Zabs zn_r_eq_n_read0 mod Zabs zd_r_eq_n_read0).
  {
    apply Z.mod_unique with (q := qv).
    - rewrite <- PreH15. lia.
    - exact Hdecomp.
  }
  assert (Habs_r :
    Zabs rv = list_to_Z UINT_MOD l_rem).
  {
    rewrite Z.abs_eq by lia.
    symmetry; exact PreH11.
  }
  assert (Hsame_tr : same_sign_or_zero rv tr_size).
  {
    unfold same_sign_or_zero, same_sign.
    right; left; split; lia.
  }
  prop_apply
    (mpd_store_Z_compact_read0_ret_ok
      np (list_to_Z UINT_MOD l_rem) retval rv Habs_r).
  Intros.
  assert (Hsame_field : same_sign rv retval).
  {
    unfold same_sign.
    left; split; lia.
  }
  assert (Habs_size : Zabs retval = retval).
  {
    rewrite Z.abs_eq by lia.
    reflexivity.
  }
  assert (Hdn_nn : dn_g <= nn_g) by lia.
  assert (Hnn_cap : nn_g <= tr_cap) by lia.
  assert (Hused_mid : Zmax retval 1 <= dn_g).
  { unfold Zmax; lia. }
  sep_apply
    (store_Z_read0_from_compact_read0_tail
      tr np rv retval (list_to_Z UINT_MOD l_rem) retval
      tr_cap dn_g nn_g l_tail
      (eq_sym Habs_r) (eq_sym Habs_size) Hused_mid
      Hdn_nn Hnn_cap Hsame_field).
  Exists rv.
  entailer!.
  all: try exact Hsame_tr.
  all: try (rewrite Z.abs_eq by lia;
            rewrite Z.rem_mod_nonneg by lia;
            exact Hmod).
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_30_1_nonalias_q_rem : mpz_div_qr_entail_wit_30_1_nonalias_q_rem.
Proof.
  unfold mpz_div_qr_entail_wit_30_1_nonalias_q_rem.
  right; intros.
  subst zd_g.
  assert (Habsdiv :
    Zabs zn_nonalias = qv * Zabs zd_nonalias + rv) by lia.
  assert (Hmod : rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_nonalias zn_nonalias zd_nonalias qtr rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH40.
    - exact PreH32.
    - exact PreH34.
    - exact PreH37.
    - exact PreH33.
    - exact PreH8.
    - exact PreH9.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH19.
    - exact PreH20. }
  assert (Hmath :
    mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias qtr rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  Exists qtr rtr.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_30_2_nonalias_noq_rem : mpz_div_qr_entail_wit_30_2_nonalias_noq_rem.
Proof.
  unfold mpz_div_qr_entail_wit_30_2_nonalias_noq_rem.
  right; intros.
  subst zd_g.
  assert (Habsdiv :
    Zabs zn_nonalias = qv * Zabs zd_nonalias + rv) by lia.
  assert (Hmod : rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  pose proof
    (list_to_Z_bound UINT_MOD UINT_MOD_pos l_q PreH11) as Hqbound.
  assert (Hqv_nonneg : 0 <= qv) by lia.
  set (qout := if Z_lt_dec qs 0 then - qv else qv).
  assert (Hqsign : same_sign_or_zero qout qs).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia.
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia. }
  assert (Hqabs : Zabs qout = qv).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - rewrite Z.abs_opp, Z.abs_eq; lia.
    - rewrite Z.abs_eq; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_nonalias zn_nonalias zd_nonalias qout rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH38.
    - exact PreH30.
    - exact PreH32.
    - exact PreH35.
    - exact PreH31.
    - exact Hqsign.
    - exact Hqabs.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH17.
    - exact PreH18. }
  assert (Hmath :
    mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias qout rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  Exists qout rtr.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_30_3_nonalias_q_rem : mpz_div_qr_entail_wit_30_3_nonalias_q_rem.
Proof.
  unfold mpz_div_qr_entail_wit_30_3_nonalias_q_rem.
  right; intros.
  subst zd_g.
  assert (Habsdiv :
    Zabs zn_nonalias = qv * Zabs zd_nonalias + rv) by lia.
  assert (Hmod : rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_nonalias zn_nonalias zd_nonalias qtr rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH40.
    - exact PreH32.
    - exact PreH34.
    - exact PreH37.
    - exact PreH33.
    - exact PreH8.
    - exact PreH9.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH19.
    - exact PreH20. }
  assert (Hmath :
    mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias qtr rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  Exists qtr rtr.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_30_4_nonalias_noq_rem : mpz_div_qr_entail_wit_30_4_nonalias_noq_rem.
Proof.
  unfold mpz_div_qr_entail_wit_30_4_nonalias_noq_rem.
  right; intros.
  subst zd_g.
  assert (Habsdiv :
    Zabs zn_nonalias = qv * Zabs zd_nonalias + rv) by lia.
  assert (Hmod : rv = Zabs zn_nonalias mod Zabs zd_nonalias).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  pose proof
    (list_to_Z_bound UINT_MOD UINT_MOD_pos l_q PreH11) as Hqbound.
  assert (Hqv_nonneg : 0 <= qv) by lia.
  set (qout := if Z_lt_dec qs 0 then - qv else qv).
  assert (Hqsign : same_sign_or_zero qout qs).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia.
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia. }
  assert (Hqabs : Zabs qout = qv).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - rewrite Z.abs_opp, Z.abs_eq; lia.
    - rewrite Z.abs_eq; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_nonalias zn_nonalias zd_nonalias qout rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH38.
    - exact PreH30.
    - exact PreH32.
    - exact PreH35.
    - exact PreH31.
    - exact Hqsign.
    - exact Hqabs.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH17.
    - exact PreH18. }
  assert (Hmath :
    mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias qout rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  Exists qout rtr.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_31_1_r_eq_n_q_rem : mpz_div_qr_entail_wit_31_1_r_eq_n_q_rem.
Proof.
  unfold mpz_div_qr_entail_wit_31_1_r_eq_n_q_rem.
  right; intros.
  subst zd_g.
  subst r0_r_eq_n_read0.
  assert (Habsdiv :
    Zabs zn_r_eq_n_read0 = qv * Zabs zd_r_eq_n_read0 + rv) by lia.
  assert (Hmod : rv = Zabs zn_r_eq_n_read0 mod Zabs zd_r_eq_n_read0).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  assert (Hzn_nonzero : zn_r_eq_n_read0 <> 0).
  { assert (Hnn_pos : 0 < nn_g) by lia.
    pose proof (is_compact_Z_size_pos_value_pos
      (Zabs zn_r_eq_n_read0) nn_g PreH32 Hnn_pos) as Habs_pos.
    intro Hzero; subst zn_r_eq_n_read0; cbn in Habs_pos; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 qtr rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH41.
    - exact Hzn_nonzero.
    - exact PreH35.
    - exact PreH38.
    - exact PreH34.
    - exact PreH8.
    - exact PreH9.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH19.
    - exact PreH20. }
  assert (Hmath :
    mpz_div_qr_math mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 qtr rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  Exists qtr rtr.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_31_2_r_eq_n_noq_rem : mpz_div_qr_entail_wit_31_2_r_eq_n_noq_rem.
Proof.
  unfold mpz_div_qr_entail_wit_31_2_r_eq_n_noq_rem.
  right; intros.
  subst zd_g.
  subst r0_r_eq_n_read0.
  assert (Habsdiv :
    Zabs zn_r_eq_n_read0 = qv * Zabs zd_r_eq_n_read0 + rv) by lia.
  assert (Hmod : rv = Zabs zn_r_eq_n_read0 mod Zabs zd_r_eq_n_read0).
  { apply Z.mod_unique with (q := qv); lia. }
  assert (Hrabs : Zabs rtr = rv).
  { rewrite Z.rem_mod_nonneg in PreH4 by lia; lia. }
  assert (Hzn_nonzero : zn_r_eq_n_read0 <> 0).
  { assert (Hnn_pos : 0 < nn_g) by lia.
    pose proof (is_compact_Z_size_pos_value_pos
      (Zabs zn_r_eq_n_read0) nn_g PreH30 Hnn_pos) as Habs_pos.
    intro Hzero; subst zn_r_eq_n_read0; cbn in Habs_pos; lia. }
  pose proof
    (list_to_Z_bound UINT_MOD UINT_MOD_pos l_q PreH11) as Hqbound.
  assert (Hqv_nonneg : 0 <= qv) by lia.
  set (qout := if Z_lt_dec qs 0 then - qv else qv).
  assert (Hqsign : same_sign_or_zero qout qs).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia.
    - unfold same_sign_or_zero, same_sign.
      destruct (Z.eq_dec qv 0); lia. }
  assert (Hqabs : Zabs qout = qv).
  { unfold qout.
    destruct (Z_lt_dec qs 0) as [Hqs | Hqs].
    - rewrite Z.abs_opp, Z.abs_eq; lia.
    - rewrite Z.abs_eq; lia. }
  assert (Htrunc :
    mpz_div_qr_math_trunc
      mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 qout rtr).
  { eapply mpz_div_qr_math_from_abs_trunc_signs
      with (qv := qv) (rv := rv) (ns := tr_size)
           (ds := d_size) (qs := qs).
    - unfold GMP_DIV_TRUNC; lia.
    - exact PreH39.
    - exact Hzn_nonzero.
    - exact PreH33.
    - exact PreH36.
    - exact PreH32.
    - exact Hqsign.
    - exact Hqabs.
    - exact PreH3.
    - exact Hrabs.
    - exact Habsdiv.
    - exact PreH17.
    - exact PreH18. }
  assert (Hmath :
    mpz_div_qr_math mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 qout rtr).
  { unfold mpz_div_qr_math; left; exact Htrunc. }
  Exists qout rtr.
  entailer!.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_1_nonalias_done : mpz_div_qr_return_wit_1_nonalias_done.
Proof.
  pre_process; Left; Exists qout rout; entailer!.
  unfold mpz_div_qr_ret_ok in *; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_2_nonalias_done : mpz_div_qr_return_wit_2_nonalias_done.
Proof.
  pre_process; Left; Exists qout rout; entailer!.
  unfold mpz_div_qr_ret_ok in *; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_3_r_eq_n_done : mpz_div_qr_return_wit_3_r_eq_n_done.
Proof.
  pre_process; Right; Exists qout rout; entailer!.
  unfold mpz_div_qr_ret_ok in *; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_4_r_eq_n_done : mpz_div_qr_return_wit_4_r_eq_n_done.
Proof.
  pre_process; Right; Exists qout rout; entailer!.
  unfold mpz_div_qr_ret_ok in *; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_5_nonalias : mpz_div_qr_return_wit_5_nonalias.
Proof.
  pre_process; Exists 0 zn_nonalias.
  assert (Hzn_nz : zn_nonalias <> 0).
  { assert (0 < Zabs zn_nonalias).
    { eapply is_compact_Z_size_pos_value_pos; eauto; lia. }
    lia. }
  assert (Habs_lt : Zabs zn_nonalias < Zabs zd_nonalias).
  { eapply is_compact_Z_size_lt_value_lt; eauto; lia. }
  assert (Hmath : mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias 0 zn_nonalias).
  { eapply (mpz_div_qr_math_small_remainder
      mode0_nonalias zn_nonalias zd_nonalias size size_2).
    - unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    - unfold mpz_div_qr_small_q0_case, GMP_DIV_TRUNC; lia.
    - exact Hzn_nz.
    - assumption.
    - assumption.
    - assumption.
    - exact Habs_lt. }
  sep_apply (store_Z_from_fields d0_nonalias ptr size_2 cap_2 zd_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_zero_from_fields q0_nonalias ptr_2 size_3 cap_3 old_q_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_to_optional_store_Z_nonzero q0_nonalias 0); [ | entailer!].
  sep_apply (store_Z_to_optional_store_Z_nonzero r0_nonalias zn_nonalias); [ | entailer!].
  entailer!.
  unfold mpz_div_qr_ret_ok; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_6_r_eq_n_read0 : mpz_div_qr_return_wit_6_r_eq_n_read0.
Proof.
  pre_process; Exists 0 zn_r_eq_n_read0.
  assert (Hzn_nz : zn_r_eq_n_read0 <> 0).
  { assert (0 < Zabs zn_r_eq_n_read0).
    { eapply is_compact_Z_size_pos_value_pos; eauto; lia. }
    lia. }
  assert (Habs_lt : Zabs zn_r_eq_n_read0 < Zabs zd_r_eq_n_read0).
  { eapply is_compact_Z_size_lt_value_lt; eauto; lia. }
  assert (Hmath :
    mpz_div_qr_math mode0_r_eq_n_read0 zn_r_eq_n_read0
      zd_r_eq_n_read0 0 zn_r_eq_n_read0).
  { eapply (mpz_div_qr_math_small_remainder
      mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 size size_2).
    - unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    - unfold mpz_div_qr_small_q0_case, GMP_DIV_TRUNC; lia.
    - exact Hzn_nz.
    - assumption.
    - assumption.
    - assumption.
    - exact Habs_lt. }
  sep_apply (store_Z_to_store_Z_read0_nonzero
    n0_r_eq_n_read0 zn_r_eq_n_read0 Hzn_nz).
  sep_apply (store_Z_from_fields d0_r_eq_n_read0 ptr size_2 cap_2 zd_r_eq_n_read0);
    [ | entailer! | entailer!].
  sep_apply (store_Z_zero_from_fields q0_r_eq_n_read0 ptr_2 size_3 cap_3
    old_q_r_eq_n_read0); [ | entailer! | entailer!].
  sep_apply (store_Z_to_optional_store_Z_nonzero q0_r_eq_n_read0 0);
    [ | entailer!].
  entailer!.
  unfold mpz_div_qr_ret_ok; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_7_nonalias : mpz_div_qr_return_wit_7_nonalias.
Proof.
  pre_process; Exists 0 zn_nonalias.
  prop_apply_p (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr
    (Zabs zn_nonalias) (Zabs size) ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs zd_nonalias) (Zabs size_2)).
  Intros.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap zn_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2 zd_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_zero_from_fields q0_nonalias ptr_3 size_3 cap_3 old_q_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_to_optional_store_Z_nonzero q0_nonalias 0); [ | entailer!].
  entailer!.
  - unfold optional_store_Z. Left. entailer!.
  - unfold mpz_div_qr_ret_ok; lia.
  - unfold mpz_div_qr_math; left.
    unfold mpz_div_qr_math_trunc, GMP_DIV_TRUNC.
    repeat split; try lia; try ring.
    + eapply is_compact_Z_size_lt_value_lt; eauto; lia.
    + right; apply same_sign_refl.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_8_nonalias : mpz_div_qr_return_wit_8_nonalias.
Proof.
  pre_process; Exists 0 zn_nonalias.
  assert (Hzn_nz : zn_nonalias <> 0).
  { assert (0 < Zabs zn_nonalias).
    { eapply is_compact_Z_size_pos_value_pos; eauto; lia. }
    lia. }
  assert (Habs_lt : Zabs zn_nonalias < Zabs zd_nonalias).
  { eapply is_compact_Z_size_lt_value_lt; eauto; lia. }
  assert (Hmath : mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias 0 zn_nonalias).
  { eapply (mpz_div_qr_math_small_remainder
      mode0_nonalias zn_nonalias zd_nonalias size size_2).
    - unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    - unfold mpz_div_qr_small_q0_case, GMP_DIV_TRUNC; lia.
    - exact Hzn_nz.
    - assumption.
    - assumption.
    - assumption.
    - exact Habs_lt. }
  sep_apply (store_Z_from_fields d0_nonalias ptr size_2 cap_2 zd_nonalias);
    [ | entailer! | entailer!].
  sep_apply (optional_store_Z_null_change q0_nonalias old_q_nonalias 0); [ | entailer!].
  sep_apply (store_Z_to_optional_store_Z_nonzero r0_nonalias zn_nonalias); [ | entailer!].
  entailer!.
  unfold mpz_div_qr_ret_ok; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_9_r_eq_n_read0 : mpz_div_qr_return_wit_9_r_eq_n_read0.
Proof.
  pre_process; Exists 0 zn_r_eq_n_read0.
  assert (Hzn_nz : zn_r_eq_n_read0 <> 0).
  { assert (0 < Zabs zn_r_eq_n_read0).
    { eapply is_compact_Z_size_pos_value_pos; eauto; lia. }
    lia. }
  assert (Habs_lt : Zabs zn_r_eq_n_read0 < Zabs zd_r_eq_n_read0).
  { eapply is_compact_Z_size_lt_value_lt; eauto; lia. }
  assert (Hmath :
    mpz_div_qr_math mode0_r_eq_n_read0 zn_r_eq_n_read0
      zd_r_eq_n_read0 0 zn_r_eq_n_read0).
  { eapply (mpz_div_qr_math_small_remainder
      mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 size size_2).
    - unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    - unfold mpz_div_qr_small_q0_case, GMP_DIV_TRUNC; lia.
    - exact Hzn_nz.
    - assumption.
    - assumption.
    - assumption.
    - exact Habs_lt. }
  sep_apply (store_Z_to_store_Z_read0_nonzero
    n0_r_eq_n_read0 zn_r_eq_n_read0 Hzn_nz).
  sep_apply (store_Z_from_fields d0_r_eq_n_read0 ptr size_2 cap_2 zd_r_eq_n_read0);
    [ | entailer! | entailer!].
  sep_apply (optional_store_Z_null_change q0_r_eq_n_read0
    old_q_r_eq_n_read0 0); [ | entailer!].
  entailer!.
  unfold mpz_div_qr_ret_ok; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_10_nonalias : mpz_div_qr_return_wit_10_nonalias.
Proof.
  pre_process; Exists 0 zn_nonalias.
  prop_apply_p (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr
    (Zabs zn_nonalias) (Zabs size) ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs zd_nonalias) (Zabs size_2)).
  Intros.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap zn_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2 zd_nonalias);
    [ | entailer! | entailer!].
  sep_apply (optional_store_Z_null_change q0_nonalias old_q_nonalias 0); [ | entailer!].
  sep_apply (optional_store_Z_null_change r0_nonalias old_r_nonalias zn_nonalias); [ | entailer!].
  entailer!.
  - unfold mpz_div_qr_ret_ok; lia.
  - unfold mpz_div_qr_math; left.
    unfold mpz_div_qr_math_trunc, GMP_DIV_TRUNC.
    repeat split; try lia; try ring.
    + eapply is_compact_Z_size_lt_value_lt; eauto; lia.
    + right; apply same_sign_refl.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_11_nonalias : mpz_div_qr_return_wit_11_nonalias.
Proof.
  pre_process; Exists 0 0.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  assert (Hzn0 : zn_nonalias = 0).
  { pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
      (Zabs zn_nonalias) (Zabs size) H) as [_ [[Hsize Hz] | [Hsize _]]]; lia. }
  subst zn_nonalias.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap 0);
    [ | entailer! | entailer!].
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2 zd_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_zero_from_fields q0_nonalias ptr_3 size_3 cap_3 old_q_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_zero_from_fields r0_nonalias ptr_4 size_4 cap_4 old_r_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_to_optional_store_Z_nonzero q0_nonalias 0); [ | entailer!].
  sep_apply (store_Z_to_optional_store_Z_nonzero r0_nonalias 0); [ | entailer!].
  entailer!.
  - unfold mpz_div_qr_ret_ok; lia.
  - eapply mpz_div_qr_math_zero_all_modes.
    + unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    + assumption.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_12_r_eq_n_read0 : mpz_div_qr_return_wit_12_r_eq_n_read0.
Proof.
  unfold mpz_div_qr_return_wit_12_r_eq_n_read0.
  left.
  intros.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
    (Zabs zn_r_eq_n_read0) (Zabs size) PreH4)
    as [_ [[Hsize Hzn] | [Hsize _]]];
  exfalso; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_13_nonalias : mpz_div_qr_return_wit_13_nonalias.
Proof.
  pre_process; Exists 0 0.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  assert (Hzn0 : zn_nonalias = 0).
  { pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
      (Zabs zn_nonalias) (Zabs size) H) as [_ [[Hsize Hz] | [Hsize _]]]; lia. }
  subst zn_nonalias.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap 0);
    [ | entailer! | entailer!].
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2 zd_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_zero_from_fields r0_nonalias ptr_3 size_3 cap_3 old_r_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_to_optional_store_Z_nonzero r0_nonalias 0); [ | entailer!].
  entailer!.
  - unfold optional_store_Z. Left. entailer!.
  - unfold mpz_div_qr_ret_ok; lia.
  - eapply mpz_div_qr_math_zero_all_modes.
    + unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    + assumption.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_14_r_eq_n_read0 : mpz_div_qr_return_wit_14_r_eq_n_read0.
Proof.
  unfold mpz_div_qr_return_wit_14_r_eq_n_read0.
  left.
  intros.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
    (Zabs zn_r_eq_n_read0) (Zabs size) PreH2)
    as [_ [[Hsize Hzn] | [Hsize _]]];
  exfalso; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_15_nonalias : mpz_div_qr_return_wit_15_nonalias.
Proof.
  pre_process; Exists 0 0.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  assert (Hzn0 : zn_nonalias = 0).
  { pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
      (Zabs zn_nonalias) (Zabs size) H) as [_ [[Hsize Hz] | [Hsize _]]]; lia. }
  subst zn_nonalias.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap 0);
    [ | entailer! | entailer!].
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2 zd_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_zero_from_fields q0_nonalias ptr_3 size_3 cap_3 old_q_nonalias);
    [ | entailer! | entailer!].
  sep_apply (store_Z_to_optional_store_Z_nonzero q0_nonalias 0); [ | entailer!].
  sep_apply (optional_store_Z_null_change r0_nonalias old_r_nonalias 0); [ | entailer!].
  entailer!.
  - unfold mpz_div_qr_ret_ok; lia.
  - eapply mpz_div_qr_math_zero_all_modes.
    + unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    + assumption.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_16_nonalias : mpz_div_qr_return_wit_16_nonalias.
Proof.
  pre_process; Exists 0 0.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  assert (Hzn0 : zn_nonalias = 0).
  { pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
      (Zabs zn_nonalias) (Zabs size) H) as [_ [[Hsize Hz] | [Hsize _]]]; lia. }
  subst zn_nonalias.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap 0);
    [ | entailer! | entailer!].
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2 zd_nonalias);
    [ | entailer! | entailer!].
  sep_apply (optional_store_Z_null_change q0_nonalias old_q_nonalias 0); [ | entailer!].
  sep_apply (optional_store_Z_null_change r0_nonalias old_r_nonalias 0); [ | entailer!].
  entailer!.
  - unfold mpz_div_qr_ret_ok; lia.
  - eapply mpz_div_qr_math_zero_all_modes.
    + unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    + assumption.
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_11_nonalias_pure : mpz_div_qr_partial_solve_wit_11_nonalias_pure.
Proof.
  unfold mpz_div_qr_partial_solve_wit_11_nonalias_pure.
  right; intros; split_pures.
  - dump_pre_spatial.
    destruct (Z_lt_ge_dec size 0).
    + rewrite Z.abs_neq in PreH17 by lia; lia.
    + lia.
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_12_r_eq_n_read0_pure : mpz_div_qr_partial_solve_wit_12_r_eq_n_read0_pure.
Proof.
  unfold mpz_div_qr_partial_solve_wit_12_r_eq_n_read0_pure.
  right; intros; split_pures.
  - dump_pre_spatial.
    destruct (Z_lt_ge_dec size 0).
    + rewrite Z.abs_neq in PreH17 by lia; lia.
    + lia.
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_13_nonalias_pure : mpz_div_qr_partial_solve_wit_13_nonalias_pure.
Proof.
  unfold mpz_div_qr_partial_solve_wit_13_nonalias_pure.
  right; intros; split_pures.
  - dump_pre_spatial.
    pose proof (is_compact_Z_positive_size (Zabs zd_nonalias) (Zabs size)
      PreH16 ltac:(pose proof (Z.abs_nonneg zd_nonalias); lia)).
    destruct (Z_lt_ge_dec size 0).
    + rewrite Z.abs_neq in PreH18 by lia; lia.
    + lia.
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_14_r_eq_n_read0_pure : mpz_div_qr_partial_solve_wit_14_r_eq_n_read0_pure.
Proof.
  unfold mpz_div_qr_partial_solve_wit_14_r_eq_n_read0_pure.
  right; intros; split_pures.
  - dump_pre_spatial.
    pose proof (is_compact_Z_positive_size (Zabs zd_r_eq_n_read0) (Zabs size)
      PreH16 ltac:(pose proof (Z.abs_nonneg zd_r_eq_n_read0); lia)).
    destruct (Z_lt_ge_dec size 0).
    + rewrite Z.abs_neq in PreH18 by lia; lia.
    + lia.
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_28_nonalias_q_pure : mpz_div_qr_partial_solve_wit_28_nonalias_q_pure.
Proof.
  unfold mpz_div_qr_partial_solve_wit_28_nonalias_q_pure.
  left; intros.
  prop_apply (store_int_range (&("nn")) retval).
  Intros.
  assert (Hdn_pos : retval_2 >= 1).
  { subst retval_2.
    pose proof (is_compact_Z_positive_size (Zabs zd_nonalias) (Zabs size_2)
      PreH10 ltac:(lia)); lia. }
  change Int.max_signed with 2147483647 in H.
  entailer!.
  rewrite (unsigned_last_nbits_eq (retval - retval_2 + 1) 64).
  2: { change (2 ^ 64) with 18446744073709551616; lia. }
  rewrite unsigned_last_nbits_eq.
  2: { change (2 ^ 64) with 18446744073709551616; nia. }
  reflexivity.
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_29_r_eq_n_q_pure : mpz_div_qr_partial_solve_wit_29_r_eq_n_q_pure.
Proof.
  unfold mpz_div_qr_partial_solve_wit_29_r_eq_n_q_pure.
  left; intros.
  prop_apply (store_int_range (&("nn")) retval).
  Intros.
  assert (Hdn_pos : retval_2 >= 1).
  { subst retval_2.
    pose proof (is_compact_Z_positive_size (Zabs zd_r_eq_n_read0) (Zabs size_2)
      PreH10 ltac:(lia)); lia. }
  change Int.max_signed with 2147483647 in H.
  entailer!.
  rewrite (unsigned_last_nbits_eq (retval - retval_2 + 1) 64).
  2: { change (2 ^ 64) with 18446744073709551616; lia. }
  rewrite unsigned_last_nbits_eq.
  2: { change (2 ^ 64) with 18446744073709551616; nia. }
  reflexivity.
Qed.

Lemma proof_of_mpz_tdiv_r_entail_wit_1 : mpz_tdiv_r_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  unfold optional_store_Z.
  Left.
  entailer!.
Qed.

Lemma proof_of_mpz_tdiv_r_return_wit_1 : mpz_tdiv_r_return_wit_1.
Proof.
  pre_process.
  Exists qv_2 rv_2.
  entailer!.
  unfold optional_store_Z.
  Split.
  - Intros_p Hnull. entailer!.
  - Intros_p Hnonnull. entailer!.
Qed.
