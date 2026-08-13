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

Lemma proof_of_mpn_normalized_size_entail_wit_1_split_goal_1 :
  mpn_normalized_size_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite sublist_self; try lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_1_split_goal_2 :
  mpn_normalized_size_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold normalized_size_read0_guard.
  left.
  lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_1 :
  mpn_normalized_size_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_2_split_goal_1 :
  mpn_normalized_size_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH7 as Hcalc.
  rewrite (sublist_split 0 n (n - 1)) in Hcalc; try lia.
  set (m := n - 1) in Hcalc.
  replace n with (m + 1) in Hcalc by (unfold m; lia).
  rewrite (sublist_single 0 m l) in Hcalc; try lia.
  change (Znth m l 0 = 0) in PreH1.
  rewrite PreH1 in Hcalc.
  unfold UINT_MOD in Hcalc.
  rewrite list_to_Z_concat in Hcalc;
    [ | lia
      | apply list_within_bound_sublist; try lia; tauto
      | simpl; lia ].
  simpl in Hcalc.
  rewrite Z.add_0_r in Hcalc.
  change (list_to_Z UINT_MOD (sublist 0 (n - 1) l) = val_read0) in Hcalc.
  exact Hcalc.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_2_split_goal_2 :
  mpn_normalized_size_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold normalized_size_read0_guard.
  destruct (Z.eq_dec (n - 1) 0) as [Hm | Hm].
  - right.
    replace (Znth 0 l 0) with (Znth (n - 1) l 0) by
      (rewrite Hm; reflexivity).
    exact PreH1.
  - left; lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_2 :
  mpn_normalized_size_entail_wit_2.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_normalized_size_entail_wit_2_split_goal_1.
  + Goal_apply proof_of_mpn_normalized_size_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3_1_split_goal_1 :
  mpn_normalized_size_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n = 0) by lia.
  subst n.
  rewrite Zsublist_nil; try lia.
  simpl.
  lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3_1 :
  mpn_normalized_size_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_normalized_size_entail_wit_3_1_split_goal_1.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3_2_split_goal_1 :
  mpn_normalized_size_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite list_last_to_Znth.
  - rewrite Zlength_sublist; try lia.
    replace (n - 0 - 1) with (n - 1) by lia.
    pose proof (list_within_bound_sublist UINT_MOD l 0 n (ltac:(lia)) (ltac:(lia)) (ltac:(tauto))) as Hbound.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos (sublist 0 n l) (n - 1) (ltac:(lia)) Hbound) as Hznth.
    rewrite Znth_sublist in Hznth; try lia.
    replace (n - 1 + 0) with (n - 1) in Hznth by lia.
    rewrite Znth_sublist; try lia.
    replace (n - 1 + 0) with (n - 1) by lia.
    lia.
  - intro Hnil.
    pose proof (Zlength_sublist 0 n l) as Hlen.
    rewrite Hnil in Hlen.
    rewrite Zlength_nil in Hlen.
    lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3_2 :
  mpn_normalized_size_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_normalized_size_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_1_split_goal_spatial :
  mpn_normalized_size_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
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
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      rewrite list_to_Z_nil, Zlength_nil.
      lia.
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
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial.
        split; [exact PreH5 |].
        split; [exact PreH8 |].
        split; [exact Hbound | reflexivity].
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_1 :
  mpn_normalized_size_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_normalized_size_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpn_normalized_size_which_implies_wit_1 : mpn_normalized_size_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z.
  unfold mpd_store_list.
  Intros l.
  destruct H as [Hval Hbound].
  Exists l.
  rewrite <- H0.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity.
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_35_nonalias : mpz_div_qr_safety_wit_35_nonalias.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_int_range (&("nn")) retval).
  Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr (Zabs zd_nonalias) (Zabs size_2)).
  Intros.
  assert (Hdn_pos : retval_2 >= 1).
  { subst retval_2.
    pose proof (is_compact_Z_positive_size (Zabs zd_nonalias) (Zabs size_2)
      H0 ltac:(lia)); lia. }
  repeat split_pures; dump_pre_spatial.
  all: change Int.min_signed with (-2147483648) in H.
  all: change Int.max_signed with 2147483647 in H.
  all: lia.
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_36_nonalias_split_goal_1 :
  mpz_div_qr_safety_wit_36_nonalias_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_int_range (&("nn")) retval).
  Intros.
  repeat split_pures; dump_pre_spatial.
  all: change Int.min_signed with (-2147483648) in H.
  all: change Int.max_signed with 2147483647 in H.
  all: lia.
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_36_nonalias_split_goal_2 :
  mpz_div_qr_safety_wit_36_nonalias_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_36_nonalias : mpz_div_qr_safety_wit_36_nonalias.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpz_div_qr_safety_wit_36_nonalias_split_goal_1.
  + Goal_apply proof_of_mpz_div_qr_safety_wit_36_nonalias_split_goal_2.
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_38_r_eq_n_read0 : mpz_div_qr_safety_wit_38_r_eq_n_read0.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_int_range (&("nn")) retval).
  Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr (Zabs zd_r_eq_n_read0) (Zabs size_2)).
  Intros.
  assert (Hdn_pos : retval_2 >= 1).
  { subst retval_2.
    pose proof (is_compact_Z_positive_size
      (Zabs zd_r_eq_n_read0) (Zabs size_2) H0 ltac:(lia)); lia. }
  repeat split_pures; dump_pre_spatial.
  all: change Int.min_signed with (-2147483648) in H.
  all: change Int.max_signed with 2147483647 in H.
  all: lia.
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_39_r_eq_n_read0_split_goal_1 :
  mpz_div_qr_safety_wit_39_r_eq_n_read0_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_int_range (&("nn")) retval).
  Intros.
  repeat split_pures; dump_pre_spatial.
  all: change Int.min_signed with (-2147483648) in H.
  all: change Int.max_signed with 2147483647 in H.
  all: lia.
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_39_r_eq_n_read0_split_goal_2 :
  mpz_div_qr_safety_wit_39_r_eq_n_read0_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_qr_safety_wit_39_r_eq_n_read0 : mpz_div_qr_safety_wit_39_r_eq_n_read0.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpz_div_qr_safety_wit_39_r_eq_n_read0_split_goal_1.
  + Goal_apply proof_of_mpz_div_qr_safety_wit_39_r_eq_n_read0_split_goal_2.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_3_nonalias : mpz_div_qr_entail_wit_3_nonalias.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros; Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs zd_nonalias) (Zabs size_2)).
  Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_4_r_eq_n_read0 : mpz_div_qr_entail_wit_4_r_eq_n_read0.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros; Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr_2
      (Zabs zd_r_eq_n_read0) (Zabs size_2)).
  Intros.
  prop_apply
    (mpd_store_Z_to_is_compact_Z ptr
    (Zabs zn_r_eq_n_read0) (Zabs size)).
  Intros.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_9_nonalias_q : mpz_div_qr_entail_wit_9_nonalias_q.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  { unfold optional_q_undef.
    Right.
    split_pure_spatial.
    - cancel.
    - dump_pre_spatial; exact PreH1. }
  sep_apply Hq_undef.
  sep_apply
    (mpd_store_Z_compact_view ptr (Zabs zn_nonalias) (Zabs size)).
  Intros l_np.
  destruct H1 as [Hnp_val [Hnp_last Hnp_bound]].
  subst retval retval_2 x_callee__mp_size.
  Exists ptr_3 cap_2 cap_3 l_np zd_nonalias.
  split_pure_spatial.
  - sep_apply
      (store_Z_to_optional_store_Z_nonzero q0_nonalias old_q_nonalias).
    + cancel.
    + assumption.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_10_nonalias_noq : mpz_div_qr_entail_wit_10_nonalias_noq.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  destruct H1 as [Hnp_val [Hnp_last Hnp_bound]].
  subst retval retval_2.
  Exists ptr_2 cap_2 cap_3 l_np zd_nonalias.
  unfold optional_q_undef.
  split_pure_spatial.
  - Left.
    split_pure_spatial.
    + normalize.
      repeat cancel.
    + dump_pre_spatial; reflexivity.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_11_r_eq_n_q : mpz_div_qr_entail_wit_11_r_eq_n_q.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  { unfold optional_q_undef.
    Right.
    split_pure_spatial.
    - cancel.
    - dump_pre_spatial; exact PreH1. }
  sep_apply Hq_undef.
  sep_apply
    (mpd_store_Z_compact_view ptr (Zabs zn_r_eq_n_read0) (Zabs size)).
  Intros l_np.
  destruct H1 as [Hnp_val [Hnp_last Hnp_bound]].
  subst retval retval_2 x_callee__mp_size.
  Exists ptr_3 cap_2 cap_3 l_np zd_r_eq_n_read0.
  split_pure_spatial.
  - sep_apply
      (store_Z_to_optional_store_Z_nonzero
        q0_r_eq_n_read0 old_q_r_eq_n_read0).
    + cancel.
    + assumption.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_12_r_eq_n_noq : mpz_div_qr_entail_wit_12_r_eq_n_noq.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  destruct H1 as [Hnp_val [Hnp_last Hnp_bound]].
  subst retval retval_2.
  Exists ptr_2 cap_2 cap_3 l_np zd_r_eq_n_read0.
  unfold optional_q_undef.
  split_pure_spatial.
  - Left.
    split_pure_spatial.
    + normalize.
      repeat cancel.
    + dump_pre_spatial; reflexivity.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_15_1_nonalias_q : mpz_div_qr_entail_wit_15_1_nonalias_q.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (- qv).
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
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact
    qp qn l_q qv); try assumption; try lia.
  split_pure_spatial.
  - pose proof (store_Z_from_fields tq qp (-(qn - 0)) qn (-qv)
      ltac:(rewrite Z.abs_opp, Z.abs_eq by lia; lia) Hsame_size) as Hstore.
    replace (Zabs (-qv)) with qv in Hstore by
      (rewrite Z.abs_opp, Z.abs_eq; lia).
    replace (Zabs (-(qn - 0))) with qn in Hstore by lia.
    sep_apply Hstore.
    sep_apply store_int_undef_store_int.
    normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_15_2_nonalias_q : mpz_div_qr_entail_wit_15_2_nonalias_q.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists qv.
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
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact
    qp qn l_q qv); try assumption; try lia.
  split_pure_spatial.
  - pose proof (store_Z_from_fields tq qp (qn - 0) qn qv
      ltac:(rewrite Z.abs_eq by lia; lia) Hsame_size) as Hstore.
    replace (Zabs qv) with qv in Hstore by
      (symmetry; apply Z.abs_eq; lia).
    replace (Zabs (qn - 0)) with qn in Hstore by lia.
    sep_apply Hstore.
    sep_apply store_int_undef_store_int.
    normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_15_3_nonalias_q : mpz_div_qr_entail_wit_15_3_nonalias_q.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (- qv).
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
  replace ((nn_g - dn_g) + 1) with qn in * by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact
    qp qn l_q qv); try assumption; try lia.
  split_pure_spatial.
  - pose proof (store_Z_from_fields tq qp (-(qn - 1)) qn (-qv)
      ltac:(rewrite Z.abs_opp, Z.abs_eq by lia; lia) Hsame_size) as Hstore.
    replace (Zabs (-qv)) with qv in Hstore by
      (rewrite Z.abs_opp, Z.abs_eq; lia).
    replace (Zabs (-(qn - 1))) with (qn - 1) in Hstore by lia.
    sep_apply Hstore.
    sep_apply store_int_undef_store_int.
    normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_15_4_nonalias_q : mpz_div_qr_entail_wit_15_4_nonalias_q.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists qv.
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
  split_pure_spatial.
  - pose proof (store_Z_from_fields tq qp (qn - 1) qn qv
      ltac:(rewrite Z.abs_eq by lia; lia) Hsame_size) as Hstore.
    replace (Zabs qv) with qv in Hstore by
      (symmetry; apply Z.abs_eq; lia).
    replace (Zabs (qn - 1)) with (qn - 1) in Hstore by lia.
    sep_apply Hstore.
    sep_apply store_int_undef_store_int.
    normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
  Unshelve.
  all: try solve [assumption | lia | unfold same_sign; lia | cancel].
Qed.
