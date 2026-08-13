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

Lemma proof_of_mpz_div_qr_entail_wit_16_1_r_eq_n_q : mpz_div_qr_entail_wit_16_1_r_eq_n_q.
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
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact qp qn l_q qv);
    try assumption; try lia.
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

Lemma proof_of_mpz_div_qr_entail_wit_16_2_r_eq_n_q : mpz_div_qr_entail_wit_16_2_r_eq_n_q.
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
  sep_apply (UIntArray_full_to_mpd_store_Z_compact_exact qp qn l_q qv);
    try assumption; try lia.
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

Lemma proof_of_mpz_div_qr_entail_wit_16_3_r_eq_n_q : mpz_div_qr_entail_wit_16_3_r_eq_n_q.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (- qv).
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

Lemma proof_of_mpz_div_qr_entail_wit_16_4_r_eq_n_q : mpz_div_qr_entail_wit_16_4_r_eq_n_q.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists qv.
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
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_19_1_nonalias_q_done : mpz_div_qr_entail_wit_19_1_nonalias_q_done.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hdecomp :
    Zabs zn_nonalias = Zabs zd_nonalias * qv + rv).
  {
    rewrite <- PreH26, PreH14, PreH17.
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
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try exact Hsame_tr;
      try (rewrite Z.abs_opp, Z.abs_eq by lia;
           rewrite Z.rem_mod_nonneg by lia;
           exact Hmod);
      try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_19_2_nonalias_q_done : mpz_div_qr_entail_wit_19_2_nonalias_q_done.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hdecomp :
    Zabs zn_nonalias = Zabs zd_nonalias * qv + rv).
  {
    rewrite <- PreH26, PreH14, PreH17.
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
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try exact Hsame_tr;
      try (rewrite Z.abs_eq by lia;
           rewrite Z.rem_mod_nonneg by lia;
           exact Hmod);
      try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_20_1_nonalias_noq : mpz_div_qr_entail_wit_20_1_nonalias_noq.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try exact Hsame_tr;
      try (rewrite Z.abs_opp, Z.abs_eq by lia;
           rewrite Z.rem_mod_nonneg by lia;
           exact Hmod);
      try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_20_2_nonalias_noq : mpz_div_qr_entail_wit_20_2_nonalias_noq.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try exact Hsame_tr;
      try (rewrite Z.abs_eq by lia;
           rewrite Z.rem_mod_nonneg by lia;
           exact Hmod);
      try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_21_1_r_eq_n_q_done : mpz_div_qr_entail_wit_21_1_r_eq_n_q_done.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hdecomp :
    Zabs zn_r_eq_n_read0 = Zabs zd_r_eq_n_read0 * qv + rv).
  {
    rewrite <- PreH28, PreH14, PreH17.
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
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try exact Hsame_tr;
      try (rewrite Z.abs_opp, Z.abs_eq by lia;
           rewrite Z.rem_mod_nonneg by lia;
           exact Hmod);
      try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_21_2_r_eq_n_q_done : mpz_div_qr_entail_wit_21_2_r_eq_n_q_done.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hdecomp :
    Zabs zn_r_eq_n_read0 = Zabs zd_r_eq_n_read0 * qv + rv).
  {
    rewrite <- PreH28, PreH14, PreH17.
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
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try exact Hsame_tr;
      try (rewrite Z.abs_eq by lia;
           rewrite Z.rem_mod_nonneg by lia;
           exact Hmod);
      try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_22_1_r_eq_n_noq : mpz_div_qr_entail_wit_22_1_r_eq_n_noq.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try exact Hsame_tr;
      try (rewrite Z.abs_opp, Z.abs_eq by lia;
           rewrite Z.rem_mod_nonneg by lia;
           exact Hmod);
      try lia.
Qed.

Lemma proof_of_mpz_div_qr_entail_wit_22_2_r_eq_n_noq : mpz_div_qr_entail_wit_22_2_r_eq_n_noq.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try exact Hsame_tr;
      try (rewrite Z.abs_eq by lia;
           rewrite Z.rem_mod_nonneg by lia;
           exact Hmod);
      try lia.
Qed.
