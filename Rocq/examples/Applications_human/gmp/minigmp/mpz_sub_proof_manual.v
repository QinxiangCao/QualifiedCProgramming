From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_sub_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_sub_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_sub_safety_wit_4_nonalias_split_goal_1 : mpz_sub_safety_wit_4_nonalias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (store_Z_remain_size_int_range r_pre (Zabs n_nonalias - Zabs m_nonalias) retval).
  Intros.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_sub_safety_wit_4_nonalias : mpz_sub_safety_wit_4_nonalias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_sub_safety_wit_4_nonalias_split_goal_1.
Qed.

Lemma proof_of_mpz_sub_safety_wit_6_r_eq_a_split_goal_1 : mpz_sub_safety_wit_6_r_eq_a_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_sub_safety_wit_6_r_eq_a : mpz_sub_safety_wit_6_r_eq_a.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_sub_safety_wit_6_r_eq_a_split_goal_1.
Qed.

Lemma proof_of_mpz_sub_safety_wit_8_nonalias_split_goal_1 : mpz_sub_safety_wit_8_nonalias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (store_Z_remain_size_int_range r_pre (Zabs n_nonalias + Zabs m_nonalias) retval).
  Intros.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_sub_safety_wit_8_nonalias : mpz_sub_safety_wit_8_nonalias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_sub_safety_wit_8_nonalias_split_goal_1.
Qed.

Lemma proof_of_mpz_sub_safety_wit_10_r_eq_a_split_goal_1 : mpz_sub_safety_wit_10_r_eq_a_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_sub_safety_wit_10_r_eq_a : mpz_sub_safety_wit_10_r_eq_a.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_sub_safety_wit_10_r_eq_a_split_goal_1.
Qed.

Lemma proof_of_mpz_sub_entail_wit_1_r_eq_a : mpz_sub_entail_wit_1_r_eq_a.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Intros ptr old_size cap bptr bsize bcap.
  prop_apply (store_int_range (&(a_pre # "__mpz_struct" ->ₛ "_mp_alloc")) cap).
  Intros.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  Exists bptr ptr old_size bcap bsize cap.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial.
    all: try assumption; try reflexivity.
    all: unfold same_sign in *.
    all: pose proof (proj1 (Z.lxor_nonneg size size_2) ltac:(lia)).
    all: assert (0 <= Z.lxor old_size bsize) by (rewrite Z.lxor_nonneg; lia).
    all: lia.
Qed.

Lemma proof_of_mpz_sub_entail_wit_2_r_eq_a : mpz_sub_entail_wit_2_r_eq_a.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Intros ptr old_size cap bptr bsize bcap.
  replace (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) with (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  prop_apply (store_int_range (&(a_pre # "__mpz_struct" ->ₛ "_mp_alloc")) cap).
  Intros.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  Exists bptr ptr old_size bcap bsize cap.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial.
    all: try assumption; try reflexivity.
    all: unfold same_sign in *.
    all: assert (~ 0 <= Z.lxor old_size bsize) by
      (rewrite Z.lxor_nonneg;
       destruct (lxor_negative_implies_opposite_signs_simple size size_2 ltac:(lia));
       lia).
    all: lia.
Qed.

Lemma proof_of_mpz_sub_return_wit_1_nonalias_split_goal_1 : mpz_sub_return_wit_1_nonalias_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n_nonalias >= 0 /\ m_nonalias >= 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_nonneg_implies_same_sign size size_2 ltac:(lia)); lia. }
  dump_pre_spatial.
  replace (n_nonalias - m_nonalias) with (Zabs n_nonalias - Zabs m_nonalias) by lia.
  exact PreH1.
Qed.

Lemma proof_of_mpz_sub_return_wit_1_nonalias_split_goal_spatial : mpz_sub_return_wit_1_nonalias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n_nonalias >= 0 /\ m_nonalias >= 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_nonneg_implies_same_sign size size_2 ltac:(lia)); lia. }
  assert (Habs: Zabs (Zabs n_nonalias - Zabs m_nonalias) = Zabs (n_nonalias - m_nonalias)) by lia.
  rewrite Habs.
  repeat cancel.
Qed.

Lemma proof_of_mpz_sub_return_wit_1_nonalias : mpz_sub_return_wit_1_nonalias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_sub_return_wit_1_nonalias_split_goal_spatial.
  - Goal_apply proof_of_mpz_sub_return_wit_1_nonalias_split_goal_1.
Qed.

Lemma proof_of_mpz_sub_return_wit_2_nonalias_split_goal_1 : mpz_sub_return_wit_2_nonalias_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_sub_return_wit_2_nonalias_split_goal_2 : mpz_sub_return_wit_2_nonalias_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n_nonalias < 0 /\ m_nonalias < 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_nonneg_implies_same_sign size size_2 ltac:(lia)); lia. }
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs (Zabs n_nonalias - Zabs m_nonalias)) (Zabs retval)).
  Intros.
  dump_pre_spatial.
  replace (n_nonalias - m_nonalias) with (-(Zabs n_nonalias - Zabs m_nonalias)) by lia.
  apply same_sign_opp_compact_abs; [exact PreH1 | assumption].
Qed.

Lemma proof_of_mpz_sub_return_wit_2_nonalias_split_goal_spatial : mpz_sub_return_wit_2_nonalias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n_nonalias < 0 /\ m_nonalias < 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_nonneg_implies_same_sign size size_2 ltac:(lia)); lia. }
  assert (Habs: Zabs (Zabs n_nonalias - Zabs m_nonalias) = Zabs (n_nonalias - m_nonalias)) by lia.
  rewrite Habs.
  rewrite Z.abs_opp.
  repeat cancel.
Qed.

Lemma proof_of_mpz_sub_return_wit_2_nonalias : mpz_sub_return_wit_2_nonalias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_sub_return_wit_2_nonalias_split_goal_spatial.
  - Goal_apply proof_of_mpz_sub_return_wit_2_nonalias_split_goal_1.
  - Goal_apply proof_of_mpz_sub_return_wit_2_nonalias_split_goal_2.
Qed.

Lemma proof_of_mpz_sub_return_wit_3_r_eq_a : mpz_sub_return_wit_3_r_eq_a.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst r_pre.
  assert (za_r_eq_a >= 0 /\ zb_r_eq_a >= 0) as Hnm.
  { unfold same_sign in *.
    pose proof (proj1 (Z.lxor_nonneg old_size bsize) ltac:(lia)).
    lia. }
  replace (Zabs (Zabs za_r_eq_a - Zabs zb_r_eq_a)) with (Zabs (za_r_eq_a - zb_r_eq_a)) in * by lia.
  replace (Zabs za_r_eq_a - Zabs zb_r_eq_a) with (za_r_eq_a - zb_r_eq_a) in * by lia.
  unfold store_Z at 1.
  Exists ptr; Exists rn_v; Exists cap.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_mpz_sub_return_wit_4_r_eq_a : mpz_sub_return_wit_4_r_eq_a.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst r_pre.
  assert (za_r_eq_a < 0 /\ zb_r_eq_a < 0) as Hnm.
  { unfold same_sign in *.
    destruct (lxor_nonneg_implies_same_sign old_size bsize ltac:(lia)); lia. }
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs (Zabs za_r_eq_a - Zabs zb_r_eq_a)) (Zabs rn_v)).
  Intros.
  assert (same_sign (za_r_eq_a - zb_r_eq_a) (- rn_v)) as Hsg.
  { replace (za_r_eq_a - zb_r_eq_a) with (-(Zabs za_r_eq_a - Zabs zb_r_eq_a)) by lia.
    apply same_sign_opp_compact_abs; assumption. }
  replace (Zabs (Zabs za_r_eq_a - Zabs zb_r_eq_a)) with (Zabs (za_r_eq_a - zb_r_eq_a)) in * by lia.
  unfold store_Z at 1.
  Exists ptr; Exists (- rn_v); Exists cap.
  replace (Zabs (- rn_v)) with (Zabs rn_v) by lia.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_sub_return_wit_5_nonalias_split_goal_1 : mpz_sub_return_wit_5_nonalias_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n_nonalias >= 0 /\ m_nonalias < 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_negative_implies_opposite_signs_simple size size_2 ltac:(lia)); lia. }
  dump_pre_spatial.
  replace (n_nonalias - m_nonalias) with (Zabs n_nonalias + Zabs m_nonalias) by lia.
  exact PreH1.
Qed.

Lemma proof_of_mpz_sub_return_wit_5_nonalias_split_goal_spatial : mpz_sub_return_wit_5_nonalias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n_nonalias >= 0 /\ m_nonalias < 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_negative_implies_opposite_signs_simple size size_2 ltac:(lia)); lia. }
  assert (Habs: Zabs (Zabs n_nonalias + Zabs m_nonalias) = Zabs (n_nonalias - m_nonalias)) by lia.
  rewrite Habs.
  repeat cancel.
Qed.

Lemma proof_of_mpz_sub_return_wit_5_nonalias : mpz_sub_return_wit_5_nonalias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_sub_return_wit_5_nonalias_split_goal_spatial.
  - Goal_apply proof_of_mpz_sub_return_wit_5_nonalias_split_goal_1.
Qed.

Lemma proof_of_mpz_sub_return_wit_6_nonalias_split_goal_1 : mpz_sub_return_wit_6_nonalias_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_sub_return_wit_6_nonalias_split_goal_2 : mpz_sub_return_wit_6_nonalias_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n_nonalias < 0 /\ m_nonalias >= 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_negative_implies_opposite_signs_simple size size_2 ltac:(lia)); lia. }
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs (Zabs n_nonalias + Zabs m_nonalias)) (Zabs retval)).
  Intros.
  dump_pre_spatial.
  replace (n_nonalias - m_nonalias) with (-(Zabs n_nonalias + Zabs m_nonalias)) by lia.
  apply same_sign_opp_compact_abs; [exact PreH1 | assumption].
Qed.

Lemma proof_of_mpz_sub_return_wit_6_nonalias_split_goal_spatial : mpz_sub_return_wit_6_nonalias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n_nonalias < 0 /\ m_nonalias >= 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_negative_implies_opposite_signs_simple size size_2 ltac:(lia)); lia. }
  assert (Habs: Zabs (Zabs n_nonalias + Zabs m_nonalias) = Zabs (n_nonalias - m_nonalias)) by lia.
  rewrite Habs.
  rewrite Z.abs_opp.
  repeat cancel.
Qed.

Lemma proof_of_mpz_sub_return_wit_6_nonalias : mpz_sub_return_wit_6_nonalias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_sub_return_wit_6_nonalias_split_goal_spatial.
  - Goal_apply proof_of_mpz_sub_return_wit_6_nonalias_split_goal_1.
  - Goal_apply proof_of_mpz_sub_return_wit_6_nonalias_split_goal_2.
Qed.

Lemma proof_of_mpz_sub_return_wit_7_r_eq_a : mpz_sub_return_wit_7_r_eq_a.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst r_pre.
  assert (za_r_eq_a >= 0 /\ zb_r_eq_a < 0) as Hnm.
  { unfold same_sign in *.
    destruct (lxor_negative_implies_opposite_signs_simple old_size bsize ltac:(lia)); lia. }
  replace (Zabs za_r_eq_a + Zabs zb_r_eq_a) with (Zabs (za_r_eq_a - zb_r_eq_a)) in * by lia.
  replace (Zabs za_r_eq_a + Zabs zb_r_eq_a) with (za_r_eq_a - zb_r_eq_a) in * by lia.
  unfold store_Z at 1.
  Exists ptr; Exists rn_v; Exists cap.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption.
    unfold same_sign in *; lia.
Qed.

Lemma proof_of_mpz_sub_return_wit_8_r_eq_a : mpz_sub_return_wit_8_r_eq_a.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst r_pre.
  assert (za_r_eq_a < 0 /\ zb_r_eq_a >= 0) as Hnm.
  { unfold same_sign in *.
    destruct (lxor_negative_implies_opposite_signs_simple old_size bsize ltac:(lia)); lia. }
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs za_r_eq_a + Zabs zb_r_eq_a) (Zabs rn_v)).
  Intros.
  assert (same_sign (za_r_eq_a - zb_r_eq_a) (- rn_v)) as Hsg.
  { replace (za_r_eq_a - zb_r_eq_a) with (-(Zabs za_r_eq_a + Zabs zb_r_eq_a)) by lia.
    replace (Zabs za_r_eq_a + Zabs zb_r_eq_a) with (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) in H by lia.
    eapply same_sign_opp_compact_abs; eauto. }
  replace (Zabs za_r_eq_a + Zabs zb_r_eq_a) with (Zabs (za_r_eq_a - zb_r_eq_a)) in * by lia.
  unfold store_Z at 1.
  Exists ptr; Exists (- rn_v); Exists cap.
  replace (Zabs (- rn_v)) with (Zabs rn_v) by lia.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

