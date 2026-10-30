From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P037_1875C_jellyfish_and_green_apple_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P037_1875C_jellyfish_and_green_apple_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P037_1875C_jellyfish_and_green_apple_lib.
Local Open Scope sac.

Lemma proof_of_gcdll_entail_wit_2_split_goal_1 : gcdll_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GcdValue in *.
  rewrite (Z.gcd_comm b (a % ( b ))).
  rewrite (Z.gcd_rem a b PreH6).
  rewrite (Z.gcd_comm b a).
  exact PreH5.
Qed.

Lemma proof_of_gcdll_entail_wit_2_split_goal_2 : gcdll_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (0 < b) as Hb by lia.
  assert (0 <= a % ( b ) < b) as Hmod by
      (apply Z.rem_bound_pos; lia).
  destruct Hmod as [Hmod_nonneg Hmod_lt].
  lia.
Qed.

Lemma proof_of_gcdll_entail_wit_2_split_goal_3 : gcdll_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (0 < b) as Hb by lia.
  assert (0 <= a % ( b ) < b) as Hmod by
      (apply Z.rem_bound_pos; lia).
  destruct Hmod as [Hmod_nonneg Hmod_lt].
  exact Hmod_nonneg.
Qed.

Lemma proof_of_gcdll_entail_wit_2 : gcdll_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_gcdll_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_gcdll_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_gcdll_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_gcdll_return_wit_1_split_goal_1 : gcdll_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GcdValue in *.
  subst b.
  rewrite Z.gcd_0_r in PreH5.
  rewrite Z.abs_eq in PreH5 by lia.
  exact PreH5.
Qed.

Lemma proof_of_gcdll_return_wit_1 : gcdll_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_gcdll_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_1_split_goal_1 : solver_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_1_split_goal_2 : solver_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    unfold GcdValue in *;
    pose proof (positive_gcd_quotient_bounds__solver_setup n_pre m_pre ltac:(lia) ltac:(lia));
    lia).
Qed.

Lemma proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_2_split_goal_1 : solver_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold GcdValue in *.
  subst retval.
  pose proof (positive_gcd_quotient_bounds__solver_setup n_pre m_pre ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_2_split_goal_2 : solver_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold GcdValue in *.
  subst retval.
  pose proof (positive_gcd_quotient_bounds__solver_setup n_pre m_pre ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold DyadicRemainderPrefix.
  exists 0.
  unfold DyadicResidue, Zmap_range.
  simpl.
  repeat split; try lia.
  rewrite rem_mod_pos__solver_setup by lia.
  replace
    (match n_pre mod m_pre with
     | 0 => 0
     | Z.pos p => Z.pos p
     | Z.neg p => Z.neg p
     end)
    with (n_pre mod m_pre) by (destruct (n_pre mod m_pre); reflexivity).
  symmetry.
  apply Z.mod_mod.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite rem_mod_pos__solver_setup by lia.
  pose proof (Z.mod_pos_bound n_pre m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite rem_mod_pos__solver_setup by lia.
  pose proof (Z.mod_pos_bound n_pre m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GcdValue in *.
  subst retval.
  pose proof (positive_gcd_quotient_bounds__solver_setup n_pre m_pre ltac:(lia) ltac:(lia)) as Hbounds.
  unfold PowerOfTwo.
  eapply land_pred_zero_power_of_two__solver_setup.
  - lia.
  - exact PreH6.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Z.rem_mod_nonneg in PreH11 |- * by lia.
  rewrite (Z.rem_mod_nonneg (2 * n) m_pre) by lia.
  eapply dyadic_prefix_step__dyadic_transition.
  - lia.
  - exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst d.
  rewrite Z.rem_mod_nonneg in PreH11 by lia.
  eapply dyadic_prefix_total_bound__dyadic_transition.
  - exact PreH1.
  - exact PreH3.
  - exact PreH4.
  - exact PreH6.
  - exact PreH11.
  - exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound (2 * n) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_4 : solver_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound (2 * n) m_pre ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_4.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n.
  unfold Spec.
  left.
  assert (Hremmod : Z.rem n_pre m_pre = n_pre mod m_pre).
  { rewrite Z.rem_mod_nonneg by lia. reflexivity. }
  rewrite Hremmod in PreH11.
  apply complete_dyadic_prefix_minimum__dyadic_final; try lia.
  exact PreH11.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval.
  unfold Spec.
  right.
  split; [reflexivity |].
  apply nondyadic_no_achievable_division__dyadic_final; try lia.
  apply land_pred_nonzero_not_power_of_two__dyadic_final.
  - apply reduced_denominator_positive__dyadic_final; lia.
  - assert (Hg : GcdValue n_pre m_pre > 0).
    { pose proof (gcd_value_positive__dyadic_final n_pre m_pre
        ltac:(lia) ltac:(lia)). lia. }
    rewrite zdiv_equiv in PreH6 by lia.
    exact PreH6.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.
