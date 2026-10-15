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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P064_223C_partial_sums_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P064_223C_partial_sums_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P064_223C_partial_sums_lib.
Local Open Scope sac.

Lemma proof_of_power_entail_wit_1_split_goal_1 : power_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  apply power_loop_state_init__power_loop.
  exact PreH3.
Qed.

Lemma proof_of_power_entail_wit_1_split_goal_2 : power_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  apply modulo_strict_upper_bound__power_loop.
Qed.

Lemma proof_of_power_entail_wit_1_split_goal_3 : power_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  apply modulo_nonnegative__power_loop.
Qed.

Lemma proof_of_power_entail_wit_1 : power_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_power_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_power_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_power_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_1 : power_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Z.rem_mod_nonneg by nia.
  eapply power_loop_state_odd_step__power_loop.
  - exact PreH9.
  - exact PreH13.
  - exact PreH11.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_2 : power_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply Z.le_trans.
  - apply shiftr_one_le__power_loop. exact PreH9.
  - exact PreH10.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_3 : power_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply shiftr_one_nonnegative__power_loop.
  exact PreH9.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_4 : power_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  apply modulo_strict_upper_bound__power_loop.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_5 : power_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  apply modulo_nonnegative__power_loop.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_6 : power_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  apply modulo_strict_upper_bound__power_loop.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_7 : power_entail_wit_2_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  apply modulo_nonnegative__power_loop.
Qed.

Lemma proof_of_power_entail_wit_2_1 : power_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_6.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_7.
Qed.

Lemma proof_of_power_entail_wit_2_2_split_goal_1 : power_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Z.rem_mod_nonneg by nia.
  eapply power_loop_state_even_step__power_loop.
  - exact PreH9.
  - exact PreH13.
  - exact PreH11.
Qed.

Lemma proof_of_power_entail_wit_2_2_split_goal_2 : power_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply Z.le_trans.
  - apply shiftr_one_le__power_loop. exact PreH9.
  - exact PreH10.
Qed.

Lemma proof_of_power_entail_wit_2_2_split_goal_3 : power_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply shiftr_one_nonnegative__power_loop.
  exact PreH9.
Qed.

Lemma proof_of_power_entail_wit_2_2_split_goal_4 : power_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  apply modulo_strict_upper_bound__power_loop.
Qed.

Lemma proof_of_power_entail_wit_2_2_split_goal_5 : power_entail_wit_2_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.rem_mod_nonneg by nia.
  apply modulo_nonnegative__power_loop.
Qed.

Lemma proof_of_power_entail_wit_2_2 : power_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_power_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_power_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_power_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_power_entail_wit_2_2_split_goal_4.
  - Goal_apply proof_of_power_entail_wit_2_2_split_goal_5.
Qed.

Lemma proof_of_power_return_wit_1_split_goal_1 : power_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply power_loop_state_finish__power_loop.
  - lia.
  - subst e. exact PreH11.
Qed.

Lemma proof_of_power_return_wit_1 : power_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_power_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((d - 1) - 0) with (d - 1) by lia.
  specialize (PreH13 (d - 1) ltac:(lia)).
  destruct PreH13 as [Hcoef_nonneg Hcoef_lt].
  pose proof
    (Z.rem_bound_pos_pos (Znth (d - 1) coefficients 0)
       1000000007 ltac:(lia) ltac:(lia)) as Hcoef_mod.
  pose proof
    (Z.rem_bound_pos_pos ((k_pre - 1) + d)
       1000000007 ltac:(lia) ltac:(lia)) as Hfactor_mod.
  pose proof
    (Z.rem_bound_pos_pos
       ((Znth (d - 1) coefficients 0 % 1000000007) *
        (((k_pre - 1) + d) % 1000000007))
       1000000007 ltac:(nia) ltac:(lia)) as Hproduct_mod.
  pose proof
    (two_mod_factors_fit_int64__overflow_bounds
       ((((Znth (d - 1) coefficients 0 % 1000000007) *
          (((k_pre - 1) + d) % 1000000007)) % 1000000007))
       retval Hproduct_mod (conj PreH1 PreH2)) as Hfit.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((d - 1) - 0) with (d - 1) by lia.
  specialize (PreH13 (d - 1) ltac:(lia)).
  destruct PreH13 as [Hcoef_nonneg Hcoef_lt].
  pose proof
    (Z.rem_bound_pos_pos (Znth (d - 1) coefficients 0)
       1000000007 ltac:(lia) ltac:(lia)) as Hcoef_mod.
  pose proof
    (Z.rem_bound_pos_pos ((k_pre - 1) + d)
       1000000007 ltac:(lia) ltac:(lia)) as Hfactor_mod.
  pose proof
    (Z.rem_bound_pos_pos
       ((Znth (d - 1) coefficients 0 % 1000000007) *
        (((k_pre - 1) + d) % 1000000007))
       1000000007 ltac:(nia) ltac:(lia)) as Hproduct_mod.
  pose proof
    (two_mod_factors_fit_int64__overflow_bounds
       ((((Znth (d - 1) coefficients 0 % 1000000007) *
          (((k_pre - 1) + d) % 1000000007)) % 1000000007))
       retval Hproduct_mod (conj PreH1 PreH2)) as Hfit.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_1 : solver_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((d - 1) - 0) with (d - 1) by lia.
  specialize (PreH10 (d - 1) ltac:(lia)).
  destruct PreH10 as [Hcoef_nonneg Hcoef_lt].
  pose proof
    (Z.rem_bound_pos_pos (Znth (d - 1) coefficients 0)
       1000000007 ltac:(lia) ltac:(lia)) as Hcoef_mod.
  pose proof
    (Z.rem_bound_pos_pos ((k_pre - 1) + d)
       1000000007 ltac:(lia) ltac:(lia)) as Hfactor_mod.
  pose proof
    (two_mod_factors_fit_int64__overflow_bounds
       (Znth (d - 1) coefficients 0 % 1000000007)
       (((k_pre - 1) + d) % 1000000007)
       Hcoef_mod Hfactor_mod) as Hfit.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_2 : solver_safety_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((d - 1) - 0) with (d - 1) by lia.
  specialize (PreH10 (d - 1) ltac:(lia)).
  destruct PreH10 as [Hcoef_nonneg Hcoef_lt].
  pose proof
    (Z.rem_bound_pos_pos (Znth (d - 1) coefficients 0)
       1000000007 ltac:(lia) ltac:(lia)) as Hcoef_mod.
  pose proof
    (Z.rem_bound_pos_pos ((k_pre - 1) + d)
       1000000007 ltac:(lia) ltac:(lia)) as Hfactor_mod.
  pose proof
    (two_mod_factors_fit_int64__overflow_bounds
       (Znth (d - 1) coefficients 0 % 1000000007)
       (((k_pre - 1) + d) % 1000000007)
       Hcoef_mod Hfactor_mod) as Hfit.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_33_split_goal_1 : solver_safety_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH9 (i - j) ltac:(lia)).
  specialize (PreH7 j ltac:(lia)).
  destruct PreH9 as [Hcoef_nonneg Hcoef_lt].
  destruct PreH7 as [Hvalue_nonneg Hvalue_upper].
  pose proof
    (Z.rem_bound_pos_pos (Znth j values 0)
       1000000007 ltac:(lia) ltac:(lia)) as Hvalue_mod.
  pose proof
    (mod_product_plus_residue_fit_int64__overflow_bounds
       s (Znth (i - j) coefficients 0)
       (Znth j values 0 % 1000000007)
       (conj PreH17 PreH18) (conj Hcoef_nonneg Hcoef_lt) Hvalue_mod) as Hfit.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_33_split_goal_2 : solver_safety_wit_33_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH9 (i - j) ltac:(lia)).
  specialize (PreH7 j ltac:(lia)).
  destruct PreH9 as [Hcoef_nonneg Hcoef_lt].
  destruct PreH7 as [Hvalue_nonneg Hvalue_upper].
  pose proof
    (Z.rem_bound_pos_pos (Znth j values 0)
       1000000007 ltac:(lia) ltac:(lia)) as Hvalue_mod.
  pose proof
    (mod_product_plus_residue_fit_int64__overflow_bounds
       s (Znth (i - j) coefficients 0)
       (Znth j values 0 % 1000000007)
       (conj PreH17 PreH18) (conj Hcoef_nonneg Hcoef_lt) Hvalue_mod) as Hfit.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_33_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_33_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_34_split_goal_1 : solver_safety_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH9 (i - j) ltac:(lia)).
  specialize (PreH7 j ltac:(lia)).
  destruct PreH9 as [Hcoef_nonneg Hcoef_lt].
  destruct PreH7 as [Hvalue_nonneg Hvalue_upper].
  pose proof
    (Z.rem_bound_pos_pos (Znth j values 0)
       1000000007 ltac:(lia) ltac:(lia)) as Hvalue_mod.
  pose proof
    (two_mod_factors_fit_int64__overflow_bounds
       (Znth (i - j) coefficients 0)
       (Znth j values 0 % 1000000007)
       (conj Hcoef_nonneg Hcoef_lt) Hvalue_mod) as Hfit.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_34_split_goal_2 : solver_safety_wit_34_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH9 (i - j) ltac:(lia)).
  specialize (PreH7 j ltac:(lia)).
  destruct PreH9 as [Hcoef_nonneg Hcoef_lt].
  destruct PreH7 as [Hvalue_nonneg Hvalue_upper].
  pose proof
    (Z.rem_bound_pos_pos (Znth j values 0)
       1000000007 ltac:(lia) ltac:(lia)) as Hvalue_mod.
  pose proof
    (two_mod_factors_fit_int64__overflow_bounds
       (Znth (i - j) coefficients 0)
       (Znth j values 0 % 1000000007)
       (conj Hcoef_nonneg Hcoef_lt) Hvalue_mod) as Hfit.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_34_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_34_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold IdentityPrefix.
  intros i Hi.
  rewrite Zlength_nil in Hi.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply identity_prefix_snoc_mod__identity_prefix.
  - exact PreH9.
  - exact PreH10.
  - specialize (PreH6 i).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, PreH9, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (1 :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic (Int64Array.seg_single coef_pre 0 1).
    replace (0 + 1) with 1 by lia.
    cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial.
      intros q Hq.
      assert (q = 0) by lia.
      subst q.
      change (0 <= 1 < 1000000007).
      lia.
    + dump_pre_spatial.
      apply coefficient_prefix_singleton__coefficient_construction.
      lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH11 q_2 H).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH7 q H).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (d - 1 - 0) with (d - 1) by lia.
  apply coefficient_prefix_snoc__coefficient_construction; assumption.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec q_2 d) as [Hlt | Hge].
  - rewrite app_Znth1 by (rewrite PreH12; lia).
    apply PreH13. lia.
  - assert (q_2 = d) by lia. subst q_2.
    rewrite app_Znth2 by (rewrite PreH12; lia).
    rewrite PreH12.
    replace (d - d) with 0 by lia.
    rewrite Znth0_cons.
    replace (d - 1 - 0) with (d - 1) by lia.
    pose proof (PreH13 (d - 1) ltac:(lia)) as Hold.
    pose proof
      (rem_range_nonneg__coefficient_construction
         (Znth (d - 1) coefficients_2 0) (proj1 Hold)) as Hleft.
    assert (Hright_arg : 0 <= k_pre - 1 + d) by lia.
    pose proof
      (rem_range_nonneg__coefficient_construction
         (k_pre - 1 + d) Hright_arg) as Hright.
    pose proof
      (rem_range_nonneg__coefficient_construction
         (Z.rem (Znth (d - 1) coefficients_2 0) 1000000007 *
          Z.rem (k_pre - 1 + d) 1000000007)
         ltac:(clear - Hleft Hright; nia)) as Hproduct.
    apply rem_range_nonneg__coefficient_construction.
    clear - Hproduct PreH1.
    nia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH12.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH9 q H).
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hd : d = n_pre) by lia.
  subst d.
  rewrite Hd in *.
  Exists (@nil Z) coefficients_2.
  rewrite Int64Array.undef_seg_empty.
  rewrite Int64Array.seg_empty.
  sep_apply
    (Int64Array.seg_to_full coef_pre 0 n_pre coefficients_2).
  sep_apply
    (Int64Array.undef_full_to_undef_seg out_pre n_pre).
  replace (coef_pre + 0 * sizeof(INT64)) with coef_pre by lia.
  replace (n_pre - 0) with n_pre by lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
    + reflexivity.
    + unfold ConvolutionPrefix.
      intros q Hq.
      rewrite Zlength_nil in Hq.
      lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH9.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH7.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH7 j ltac:(lia)) as Hvalue.
  pose proof (PreH9 (i - j) ltac:(lia)) as Hcoefficient.
  assert (Hvalue_rem : 0 <= Znth j values 0 % 1000000007).
  { apply Z.rem_nonneg; lia. }
  repeat rewrite Z.rem_mod_nonneg by nia.
  apply convolution_accumulator_step__convolution_loop; assumption.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (Z.rem_bound_abs
       (s + Znth (i - j) coefficients_2 0 *
              (Znth j values 0 % 1000000007))
       1000000007 ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH7 j ltac:(lia)) as Hvalue.
  pose proof (PreH9 (i - j) ltac:(lia)) as Hcoefficient.
  assert (Hvalue_rem : 0 <= Znth j values 0 % 1000000007).
  { apply Z.rem_nonneg; lia. }
  apply Z.rem_nonneg; nia.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply convolution_prefix_snoc__convolution_loop; eassumption.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_3 : solver_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH9.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_4 : solver_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH7.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_4.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists written.
  sep_apply_l_atomic (Int64Array.seg_to_full out_pre 0 i written).
  split_pure_spatial.
  - replace i with n_pre by lia.
    replace (out_pre + 0 * sizeof (INT64)) with out_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    rewrite Int64Array.undef_seg_empty.
    cancel.
    cancel (Int64Array.undef_full coef_pre n_pre).
    cancel emp.
  - split_pures.
    + dump_pre_spatial.
      replace k_pre with 0 by lia.
      apply identity_prefix_spec_zero__zero_final_result; lia || assumption.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre) by lia. subst i.
  assert (Hspec : Spec k_pre values written).
  {
    unfold Spec.
    eapply coefficient_convolution_iterate_prefix__positive_final_result.
    - exact PreH2.
    - rewrite <- PreH6. exact PreH5.
    - rewrite PreH8. exact PreH6.
    - rewrite <- PreH6. assumption.
    - exact PreH10.
    - exact PreH14.
  }
  Exists written.
  split_pure_spatial.
  - rewrite Hi.
    rewrite Int64Array.undef_seg_empty.
    sep_apply_l_atomic (Int64Array.seg_to_full out_pre 0 n_pre written).
    replace (out_pre + 0 * sizeof(INT64)) with out_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    sep_apply_l_atomic
      (Int64Array.full_to_full_shape coef_pre n_pre coefficients).
    cancel.
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. lia.
Qed.
