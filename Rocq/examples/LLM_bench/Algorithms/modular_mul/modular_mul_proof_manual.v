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
From SimpleC.EE.LLM_bench.Algorithms.modular_mul Require Import modular_mul_goal.
From SimpleC.EE.LLM_bench.Algorithms.modular_mul Require Import modular_mul_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib.
Local Open Scope sac.

Lemma proof_of_modular_mul_entail_wit_1_1_split_goal_1 : modular_mul_entail_wit_1_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ModularMulProgress.
  exists 0.
  ring.
Qed.

Lemma proof_of_modular_mul_entail_wit_1_1 : modular_mul_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_modular_mul_entail_wit_1_1_split_goal_1.
Qed.

Lemma proof_of_modular_mul_entail_wit_1_2_split_goal_1 : modular_mul_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ModularMulProgress.
  exists 0.
  ring.
Qed.

Lemma proof_of_modular_mul_entail_wit_1_2 : modular_mul_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_modular_mul_entail_wit_1_2_split_goal_1.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_1 : modular_mul_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg in PreH1 by lia.
  rewrite zdiv_equiv by lia.
  subst flag.
  eapply modular_mul_progress_odd_step__odd_transition; eauto; lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_2 : modular_mul_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_3 : modular_mul_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_4 : modular_mul_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_5 : modular_mul_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_6 : modular_mul_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_7 : modular_mul_entail_wit_2_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_8 : modular_mul_entail_wit_2_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_9 : modular_mul_entail_wit_2_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_10 : modular_mul_entail_wit_2_1_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_11 : modular_mul_entail_wit_2_1_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_12 : modular_mul_entail_wit_2_1_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  pose proof
    (Z.div_le_upper_bound b 2 b ltac:(lia) ltac:(nia)) as Hhalf_le.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1_split_goal_13 : modular_mul_entail_wit_2_1_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_1 : modular_mul_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_6.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_7.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_8.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_9.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_10.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_11.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_12.
  - Goal_apply proof_of_modular_mul_entail_wit_2_1_split_goal_13.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_1 : modular_mul_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg in PreH1 by lia.
  rewrite zdiv_equiv by lia.
  subst flag.
  eapply modular_mul_progress_odd_step__odd_transition; eauto; lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_2 : modular_mul_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_3 : modular_mul_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_4 : modular_mul_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_5 : modular_mul_entail_wit_2_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_6 : modular_mul_entail_wit_2_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_7 : modular_mul_entail_wit_2_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_8 : modular_mul_entail_wit_2_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_9 : modular_mul_entail_wit_2_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (res + a) modulus_pre ltac:(lia)) as Hres_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_10 : modular_mul_entail_wit_2_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_11 : modular_mul_entail_wit_2_2_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (Z.rem_bound_abs (a + a) modulus_pre ltac:(lia)) as Ha_rem.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_12 : modular_mul_entail_wit_2_2_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  pose proof
    (Z.div_le_upper_bound b 2 b ltac:(lia) ltac:(nia)) as Hhalf_le.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2_split_goal_13 : modular_mul_entail_wit_2_2_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_2 : modular_mul_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_4.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_5.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_6.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_7.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_8.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_9.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_10.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_11.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_12.
  - Goal_apply proof_of_modular_mul_entail_wit_2_2_split_goal_13.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_3_split_goal_1 : modular_mul_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbmod : Z.rem b 2 = 0).
  {
    pose proof
      (Z.rem_bound_pos b 2 ltac:(lia) ltac:(lia)) as Hbmod_bound.
    lia.
  }
  subst flag.
  eapply modular_mul_progress_even_step__even_transition; eauto; lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_3_split_goal_2 : modular_mul_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_3_split_goal_3 : modular_mul_entail_wit_2_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_3_split_goal_4 : modular_mul_entail_wit_2_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_3_split_goal_5 : modular_mul_entail_wit_2_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_3_split_goal_6 : modular_mul_entail_wit_2_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_3_split_goal_7 : modular_mul_entail_wit_2_3_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_3_split_goal_8 : modular_mul_entail_wit_2_3_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.quot_le_upper_bound; lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_3_split_goal_9 : modular_mul_entail_wit_2_3_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.quot_pos; lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_3 : modular_mul_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_mul_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_modular_mul_entail_wit_2_3_split_goal_2.
  - Goal_apply proof_of_modular_mul_entail_wit_2_3_split_goal_3.
  - Goal_apply proof_of_modular_mul_entail_wit_2_3_split_goal_4.
  - Goal_apply proof_of_modular_mul_entail_wit_2_3_split_goal_5.
  - Goal_apply proof_of_modular_mul_entail_wit_2_3_split_goal_6.
  - Goal_apply proof_of_modular_mul_entail_wit_2_3_split_goal_7.
  - Goal_apply proof_of_modular_mul_entail_wit_2_3_split_goal_8.
  - Goal_apply proof_of_modular_mul_entail_wit_2_3_split_goal_9.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_4_split_goal_1 : modular_mul_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbmod : Z.rem b 2 = 0).
  {
    pose proof
      (Z.rem_bound_pos b 2 ltac:(lia) ltac:(lia)) as Hbmod_bound.
    lia.
  }
  subst flag.
  eapply modular_mul_progress_even_step__even_transition; eauto; lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_4_split_goal_2 : modular_mul_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_4_split_goal_3 : modular_mul_entail_wit_2_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_4_split_goal_4 : modular_mul_entail_wit_2_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_4_split_goal_5 : modular_mul_entail_wit_2_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_4_split_goal_6 : modular_mul_entail_wit_2_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_4_split_goal_7 : modular_mul_entail_wit_2_4_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (z_rem_strict_bounds__even_transition (a + a) modulus_pre PreH7)
    as Hmod_bound.
  lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_4_split_goal_8 : modular_mul_entail_wit_2_4_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.quot_le_upper_bound; lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_4_split_goal_9 : modular_mul_entail_wit_2_4_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.quot_pos; lia.
Qed.

Lemma proof_of_modular_mul_entail_wit_2_4 : modular_mul_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_mul_entail_wit_2_4_split_goal_1.
  - Goal_apply proof_of_modular_mul_entail_wit_2_4_split_goal_2.
  - Goal_apply proof_of_modular_mul_entail_wit_2_4_split_goal_3.
  - Goal_apply proof_of_modular_mul_entail_wit_2_4_split_goal_4.
  - Goal_apply proof_of_modular_mul_entail_wit_2_4_split_goal_5.
  - Goal_apply proof_of_modular_mul_entail_wit_2_4_split_goal_6.
  - Goal_apply proof_of_modular_mul_entail_wit_2_4_split_goal_7.
  - Goal_apply proof_of_modular_mul_entail_wit_2_4_split_goal_8.
  - Goal_apply proof_of_modular_mul_entail_wit_2_4_split_goal_9.
Qed.

Lemma proof_of_modular_mul_return_wit_1_split_goal_1 : modular_mul_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (b = 0) by lia.
  subst b.
  subst flag.
  eapply modular_mul_progress_finish__final_result with
      (current_multiplicand := a) (remaining_multiplier := 0) (sign := -1).
  - reflexivity.
  - right. reflexivity.
  - lia.
  - exact PreH21.
Qed.

Lemma proof_of_modular_mul_return_wit_1 : modular_mul_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_modular_mul_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_modular_mul_return_wit_2_split_goal_1 : modular_mul_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (b = 0) by lia.
  subst b.
  subst flag.
  eapply modular_mul_progress_finish__final_result with
      (current_multiplicand := a) (remaining_multiplier := 0) (sign := 1).
  - reflexivity.
  - left. reflexivity.
  - lia.
  - exact PreH21.
Qed.

Lemma proof_of_modular_mul_return_wit_2 : modular_mul_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_modular_mul_return_wit_2_split_goal_1.
Qed.
