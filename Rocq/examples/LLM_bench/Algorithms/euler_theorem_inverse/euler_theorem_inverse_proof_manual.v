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
From SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse Require Import euler_theorem_inverse_goal.
From SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse Require Import euler_theorem_inverse_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.
Local Open Scope sac.

Lemma proof_of_euler_phi_safety_wit_8_split_goal_1 : euler_phi_safety_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH10 as (before & removed & Hremoved & Hbefore & Hfactor_before & Hfactor_result & Hprogress & Hcompletion).
  pose proof (euler_exact_positive_quotient_bounds__euler_phi_factor_completion result factor PreH6 PreH8 Hfactor_result) as [Hquotient [Hnonnegative Hbounded]].
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_euler_phi_safety_wit_8_split_goal_2 : euler_phi_safety_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH10 as (before & removed & Hremoved & Hbefore & Hfactor_before & Hfactor_result & Hprogress & Hcompletion).
  pose proof (euler_exact_positive_quotient_bounds__euler_phi_factor_completion result factor PreH6 PreH8 Hfactor_result) as [Hquotient [Hnonnegative Hbounded]].
  entailer_with ltac:(lia || int_auto).
Qed.

Lemma proof_of_euler_phi_safety_wit_8 : euler_phi_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_euler_phi_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_euler_phi_safety_wit_8_split_goal_2.
Qed. 

Lemma proof_of_euler_phi_entail_wit_1_split_goal_1 : euler_phi_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold EulerPhiProgress, EulerPhiResidual, NoPrimeDivisorBelow.
  split.
  - split.
    + apply Z.divide_refl.
    + intros original_phi remaining_phi Horiginal Hremaining.
      unfold EulerPhi in Horiginal, Hremaining.
      subst original_phi remaining_phi.
      ring.
  - intros p Hp Hbelow Hdivide.
    destruct Hp as [Hp _].
    lia.
Qed.

Lemma proof_of_euler_phi_entail_wit_1 : euler_phi_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_euler_phi_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_euler_phi_entail_wit_2_split_goal_1 : euler_phi_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hmod : value mod factor = 0).
  {
    apply
      (proj1
         (Coq.ZArith.Zquot.Zrem_Zmod_zero value factor ltac:(lia))).
    exact PreH1.
  }
  exact
    (euler_phi_removal_start__euler_phi_setup_removal
       value_pre factor value result PreH3 PreH5 PreH7 PreH9 Hmod PreH11).
Qed.

Lemma proof_of_euler_phi_entail_wit_2 : euler_phi_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_euler_phi_entail_wit_2_split_goal_1.
Qed. 

Lemma proof_of_euler_phi_entail_wit_3_split_goal_1 : euler_phi_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Coq.ZArith.Zquot.Zquot_Zdiv_pos by lia.
  assert (Hmod : value mod factor = 0).
  {
    apply
      (proj1
         (Coq.ZArith.Zquot.Zrem_Zmod_zero value factor ltac:(lia))).
    exact PreH1.
  }
  unfold EulerPhiRemovalProgress in *.
  destruct PreH10 as
    (before & removed & Hremoved & Hbefore & Hfactor_before &
     Hfactor_result & Hprogress & Hcompletion).
  assert (Hexact : value = (value / factor) * factor).
  {
    pose proof (Z.div_mod value factor ltac:(lia)) as Hdivision.
    rewrite Hmod, Z.add_0_r in Hdivision.
    nia.
  }
  exists before, (removed + 1).
  split; [lia |].
  split.
  - rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    rewrite Hbefore.
    rewrite Hexact at 1.
    ring.
  - split; [exact Hfactor_before |].
    split; [exact Hfactor_result |].
    split; [exact Hprogress |].
    eapply EulerPhiFactorCompletion_divide; eauto; lia.
Qed.

Lemma proof_of_euler_phi_entail_wit_3_split_goal_2 : euler_phi_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Coq.ZArith.Zquot.Zquot_Zdiv_pos by lia.
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma proof_of_euler_phi_entail_wit_3_split_goal_3 : euler_phi_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Coq.ZArith.Zquot.Zquot_Zdiv_pos by lia.
  assert (Hmod : value mod factor = 0).
  {
    apply
      (proj1
         (Coq.ZArith.Zquot.Zrem_Zmod_zero value factor ltac:(lia))).
    exact PreH1.
  }
  pose proof (Z.div_mod value factor ltac:(lia)) as Hdivision.
  rewrite Hmod, Z.add_0_r in Hdivision.
  nia.
Qed.

Lemma proof_of_euler_phi_entail_wit_3 : euler_phi_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_euler_phi_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_euler_phi_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_euler_phi_entail_wit_3_split_goal_3.
Qed. 

Lemma proof_of_euler_phi_entail_wit_4_1_split_goal_1 : euler_phi_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). eapply euler_completed_progress__euler_phi_factor_completion; eauto.
Qed.

Lemma proof_of_euler_phi_entail_wit_4_1_split_goal_2 : euler_phi_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto). eapply euler_active_frontier_bound__euler_phi_factor_completion; eauto.
Qed.

Lemma proof_of_euler_phi_entail_wit_4_1_split_goal_3 : euler_phi_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH10 as
      (before & removed & Hremoved & Hbefore & Hfactor_before &
       Hfactor_result & Hprogress & Hcompletion).
  pose proof
    (euler_exact_positive_quotient_bounds__euler_phi_factor_completion
       result factor PreH6 PreH8 Hfactor_result)
    as [Hquotient [Hnonnegative Hbounded]].
  lia.
Qed.

Lemma proof_of_euler_phi_entail_wit_4_1_split_goal_4 : euler_phi_entail_wit_4_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH10 as (before & removed & Hremoved & Hbefore & Hfactor_before & Hfactor_result & Hprogress & Hcompletion).
  pose proof (euler_exact_positive_quotient_bounds__euler_phi_factor_completion result factor PreH6 PreH8 Hfactor_result) as [Hquotient [Hnonnegative Hbounded]].
  nia.
Qed.

Lemma proof_of_euler_phi_entail_wit_4_1 : euler_phi_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_euler_phi_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_euler_phi_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_euler_phi_entail_wit_4_1_split_goal_3.
  - Goal_apply proof_of_euler_phi_entail_wit_4_1_split_goal_4.
Qed. 

Lemma proof_of_euler_phi_entail_wit_4_2_split_goal_1 : euler_phi_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact
    (euler_progress_advance_nondivisor__euler_phi_factor_completion
       value_pre factor value result PreH9 PreH1 PreH11).
Qed.

Lemma proof_of_euler_phi_entail_wit_4_2 : euler_phi_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_euler_phi_entail_wit_4_2_split_goal_1.
Qed. 

Lemma proof_of_euler_phi_entail_wit_5 : euler_phi_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH10 as Hprogress.
  destruct PreH10 as [[[q Hresult] Hresidual] Hno_small].
  assert (Hrem : Z.rem result value = 0).
  {
    apply (proj2 (Z.rem_divide result value ltac:(lia))).
    exists q.
    exact Hresult.
  }
  assert (Hquot : Z.quot result value = q).
  {
    rewrite Hresult, Z.quot_mul by lia.
    reflexivity.
  }
  destruct (Z.eq_dec value 1) as [Hunit | Hnonunit].
  - Right.
    Exists factor.
    split_pure_spatial.
    + cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: lia.
  - Left.
    Exists factor.
    split_pure_spatial.
    + cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: rewrite Hquot.
      all: nia.
Qed. 

Lemma proof_of_euler_phi_return_wit_1_split_goal_1 : euler_phi_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply euler_progress_terminal_prime__euler_phi_final_results; eauto; lia.
Qed.

Lemma proof_of_euler_phi_return_wit_1 : euler_phi_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_euler_phi_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_euler_phi_return_wit_2_split_goal_1 : euler_phi_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply euler_progress_terminal_one__euler_phi_final_results; eauto.
Qed.

Lemma proof_of_euler_phi_return_wit_2 : euler_phi_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_euler_phi_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_euler_phi_return_wit_3_split_goal_1 : euler_phi_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply euler_progress_terminal_one__euler_phi_final_results; eauto.
Qed.

Lemma proof_of_euler_phi_return_wit_3 : euler_phi_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_euler_phi_return_wit_3_split_goal_1.
Qed. 

Lemma proof_of_modular_power_entail_wit_1_split_goal_1 : modular_power_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold EulerModularPowerProgress.
  rewrite Z.mul_1_l.
  reflexivity.
Qed.

Lemma proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_modular_power_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_1 : modular_power_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg in PreH1 by lia.
  rewrite !Z.rem_mod_nonneg by lia.
  rewrite zdiv_equiv by lia.
  eapply euler_modular_progress_odd_step__modular_power_loop; eauto; lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_2 : modular_power_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (result * base) modulus_pre ltac:(lia)) as Hresult_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_3 : modular_power_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (result * base) modulus_pre ltac:(lia)) as Hresult_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_4 : modular_power_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_5 : modular_power_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (base * base) modulus_pre ltac:(lia)) as Hbase_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_6 : modular_power_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (base * base) modulus_pre ltac:(lia)) as Hbase_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1 : modular_power_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_6.
Qed. 

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_1 : modular_power_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg in PreH1 by lia.
  rewrite !Z.rem_mod_nonneg by lia.
  rewrite zdiv_equiv by lia.
  eapply euler_modular_progress_even_step__modular_power_loop; eauto; lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_2 : modular_power_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_3 : modular_power_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (base * base) modulus_pre ltac:(lia)) as Hbase_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_4 : modular_power_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (base * base) modulus_pre ltac:(lia)) as Hbase_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2 : modular_power_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_4.
Qed. 

Lemma proof_of_modular_power_return_wit_1_split_goal_1 : modular_power_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (exponent = 0) by lia.
  subst exponent.
  eapply euler_modular_progress_zero_finish__modular_power_final; eauto.
Qed.

Lemma proof_of_modular_power_return_wit_1 : modular_power_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_modular_power_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_euler_theorem_inverse_return_wit_1_split_goal_1 : euler_theorem_inverse_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (proj2 (euler_totient_inverse_theorem__inverse_final_result value_pre modulus_pre retval_2 retval PreH7 PreH8 PreH9 PreH11 PreH6 PreH3)).
Qed.

Lemma proof_of_euler_theorem_inverse_return_wit_1 : euler_theorem_inverse_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_euler_theorem_inverse_return_wit_1_split_goal_1.
Qed. 

