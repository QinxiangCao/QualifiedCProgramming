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
From SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem Require Import extended_chinese_remainder_theorem_goal.
From SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem Require Import extended_chinese_remainder_theorem_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib.
Require Import SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_lib.
Local Open Scope sac.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_1 : extended_chinese_remainder_theorem_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre i PreH1 ltac:(lia)) as Hbounds.
  destruct Hbounds as [[Hmod_pos Hmod_max] [Hres_nonneg Hres_lt]].
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_2 : extended_chinese_remainder_theorem_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre i PreH1 ltac:(lia)) as Hbounds.
  destruct Hbounds as [[Hmod_pos Hmod_max] [Hres_nonneg Hres_lt]].
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_7 : extended_chinese_remainder_theorem_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_1 : extended_chinese_remainder_theorem_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_2 : extended_chinese_remainder_theorem_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_10 : extended_chinese_remainder_theorem_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_1 : extended_chinese_remainder_theorem_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_2 : extended_chinese_remainder_theorem_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_safety_wit_11 : extended_chinese_remainder_theorem_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_1_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ExtendedCRTInputs in PreH1.
  tauto.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_1 : extended_chinese_remainder_theorem_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (crt_prefix_meaning_one__prefix_boundaries
    residue_values modulus_values n_pre PreH2 PreH1).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre 0 PreH2 ltac:(lia))
    as [[Hmodulus_pos Hmodulus_max] [Hresidue_nonneg Hresidue_lt]].
  exact Hmodulus_max.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre 0 PreH2 ltac:(lia))
    as [[Hmodulus_pos Hmodulus_max] [Hresidue_nonneg Hresidue_lt]].
  exact Hmodulus_pos.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre 0 PreH2 ltac:(lia))
    as [[Hmodulus_pos Hmodulus_max] [Hresidue_nonneg Hresidue_lt]].
  exact Hresidue_lt.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_5 : extended_chinese_remainder_theorem_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre 0 PreH2 ltac:(lia))
    as [[Hmodulus_pos Hmodulus_max] [Hresidue_nonneg Hresidue_lt]].
  exact Hresidue_nonneg.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_2 : extended_chinese_remainder_theorem_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_2_split_goal_5.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (extended_crt_index_bounds__machine_bounds
      residue_values modulus_values n_pre i PreH7 ltac:(lia))
    as Hbounds.
  destruct Hbounds as [[Hmodulus_pos Hmodulus_max]
                        [Hresidue_nonneg Hresidue_lt]].
  pose proof
    (signed_difference_division_bounds__machine_bounds
      (Znth i residue_values 0) answer retval
      ltac:(lia) ltac:(lia) PreH1) as Hdivision.
  exact (proj2 Hdivision).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (extended_crt_index_bounds__machine_bounds
      residue_values modulus_values n_pre i PreH7 ltac:(lia))
    as Hbounds.
  destruct Hbounds as [[Hmodulus_pos Hmodulus_max]
                        [Hresidue_nonneg Hresidue_lt]].
  pose proof
    (signed_difference_division_bounds__machine_bounds
      (Znth i residue_values 0) answer retval
      ltac:(lia) ltac:(lia) PreH1) as Hdivision.
  exact (proj1 Hdivision).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (extended_crt_index_bounds__machine_bounds
      residue_values modulus_values n_pre i PreH7 ltac:(lia))
    as Hbounds.
  destruct Hbounds as [[Hmodulus_pos Hmodulus_max] Hresidue_bounds].
  pose proof
    (bezout_coefficient_strict__gcd_branch_setup
      lcm (Znth i modulus_values 0) retval x_callee_v y_callee_v
      Hmodulus_pos PreH2 PreH1 PreH5 PreH3 PreH4) as Hstrict.
  exact (proj2 Hstrict).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (extended_crt_index_bounds__machine_bounds
      residue_values modulus_values n_pre i PreH7 ltac:(lia))
    as Hbounds.
  destruct Hbounds as [[Hmodulus_pos Hmodulus_max] Hresidue_bounds].
  pose proof
    (bezout_coefficient_strict__gcd_branch_setup
      lcm (Znth i modulus_values 0) retval x_callee_v y_callee_v
      Hmodulus_pos PreH2 PreH1 PreH5 PreH3 PreH4) as Hstrict.
  exact (proj1 Hstrict).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ExtendedCRTIntSafe in PreH9.
  destruct PreH9 as [Hprefix_safe Hstep_safe].
  specialize (Hstep_safe i ltac:(lia)).
  unfold CRTPrefixMeaning in PreH16.
  destruct PreH16 as [Hlcm Hcongruences].
  rewrite <- Hlcm in Hstep_safe.
  rewrite <- PreH2 in Hstep_safe.
  nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (extended_crt_index_bounds__machine_bounds
      residue_values modulus_values n_pre i PreH7 ltac:(lia))
    as Hbounds.
  destruct Hbounds as [Hmodulus_bounds Hresidue_bounds].
  pose proof
    (positive_gcd_quotient_bounds__machine_bounds
      lcm (Znth i modulus_values 0) retval
      Hmodulus_bounds PreH2 PreH1) as Hquotient.
  lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8 : extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_1 : extended_chinese_remainder_theorem_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_2.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_3.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_4.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_5.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_6.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_7.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_1_split_goal_8.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (extended_crt_index_bounds__machine_bounds
      residue_values modulus_values n_pre i PreH8 ltac:(lia))
    as Hbounds.
  destruct Hbounds as [[Hmodulus_pos Hmodulus_max]
                        [Hresidue_nonneg Hresidue_lt]].
  pose proof
    (signed_difference_division_bounds__machine_bounds
      (Znth i residue_values 0) answer retval
      ltac:(lia) ltac:(lia) PreH1) as Hdivision.
  exact (proj2 Hdivision).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (extended_crt_index_bounds__machine_bounds
      residue_values modulus_values n_pre i PreH8 ltac:(lia))
    as Hbounds.
  destruct Hbounds as [[Hmodulus_pos Hmodulus_max]
                        [Hresidue_nonneg Hresidue_lt]].
  pose proof
    (signed_difference_division_bounds__machine_bounds
      (Znth i residue_values 0) answer retval
      ltac:(lia) ltac:(lia) PreH1) as Hdivision.
  exact (proj1 Hdivision).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (extended_crt_index_bounds__machine_bounds
      residue_values modulus_values n_pre i PreH8 ltac:(lia))
    as Hbounds.
  destruct Hbounds as [Hmodulus_bounds Hresidue_bounds].
  pose proof
    (positive_gcd_quotient_bounds__machine_bounds
      lcm (Znth i modulus_values 0) retval
      Hmodulus_bounds PreH2 PreH1) as Hquotient.
  exact (proj1 Hquotient).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (extended_crt_index_bounds__machine_bounds
      residue_values modulus_values n_pre i PreH8 ltac:(lia))
    as Hbounds.
  destruct Hbounds as [Hmodulus_bounds Hresidue_bounds].
  pose proof
    (positive_gcd_quotient_bounds__machine_bounds
      lcm (Znth i modulus_values 0) retval
      Hmodulus_bounds PreH2 PreH1) as Hquotient.
  lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ExtendedCRTIntSafe in PreH10.
  destruct PreH10 as [Hprefix_safe Hstep_safe].
  specialize (Hstep_safe i ltac:(lia)).
  unfold CRTPrefixMeaning in PreH17.
  destruct PreH17 as [Hlcm Hcongruences].
  rewrite <- Hlcm in Hstep_safe.
  rewrite <- PreH2 in Hstep_safe.
  nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (extended_crt_index_bounds__machine_bounds
      residue_values modulus_values n_pre i PreH8 ltac:(lia))
    as Hbounds.
  destruct Hbounds as [Hmodulus_bounds Hresidue_bounds].
  pose proof
    (positive_gcd_quotient_bounds__machine_bounds
      lcm (Znth i modulus_values 0) retval
      Hmodulus_bounds PreH2 PreH1) as Hquotient.
  exact (proj1 Hquotient).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8 : extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_3_2 : extended_chinese_remainder_theorem_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_1.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_2.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_3.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_4.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_5.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_6.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_7.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_3_2_split_goal_8.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (crt_merge_difference_divisible__merge_transition
      residue_values modulus_values n_pre i answer lcm
      PreH4 PreH13 (conj PreH6 PreH8)) as Hdifference.
  rewrite <- PreH14 in Hdifference.
  assert (Hmodulus_divides :
      (gcd | Znth i modulus_values 0)).
  { rewrite PreH14. apply Z.gcd_divide_r. }
  assert (Hdifference_quot_div :
      (Znth i residue_values 0 - answer) ÷ gcd =
      (Znth i residue_values 0 - answer) / gcd).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  assert (Hmodulus_quot_div :
      Znth i modulus_values 0 ÷ gcd =
      Znth i modulus_values 0 / gcd).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  unfold ModularMul in PreH2.
  destruct PreH2 as [[Hretval_lower Hretval_upper] [q Hmul]].
  rewrite Hdifference_quot_div in Hmul.
  rewrite Hmodulus_quot_div in PreH17.
  eapply (reduced_merge_equation_from_bezout__merge_transition
    answer lcm (Znth i residue_values 0) (Znth i modulus_values 0)
    gcd x y (retval + reduced_modulus) (q - 1)); eauto.
  nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hmodulus_divides :
      (gcd | Znth i modulus_values 0)).
  { rewrite PreH14. apply Z.gcd_divide_r. }
  assert (Hmodulus_quot_div :
      Znth i modulus_values 0 ÷ gcd =
      Znth i modulus_values 0 / gcd).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  assert (Hreduced_div :
      reduced_modulus = Znth i modulus_values 0 / gcd).
  { rewrite <- Hmodulus_quot_div. exact PreH17. }
  pose proof PreH5 as Hsafe.
  unfold ExtendedCRTIntSafe in Hsafe.
  destruct Hsafe as [Hprefix_bound _].
  specialize (Hprefix_bound (i + 1) ltac:(lia)).
  destruct Hprefix_bound as [_ Hbound].
  assert (Hstep :
      CRTLCMPrefix modulus_values (i + 1) =
      lcm * reduced_modulus).
  { eapply crt_lcm_prefix_step__merge_transition; eauto; lia. }
  rewrite Hstep in Hbound.
  exact Hbound.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ModularMul in PreH2.
  destruct PreH2 as [[Hretval_lower Hretval_upper] Hmul].
  lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply replace_Znth_Znth.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_4_1 : extended_chinese_remainder_theorem_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_3.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_4_1_split_goal_4.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (crt_merge_difference_divisible__merge_transition
      residue_values modulus_values n_pre i answer lcm
      PreH4 PreH13 (conj PreH6 PreH8)) as Hdifference.
  rewrite <- PreH14 in Hdifference.
  assert (Hmodulus_divides :
      (gcd | Znth i modulus_values 0)).
  { rewrite PreH14. apply Z.gcd_divide_r. }
  assert (Hdifference_quot_div :
      (Znth i residue_values 0 - answer) ÷ gcd =
      (Znth i residue_values 0 - answer) / gcd).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  assert (Hmodulus_quot_div :
      Znth i modulus_values 0 ÷ gcd =
      Znth i modulus_values 0 / gcd).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  unfold ModularMul in PreH2.
  destruct PreH2 as [[Hretval_lower Hretval_upper] [q Hmul]].
  rewrite Hdifference_quot_div in Hmul.
  rewrite Hmodulus_quot_div in PreH17.
  eapply (reduced_merge_equation_from_bezout__merge_transition
    answer lcm (Znth i residue_values 0) (Znth i modulus_values 0)
    gcd x y retval q); eauto.
  nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hmodulus_divides :
      (gcd | Znth i modulus_values 0)).
  { rewrite PreH14. apply Z.gcd_divide_r. }
  assert (Hmodulus_quot_div :
      Znth i modulus_values 0 ÷ gcd =
      Znth i modulus_values 0 / gcd).
  { apply quot_div_of_divide_pos__merge_transition; assumption. }
  assert (Hreduced_div :
      reduced_modulus = Znth i modulus_values 0 / gcd).
  { rewrite <- Hmodulus_quot_div. exact PreH17. }
  pose proof PreH5 as Hsafe.
  unfold ExtendedCRTIntSafe in Hsafe.
  destruct Hsafe as [Hprefix_bound _].
  specialize (Hprefix_bound (i + 1) ltac:(lia)).
  destruct Hprefix_bound as [_ Hbound].
  assert (Hstep :
      CRTLCMPrefix modulus_values (i + 1) =
      lcm * reduced_modulus).
  { eapply crt_lcm_prefix_step__merge_transition; eauto; lia. }
  rewrite Hstep in Hbound.
  exact Hbound.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ModularMul in PreH2.
  destruct PreH2 as [[Hretval_lower Hretval_upper] Hmul].
  lia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 : extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply replace_Znth_Znth.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_4_2 : extended_chinese_remainder_theorem_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_3.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_4_2_split_goal_4.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_1 : extended_chinese_remainder_theorem_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply crt_prefix_meaning_merge__merge_transition
    with (gcd := gcd).
  - exact PreH1.
  - exact PreH2.
  - lia.
  - lia.
  - exact PreH10.
  - exact PreH11.
  - exact PreH12.
  - rewrite PreH13.
    apply quot_div_of_divide_pos__merge_transition.
    + exact PreH12.
    + rewrite PreH11.
      apply Z.gcd_divide_r.
  - lia.
  - exact PreH20.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_2 : extended_chinese_remainder_theorem_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_entail_wit_5 : extended_chinese_remainder_theorem_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_return_wit_1_split_goal_1 : extended_chinese_remainder_theorem_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply crt_prefix_meaning_to_result__prefix_boundaries with (i := i).
  - lia.
  - lia.
  - exact PreH11.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_return_wit_1 : extended_chinese_remainder_theorem_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_extended_chinese_remainder_theorem_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 : extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre i PreH9 ltac:(lia)) as Hbounds.
  destruct Hbounds as [[Hmod_pos Hmod_max] [Hres_nonneg Hres_lt]].
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 : extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (extended_crt_index_bounds__machine_bounds
    residue_values modulus_values n_pre i PreH9 ltac:(lia)) as Hbounds.
  destruct Hbounds as [[Hmod_pos Hmod_max] [Hres_nonneg Hres_lt]].
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure : extended_chinese_remainder_theorem_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2.
Qed.
