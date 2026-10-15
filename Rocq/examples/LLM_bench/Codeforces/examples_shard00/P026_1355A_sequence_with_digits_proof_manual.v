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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P026_1355A_sequence_with_digits_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P026_1355A_sequence_with_digits_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib.
Local Open Scope sac.

Lemma proof_of_step_entail_wit_1_split_goal_1 : step_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply digit_scan_state_initial__step_initialization.
  lia.
Qed.

Lemma proof_of_step_entail_wit_1 : step_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_step_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_step_entail_wit_2_1_split_goal_1 : step_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (signed_decimal_remainder_bounds__step_transitions x PreH5) as Hd.
  assert (Hsigned : signed_last_nbits (Z.rem x 10) 32 = Z.rem x 10).
  { apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in *.
  pose proof (digit_scan_state_advance__step_transitions
    x_pre x mn mx PreH11 PreH5 PreH12) as Hadvance.
  rewrite Z.min_r in Hadvance by lia.
  rewrite Z.max_r in Hadvance by lia.
  exact Hadvance.
Qed.

Lemma proof_of_step_entail_wit_2_1_split_goal_2 : step_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (x / 10 <= x) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_step_entail_wit_2_1_split_goal_3 : step_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_step_entail_wit_2_1 : step_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_step_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_step_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_step_entail_wit_2_1_split_goal_3.
Qed.

Lemma proof_of_step_entail_wit_2_2_split_goal_1 : step_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (signed_decimal_remainder_bounds__step_transitions x PreH5) as Hd.
  assert (Hsigned : signed_last_nbits (Z.rem x 10) 32 = Z.rem x 10).
  { apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in *.
  pose proof (digit_scan_state_advance__step_transitions
    x_pre x mn mx PreH11 PreH5 PreH12) as Hadvance.
  rewrite Z.min_l in Hadvance by lia.
  rewrite Z.max_r in Hadvance by lia.
  exact Hadvance.
Qed.

Lemma proof_of_step_entail_wit_2_2_split_goal_2 : step_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (signed_decimal_remainder_bounds__step_transitions x PreH5) as Hd.
  assert (Hsigned : signed_last_nbits (Z.rem x 10) 32 = Z.rem x 10).
  { apply signed_last_nbits_eq; lia. }
  rewrite Hsigned.
  lia.
Qed.

Lemma proof_of_step_entail_wit_2_2_split_goal_3 : step_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (x / 10 <= x) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_step_entail_wit_2_2_split_goal_4 : step_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_step_entail_wit_2_2 : step_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_step_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_step_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_step_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_step_entail_wit_2_2_split_goal_4.
Qed.

Lemma proof_of_step_entail_wit_2_3_split_goal_1 : step_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (signed_decimal_remainder_bounds__step_transitions x PreH5) as Hd.
  assert (Hsigned : signed_last_nbits (Z.rem x 10) 32 = Z.rem x 10).
  { apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in *.
  pose proof (digit_scan_state_advance__step_transitions
    x_pre x mn mx PreH11 PreH5 PreH12) as Hadvance.
  rewrite Z.min_r in Hadvance by lia.
  rewrite Z.max_l in Hadvance by lia.
  exact Hadvance.
Qed.

Lemma proof_of_step_entail_wit_2_3_split_goal_2 : step_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (signed_decimal_remainder_bounds__step_transitions x PreH5) as Hd.
  assert (Hsigned : signed_last_nbits (Z.rem x 10) 32 = Z.rem x 10).
  { apply signed_last_nbits_eq; lia. }
  rewrite Hsigned.
  lia.
Qed.

Lemma proof_of_step_entail_wit_2_3_split_goal_3 : step_entail_wit_2_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (x / 10 <= x) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_step_entail_wit_2_3_split_goal_4 : step_entail_wit_2_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_step_entail_wit_2_3 : step_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_step_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_step_entail_wit_2_3_split_goal_2.
  - Goal_apply proof_of_step_entail_wit_2_3_split_goal_3.
  - Goal_apply proof_of_step_entail_wit_2_3_split_goal_4.
Qed.

Lemma proof_of_step_entail_wit_2_4_split_goal_1 : step_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (signed_decimal_remainder_bounds__step_transitions x PreH5) as Hd.
  assert (Hsigned : signed_last_nbits (Z.rem x 10) 32 = Z.rem x 10).
  { apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in *.
  pose proof (digit_scan_state_advance__step_transitions
    x_pre x mn mx PreH11 PreH5 PreH12) as Hadvance.
  rewrite Z.min_l in Hadvance by lia.
  rewrite Z.max_l in Hadvance by lia.
  exact Hadvance.
Qed.

Lemma proof_of_step_entail_wit_2_4_split_goal_2 : step_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (x / 10 <= x) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_step_entail_wit_2_4_split_goal_3 : step_entail_wit_2_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_step_entail_wit_2_4 : step_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_step_entail_wit_2_4_split_goal_1.
  - Goal_apply proof_of_step_entail_wit_2_4_split_goal_2.
  - Goal_apply proof_of_step_entail_wit_2_4_split_goal_3.
Qed.

Lemma proof_of_step_return_wit_1_split_goal_1 : step_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply digit_scan_state_complete__step_finalization.
  rewrite <- PreH10.
  exact PreH9.
Qed.

Lemma proof_of_step_return_wit_1 : step_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_step_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply sequence_prefix_base__solver_prefix.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try subst retval.
  try subst a_pre.
  eapply sequence_fixed_point_spec__solver_results with (i := i).
  - exact PreH11.
  - exact PreH12.
  - exact PreH16.
  - replace (a + 0) with a in PreH4 by lia.
    exact PreH4.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst a_pre.
  eapply sequence_prefix_extend__solver_prefix; eauto.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace a_pre with a1 by lia.
  replace k_pre with i by lia.
  apply sequence_prefix_index_spec__solver_results.
  exact PreH12.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
