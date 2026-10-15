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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P041_1538F_interesting_function_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P041_1538F_interesting_function_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P041_1538F_interesting_function_lib.
Local Open Scope sac.

Lemma proof_of_changed_upto_safety_wit_5_split_goal_1 : changed_upto_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  assert (0 <= x_pre / p) by (apply Z_div_nonneg_nonneg; lia).
  assert (x_pre / p <= x_pre) by (apply Z.div_le_upper_bound; nia).
  lia.
Qed.

Lemma proof_of_changed_upto_safety_wit_5_split_goal_2 : changed_upto_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  assert (0 <= x_pre / p) by (apply Z_div_nonneg_nonneg; lia).
  lia.
Qed.

Lemma proof_of_changed_upto_safety_wit_5 : changed_upto_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_changed_upto_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_changed_upto_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_changed_upto_entail_wit_1_split_goal_1 : changed_upto_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply decimal_place_prefix_init__changed_upto.
Qed.

Lemma proof_of_changed_upto_entail_wit_1 : changed_upto_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_changed_upto_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_changed_upto_entail_wit_2_split_goal_1 : changed_upto_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply decimal_place_prefix_step__changed_upto; [lia | lia | exact PreH8].
Qed.

Lemma proof_of_changed_upto_entail_wit_2_split_goal_2 : changed_upto_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply decimal_place_prefix_step_bound__changed_upto; [lia | lia | exact PreH8].
Qed.

Lemma proof_of_changed_upto_entail_wit_2_split_goal_3 : changed_upto_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (0 <= x_pre / p) by (apply Z_div_nonneg_nonneg; lia).
  lia.
Qed.

Lemma proof_of_changed_upto_entail_wit_2 : changed_upto_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_changed_upto_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_changed_upto_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_changed_upto_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_changed_upto_return_wit_1_split_goal_1 : changed_upto_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold DecimalPrefixTotal.
  exists p.
  split; [lia | exact PreH8].
Qed.

Lemma proof_of_changed_upto_return_wit_1 : changed_upto_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_changed_upto_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  unfold solver_return_wit_1_split_goal_1.
  intros r_pre l_pre retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5
    PreH6 PreH7 PreH8 PreH9.
  unfold Spec.
  exists (fun x =>
    SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.sum_range
      0 9 (fun d => (x + 1) / Z.pow 10 d) -
    SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.sum_range
      0 9 (fun d => x / Z.pow 10 d)).
  split.
  - intros x Hx.
    apply changed_digits_successor_sum_delta__solver_result. lia.
  - pose proof (decimal_prefix_total_canonical_sum__solver_result
      l_pre retval_2 ltac:(lia) PreH3) as Hl.
    pose proof (decimal_prefix_total_canonical_sum__solver_result
      r_pre retval ltac:(lia) PreH6) as Hr.
    pose proof (sum_range_difference_telescope__solver_result
      (fun y => SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.sum_range
        0 9 (fun d => y / Z.pow 10 d))
      l_pre r_pre ltac:(lia)) as Htel.
    cbn beta in Htel. lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
