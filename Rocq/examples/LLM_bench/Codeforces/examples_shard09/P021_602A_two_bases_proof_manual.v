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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P021_602A_two_bases_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P021_602A_two_bases_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_lib.
Local Open Scope sac.

Lemma proof_of_numeral_value_safety_wit_4_split_goal_1 : numeral_value_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdigit : 0 <= Znth i digits 0 < b_pre).
  { apply PreH7. lia. }
  assert (Hnext : v * b_pre + Znth i digits 0 <= 40 ^ (i + 1) - 1).
  { apply pow40_successor_bound__numeral_arithmetic; lia. }
  assert (Hlimit : 40 ^ (i + 1) - 1 <= 9223372036854775807).
  { apply pow40_int64_bound__numeral_arithmetic. lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_numeral_value_safety_wit_4_split_goal_2 : numeral_value_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdigit : 0 <= Znth i digits 0 < b_pre).
  { apply PreH7. lia. }
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_numeral_value_safety_wit_4 : numeral_value_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_numeral_value_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_numeral_value_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_numeral_value_safety_wit_5_split_goal_1 : numeral_value_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hnext : v * b_pre + 0 <= 40 ^ (i + 1) - 1).
  { apply pow40_successor_bound__numeral_arithmetic; lia. }
  assert (Hlimit : 40 ^ (i + 1) - 1 <= 9223372036854775807).
  { apply pow40_int64_bound__numeral_arithmetic. lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_numeral_value_safety_wit_5_split_goal_2 : numeral_value_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_numeral_value_safety_wit_5 : numeral_value_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_numeral_value_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_numeral_value_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_numeral_value_entail_wit_1_split_goal_1 : numeral_value_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_numeral_value_entail_wit_1_split_goal_2 : numeral_value_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_numeral_value_entail_wit_1_split_goal_3 : numeral_value_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  lia.
Qed.

Lemma proof_of_numeral_value_entail_wit_1 : numeral_value_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_numeral_value_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_numeral_value_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_numeral_value_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_numeral_value_entail_wit_2_split_goal_1 : numeral_value_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hdigit : 0 <= Znth i digits 0 < b_pre).
  { apply PreH7. lia. }
  apply pow40_successor_bound__numeral_arithmetic; lia.
Qed.

Lemma proof_of_numeral_value_entail_wit_2_split_goal_2 : numeral_value_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite numeral_sublist_succ__numeral_arithmetic by lia.
  rewrite <- PreH10.
  reflexivity.
Qed.

Lemma proof_of_numeral_value_entail_wit_2 : numeral_value_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_numeral_value_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_numeral_value_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_numeral_value_return_wit_1_split_goal_1 : numeral_value_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH6 in PreH10.
  rewrite numeral_sublist_full__numeral_endpoints in PreH10.
  exact PreH10.
Qed.

Lemma proof_of_numeral_value_return_wit_1 : numeral_value_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_numeral_value_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  left.
  split; [reflexivity |].
  rewrite <- PreH3, <- PreH2.
  exact PreH1.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  right; left.
  split; [reflexivity |].
  rewrite <- PreH4, <- PreH3.
  exact PreH1.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  right; right.
  split; [reflexivity |].
  rewrite <- PreH4, <- PreH3.
  lia.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
Qed.

Lemma proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_1.
Qed.
