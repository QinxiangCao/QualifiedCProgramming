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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P050_440B_balancer_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P050_440B_balancer_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P050_440B_balancer_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH3.
  rewrite <- PreH5.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9.
  rewrite sum_sublist_succ__prefix_accounting by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_le_upper_bound.
  - lia.
  - nia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  apply Z_div_nonneg_nonneg; lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_5 : solver_entail_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH9.
  rewrite <- PreH4.
  destruct (sum_sublist_full__prefix_accounting values) as [_ Hsum].
  rewrite Hsum.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_6 : solver_entail_wit_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite PreH9.
  rewrite <- PreH4.
  apply (proj2 (sum_sublist_full__prefix_accounting values)).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_7 : solver_entail_wit_3_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH6 i ltac:(lia)) as Hvalue.
  pose proof (prefix_step_magnitude_bound__transport_step
    balance (Znth i values 0) target i
    ltac:(lia) Hvalue ltac:(lia)) as [Hlower Hupper].
  nia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH19.
  rewrite prefix_transport_cost_succ__transport_step by lia.
  rewrite prefix_imbalance_succ__transport_step by lia.
  rewrite PreH5.
  rewrite <- PreH16.
  assert (Hsum_nonneg : 0 <= ListLib.sum values) by lia.
  rewrite <- Z.quot_div_nonneg by lia.
  rewrite <- PreH11.
  rewrite Z.abs_neq by lia.
  ring.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH6 i ltac:(lia)) as Hvalue.
  pose proof (prefix_step_magnitude_bound__transport_step
    balance (Znth i values 0) target i
    ltac:(lia) Hvalue ltac:(lia)) as [Hlower Hupper].
  exact Hlower.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_4 : solver_entail_wit_4_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH16.
  rewrite prefix_imbalance_succ__transport_step by lia.
  rewrite PreH5.
  assert (Hsum_nonneg : 0 <= ListLib.sum values) by lia.
  rewrite <- Z.quot_div_nonneg by lia.
  rewrite <- PreH11.
  ring.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH6 i ltac:(lia)) as Hvalue.
  pose proof (prefix_step_magnitude_bound__transport_step
    balance (Znth i values 0) target i
    ltac:(lia) Hvalue ltac:(lia)) as [Hlower Hupper].
  nia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH19.
  rewrite prefix_transport_cost_succ__transport_step by lia.
  rewrite prefix_imbalance_succ__transport_step by lia.
  rewrite PreH5.
  rewrite <- PreH16.
  assert (Hsum_nonneg : 0 <= ListLib.sum values) by lia.
  rewrite <- Z.quot_div_nonneg by lia.
  rewrite <- PreH11.
  rewrite Z.abs_eq by lia.
  ring.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_3 : solver_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH16.
  rewrite prefix_imbalance_succ__transport_step by lia.
  rewrite PreH5.
  assert (Hsum_nonneg : 0 <= ListLib.sum values) by lia.
  rewrite <- Z.quot_div_nonneg by lia.
  rewrite <- PreH11.
  ring.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace i with (n_pre - 1) in * by lia.
  rewrite PreH18.
  rewrite <- PreH4.
  apply prefix_transport_cost_optimal__final_optimality.
  exact PreH6.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed. 
