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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P019_1807G2_subsequence_addition_hard_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P019_1807G2_subsequence_addition_hard_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P019_1807G2_subsequence_addition_hard_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixAdditionState.
  split; [lia |].
  split.
  - replace (1 : Z) with (0 + 1) by lia.
    rewrite (sublist_single 0 0 sorted_2) by lia.
    simpl.
    lia.
  - split; [exact PreH1 |].
    intros k Hk.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply sorted_index_bounds_from_permutation__prefix_state.
  - exact PreH9.
  - exact PreH2.
  - lia.
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
  unfold PrefixAdditionState in *.
  destruct PreH15 as [Hprocessed [Hsum [Hhead Hprefix]]].
  split; [lia |].
  split.
  - rewrite sum_sublist_succ__prefix_state by lia.
    rewrite <- Hsum.
    reflexivity.
  - split; [exact Hhead |].
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + apply Hprefix.
      lia.
    + assert (k = i) by lia.
      subst k.
      rewrite <- Hsum.
      exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (proj2 (PreH8 1)).
  split.
  - right; reflexivity.
  - split.
    + intros _.
      eapply (prefix_state_at_end_sorted_acceptance__decision_results
        sorted i sum).
      * lia.
      * exact PreH14.
    + intros _.
      reflexivity.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (proj2 (PreH9 0)).
  split.
  - left; reflexivity.
  - split.
    + lia.
    + intros Haccept.
      exfalso.
      eapply (prefix_state_violation_not_sorted_acceptance__decision_results
        sorted i sum).
      * lia.
      * exact PreH15.
      * exact PreH1.
      * exact Haccept.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (proj2 (PreH5 0)).
  split.
  - left; reflexivity.
  - split.
    + lia.
    + intros Haccept.
      unfold SortedAcceptance in Haccept.
      tauto.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.
