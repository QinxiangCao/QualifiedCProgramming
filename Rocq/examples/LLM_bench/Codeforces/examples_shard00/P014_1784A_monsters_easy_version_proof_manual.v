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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P014_1784A_monsters_easy_version_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P014_1784A_monsters_easy_version_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixGreedyState.
  split; [lia |].
  exists (nil : list Z).
  split.
  - change (MaximalCascadePreparation (nil : list Z) (nil : list Z)).
    unfold MaximalCascadePreparation.
    split.
    + unfold CascadePreparation.
      split; [reflexivity |].
      split.
      * intros j Hj. rewrite Zlength_nil in Hj. lia.
      * split.
        -- intros Hj. rewrite Zlength_nil in Hj. lia.
        -- intros j Hj. rewrite Zlength_nil in Hj. lia.
    + intros alternative Halt j Hj. rewrite Zlength_nil in Hj. lia.
  - simpl. repeat split; try reflexivity.
    intros Hempty. rewrite PreH3 in Hempty. lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hinput : Forall (fun hp => 1 <= hp <= Zlength input) input).
  { apply Forall_Znth_bounds__greedy_transitions. exact PreH8. }
  assert (Hsorted : Forall (fun hp => 1 <= hp <= Zlength input) sorted_2).
  { eapply Permutation_Forall; eauto. }
  pose proof (Forall_Znth_elim__greedy_transitions
    sorted_2 1 (Zlength input) k Hsorted ltac:(lia)) as Hbound.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply prefix_greedy_step__greedy_transitions.
  - lia.
  - specialize (PreH10 i ltac:(lia)). lia.
  - exact PreH9.
  - exact PreH17.
  - rewrite Z.min_r by lia. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply prefix_greedy_step__greedy_transitions.
  - lia.
  - specialize (PreH10 i ltac:(lia)). lia.
  - exact PreH9.
  - exact PreH17.
  - rewrite Z.min_l by lia. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH10 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixGreedyState in PreH16.
  destruct PreH16 as [_ [prepared [_ [_ [_ Hspec]]]]].
  apply Hspec.
  lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
