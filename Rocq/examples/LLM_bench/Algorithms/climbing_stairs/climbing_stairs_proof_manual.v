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
From SimpleC.EE.LLM_bench.Algorithms.climbing_stairs Require Import climbing_stairs_goal.
From SimpleC.EE.LLM_bench.Algorithms.climbing_stairs Require Import climbing_stairs_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.climbing_stairs.climbing_stairs_lib.
Local Open Scope sac.


Lemma proof_of_climbStairs_safety_wit_4_split_goal_1 : climbStairs_safety_wit_4_split_goal_1.
Proof.
  unfold climbStairs_safety_wit_4_split_goal_1.
  intros n curr prev i Hguard Hn Hmax Hi Hiend Hp Hc Hprev Hcurr.
  assert (Hcount : ClimbingStairsCount i (prev + curr)).
  { replace i with ((i - 2) + 2) by lia.
    apply ClimbingStairsCount_next; try lia; auto.
    replace (i - 2 + 1) with (i - 1) by lia. exact Hcurr. }
  pose proof (ClimbingStairsCount_int_range_upto_45__loop_transition i (prev + curr) ltac:(lia) ltac:(lia) Hcount).
  entailer!.
Qed.
Lemma proof_of_climbStairs_safety_wit_4_split_goal_2 : climbStairs_safety_wit_4_split_goal_2.
Proof. unfold climbStairs_safety_wit_4_split_goal_2; intros; entailer!. Qed.
Lemma proof_of_climbStairs_safety_wit_4 : climbStairs_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_climbStairs_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_climbStairs_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_climbStairs_entail_wit_1_split_goal_1 : climbStairs_entail_wit_1_split_goal_1.
Proof.
  unfold climbStairs_entail_wit_1_split_goal_1.
  intros.
  replace (2 - 1) with 1 by lia.
  apply ClimbingStairsCount_one.
Qed.

Lemma proof_of_climbStairs_entail_wit_1_split_goal_2 : climbStairs_entail_wit_1_split_goal_2.
Proof.
  unfold climbStairs_entail_wit_1_split_goal_2.
  intros.
  replace (2 - 2) with 0 by lia.
  apply ClimbingStairsCount_zero.
Qed.

Lemma proof_of_climbStairs_entail_wit_1 : climbStairs_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_climbStairs_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_climbStairs_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_climbStairs_entail_wit_2_split_goal_1 : climbStairs_entail_wit_2_split_goal_1.
Proof.
  intros n_pre curr prev i PreH1 PreH2 PreH3 PreH4 PreH5
    PreH6 PreH7 PreH8 PreH9.
  replace ((i + 1) - 1) with ((i - 2) + 2) by lia.
  eapply ClimbingStairsCount_next.
  - lia.
  - exact PreH8.
  - replace (i - 2 + 1) with (i - 1) by lia.
    exact PreH9.
Qed.

Lemma proof_of_climbStairs_entail_wit_2_split_goal_2 : climbStairs_entail_wit_2_split_goal_2.
Proof.
  intros n_pre curr prev i PreH1 PreH2 PreH3 PreH4 PreH5
    PreH6 PreH7 PreH8 PreH9.
  replace ((i + 1) - 2) with (i - 1) by lia.
  exact PreH9.
Qed.

Lemma proof_of_climbStairs_entail_wit_2 : climbStairs_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_climbStairs_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_climbStairs_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_climbStairs_return_wit_1_split_goal_1 : climbStairs_return_wit_1_split_goal_1.
Proof.
  unfold climbStairs_return_wit_1_split_goal_1.
  intros n_pre curr prev i PreH1 PreH2 PreH3 PreH4 PreH5
    PreH6 PreH7 PreH8 PreH9.
  assert (i = n_pre + 1) by lia.
  replace n_pre with (i - 1) by lia.
  exact PreH9.
Qed.

Lemma proof_of_climbStairs_return_wit_1 : climbStairs_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_climbStairs_return_wit_1_split_goal_1.
Qed.
