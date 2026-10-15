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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P029_817A_treasure_hunt_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P029_817A_treasure_hunt_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P029_817A_treasure_hunt_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_1_split_goal_1 : solver_entail_wit_1_1_split_goal_1.
Proof.
  unfold solver_entail_wit_1_1_split_goal_1.
  intros.
  unfold AbsDiff.
  destruct (Z.ltb x1_pre x2_pre) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. lia.
  - reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_1 : solver_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  eapply proof_of_solver_entail_wit_1_1_split_goal_1; eauto.
Qed. 

Lemma proof_of_solver_entail_wit_1_2_split_goal_1 : solver_entail_wit_1_2_split_goal_1.
Proof.
  unfold solver_entail_wit_1_2_split_goal_1.
  intros.
  unfold AbsDiff.
  destruct (Z.ltb x1_pre x2_pre) eqn:Hlt.
  - reflexivity.
  - apply Z.ltb_ge in Hlt. lia.
Qed.

Lemma proof_of_solver_entail_wit_1_2 : solver_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  eapply proof_of_solver_entail_wit_1_2_split_goal_1; eauto.
Qed. 

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  unfold solver_entail_wit_2_1_split_goal_1.
  intros.
  unfold AbsDiff.
  destruct (Z.ltb y1_pre y2_pre) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. lia.
  - reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  eapply proof_of_solver_entail_wit_2_1_split_goal_1; eauto.
Qed. 

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  unfold solver_entail_wit_2_2_split_goal_1.
  intros.
  unfold AbsDiff.
  destruct (Z.ltb y1_pre y2_pre) eqn:Hlt.
  - reflexivity.
  - apply Z.ltb_ge in Hlt. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  eapply proof_of_solver_entail_wit_2_2_split_goal_1; eauto.
Qed. 

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  intros.
  unfold Spec, Reachable.
  right.
  split.
  - intros [_ [_ Heq]].
    congruence.
  - reflexivity.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  eapply proof_of_solver_return_wit_1_split_goal_1; eauto.
Qed. 

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  intros.
  unfold Spec, Reachable.
  left.
  split.
  - repeat split; assumption.
  - reflexivity.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  eapply proof_of_solver_return_wit_2_split_goal_1; eauto.
Qed. 

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  intros.
  unfold Spec, Reachable.
  right.
  split.
  - intros [Hrem _].
    congruence.
  - reflexivity.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  eapply proof_of_solver_return_wit_3_split_goal_1; eauto.
Qed. 

Lemma proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1.
Proof.
  intros.
  unfold Spec, Reachable.
  right.
  split.
  - intros [_ [Hrem _]].
    congruence.
  - reflexivity.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  aggressive_pre_process.
  eapply proof_of_solver_return_wit_4_split_goal_1; eauto.
Qed. 

