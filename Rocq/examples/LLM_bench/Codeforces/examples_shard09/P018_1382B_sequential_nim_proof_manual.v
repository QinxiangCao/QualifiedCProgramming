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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P018_1382B_sequential_nim_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P018_1382B_sequential_nim_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(intros; lia).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(intros; apply PreH3; assumption).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_1 : solver_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    unfold LeadingOnes;
    split; [lia | split; [assumption | left; lia]]).
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_1 : solver_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    unfold LeadingOnes;
    split; [lia | split; [assumption | right; assumption]]).
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hnotfirst : ~ FirstWins piles).
  {
    intros [k [Hleading Hwinner]].
    assert (Hkc : k = c).
    {
      apply leading_ones_unique__return_semantics with (piles := piles).
      - exact Hleading.
      - exact PreH8.
    }
    subst k.
    destruct Hwinner as [[Hend Heven] | [Hbefore Heven]].
    - rewrite <- PreH5 in Hend. lia.
    - assert (Hodd : Z.even c = false).
      {
        apply odd_of_nonnegative_rem_nonzero__return_semantics; assumption.
      }
      rewrite Hodd in Heven. discriminate.
  }
  assert (Hspec : Spec piles 0).
  {
    unfold Spec.
    right. split; [reflexivity | exact Hnotfirst].
  }
  assert (Hbridge : SolverReturnBridge 0 0).
  {
    unfold SolverReturnBridge.
    right. auto.
  }
  Exists 0.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre piles).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hbridge.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Heven : Z.even c = true).
  {
    apply even_of_nonnegative_rem_zero__return_semantics; assumption.
  }
  assert (Hfirst : FirstWins piles).
  {
    unfold FirstWins.
    exists c. split; [exact PreH8 |].
    right. split; [rewrite <- PreH5; lia | exact Heven].
  }
  assert (Hspec : Spec piles 1).
  {
    unfold Spec.
    left. split; [reflexivity | exact Hfirst].
  }
  assert (Hbridge : SolverReturnBridge 1 1).
  {
    unfold SolverReturnBridge.
    left. auto.
  }
  Exists 1.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre piles).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hbridge.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Heven : Z.even n_pre = true).
  {
    apply even_of_nonnegative_rem_not_one__return_semantics; [lia | exact PreH1].
  }
  assert (Hnotfirst : ~ FirstWins piles).
  {
    intros [k [Hleading Hwinner]].
    assert (Hkc : k = c).
    {
      apply leading_ones_unique__return_semantics with (piles := piles).
      - exact Hleading.
      - exact PreH8.
    }
    subst k.
    destruct Hwinner as [[Hend Hodd] | [Hbefore Hparity]].
    - rewrite PreH2 in Hodd. rewrite Heven in Hodd. discriminate.
    - rewrite <- PreH5 in Hbefore. lia.
  }
  assert (Hspec : Spec piles 0).
  {
    unfold Spec.
    right. split; [reflexivity | exact Hnotfirst].
  }
  assert (Hbridge : SolverReturnBridge 0 0).
  {
    unfold SolverReturnBridge.
    right. auto.
  }
  Exists 0.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre piles).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hbridge.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hodd : Z.even n_pre = false).
  {
    apply odd_of_nonnegative_rem_nonzero__return_semantics; [lia | lia].
  }
  assert (Hfirst : FirstWins piles).
  {
    unfold FirstWins.
    exists c. split; [exact PreH8 |].
    left. split.
    - rewrite PreH2, <- PreH5. reflexivity.
    - rewrite PreH2. exact Hodd.
  }
  assert (Hspec : Spec piles 1).
  {
    unfold Spec.
    left. split; [reflexivity | exact Hfirst].
  }
  assert (Hbridge : SolverReturnBridge 1 1).
  {
    unfold SolverReturnBridge.
    left. auto.
  }
  Exists 1.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre piles).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hbridge.
Qed.
