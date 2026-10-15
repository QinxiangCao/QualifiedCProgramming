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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P006_867A_between_the_offices_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P006_867A_between_the_offices_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P006_867A_between_the_offices_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfirst : Znth 0 days 0 = 70).
  {
    specialize (PreH7 0) as Halpha.
    assert (Hbounds : 0 <= 0 < n_pre) by lia.
    specialize (Halpha Hbounds).
    destruct Halpha as [H83 | H70].
    - exfalso. apply PreH1. rewrite <- PreH2. exact H83.
    - exact H70.
  }
  assert (Hlen : 2 <= Zlength days) by lia.
  assert (Halpha : forall i, 0 <= i < Zlength days ->
      Znth i days 0 = 83 \/ Znth i days 0 = 70).
  {
    intros i Hi. apply PreH7. lia.
  }
  pose proof
    (transition_count_balance_by_endpoints__endpoint_verdicts
       days Hlen Halpha) as Hbalance.
  assert (Hspec : Spec days false).
  {
    unfold Spec.
    right. split; [reflexivity |].
    rewrite Hfirst in Hbalance.
    destruct (Z.eqb (Znth (Zlength days - 1) days 0) 83);
      simpl in Hbalance; lia.
  }
  assert (Hverdict : VerdictCode false 0).
  {
    unfold VerdictCode. right. auto.
  }
  Exists false.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (n_pre + 1) (days +:: 0)).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hverdict.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfirst : Znth 0 days 0 = 83).
  {
    rewrite PreH3. exact PreH2.
  }
  assert (Hlast : Znth (Zlength days - 1) days 0 = 70).
  {
    rewrite <- PreH5.
    rewrite PreH4. exact PreH1.
  }
  assert (Hlen : 2 <= Zlength days) by lia.
  assert (Halpha : forall i, 0 <= i < Zlength days ->
      Znth i days 0 = 83 \/ Znth i days 0 = 70).
  {
    intros i Hi. apply PreH8. lia.
  }
  pose proof
    (transition_count_balance_by_endpoints__endpoint_verdicts
       days Hlen Halpha) as Hbalance.
  assert (Hspec : Spec days true).
  {
    unfold Spec.
    left. split; [reflexivity |].
    rewrite Hfirst, Hlast in Hbalance.
    simpl in Hbalance. lia.
  }
  assert (Hverdict : VerdictCode true 1).
  {
    unfold VerdictCode. left. auto.
  }
  Exists true.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (n_pre + 1) (days +:: 0)).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hverdict.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hfirst : Znth 0 days 0 = 83).
  {
    rewrite PreH3. exact PreH2.
  }
  assert (Hlast_n : Znth (n_pre - 1) days 0 = 83).
  {
    specialize (PreH8 (n_pre - 1)) as Halpha_last.
    assert (Hbounds : 0 <= n_pre - 1 < n_pre) by lia.
    specialize (Halpha_last Hbounds).
    destruct Halpha_last as [H83 | H70].
    - exact H83.
    - exfalso. apply PreH1. rewrite <- PreH4. exact H70.
  }
  assert (Hlast : Znth (Zlength days - 1) days 0 = 83).
  {
    rewrite <- PreH5. exact Hlast_n.
  }
  assert (Hlen : 2 <= Zlength days) by lia.
  assert (Halpha : forall i, 0 <= i < Zlength days ->
      Znth i days 0 = 83 \/ Znth i days 0 = 70).
  {
    intros i Hi. apply PreH8. lia.
  }
  pose proof
    (transition_count_balance_by_endpoints__endpoint_verdicts
       days Hlen Halpha) as Hbalance.
  assert (Hspec : Spec days false).
  {
    unfold Spec.
    right. split; [reflexivity |].
    rewrite Hfirst, Hlast in Hbalance.
    simpl in Hbalance. lia.
  }
  assert (Hverdict : VerdictCode false 0).
  {
    unfold VerdictCode. right. auto.
  }
  Exists false.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (n_pre + 1) (days +:: 0)).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hverdict.
Qed.
