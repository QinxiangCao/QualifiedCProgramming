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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P017_753A_santa_claus_and_candies_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P017_753A_santa_claus_and_candies_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_14_split_goal_1 : solver_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = k) by lia.
  subst i.
  pose proof
    (candy_prefix_last_value__arithmetic_and_prefix
       k written PreH12 ltac:(lia)) as Hlast.
  replace (k - 1 - 0) with (k - 1) by lia.
  rewrite Hlast.
  dump_pre_spatial.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_14_split_goal_2 : solver_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = k) by lia.
  subst i.
  pose proof
    (candy_prefix_last_value__arithmetic_and_prefix
       k written PreH12 ltac:(lia)) as Hlast.
  replace (k - 1 - 0) with (k - 1) by lia.
  rewrite Hlast.
  dump_pre_spatial.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH6.
  unfold triangular.
  replace ((k + 1) * (k + 1 + 1))
    with (k * (k + 1) + (k + 1) * 2) by ring.
  rewrite Z.div_add by lia.
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
  unfold CandyPrefix.
  split.
  - rewrite Zlength_nil. reflexivity.
  - intros j Hj. lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec k 0) as [Hk | Hk].
  - subst k.
    assert (Htri0 : triangular 0 = 0) by
      (unfold triangular; reflexivity).
    rewrite Htri0 in PreH6.
    subst used.
    lia.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply candy_prefix_snoc__arithmetic_and_prefix; assumption || lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = k) as Hi by lia. subst i.
  Exists (replace_Znth (k - 1)
    (Znth (k - 1) written 0 + (n_pre - used)) written).
  split_pure_spatial.
  - replace (k - 1 - 0) with (k - 1) by lia.
    cancel.
  - pose proof
      (greedy_candy_plan_spec__greedy_finalization
        n_pre k used written ltac:(lia) PreH6 PreH8 PreH9 PreH12)
      as [Hplan Hspec].
    split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists out_spec_2.
  unfold GreedyCandyPlan in PreH9.
  destruct PreH9 as [Hlen _].
  split_pure_spatial.
  - rewrite Hlen.
    cancel (IntArray.full out_pre k out_spec_2).
    cancel (IntArray.undef_seg out_pre k n_pre).
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.
