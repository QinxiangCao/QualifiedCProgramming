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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P005_1891A_sorting_with_twos_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P005_1891A_sorting_with_twos_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P005_1891A_sorting_with_twos_lib.
Local Open Scope sac.

Lemma proof_of_is_power_of_two_return_wit_1_split_goal_1 : is_power_of_two_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NonPowerOfTwo.
  intros (m & Hm & Hpow).
  apply PreH1.
  subst x_pre.
  apply pow_land_pred_zero__power_classification.
  exact Hm.
Qed.

Lemma proof_of_is_power_of_two_return_wit_1 : is_power_of_two_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_is_power_of_two_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_is_power_of_two_return_wit_2_split_goal_1 : is_power_of_two_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PowerOfTwoPrefix.
  destruct (proj1 (land_pred_power_iff__power_classification x_pre ltac:(lia)) PreH1)
    as (m & Hm & Hpow).
  exists m.
  repeat split; assumption || lia.
Qed.

Lemma proof_of_is_power_of_two_return_wit_2 : is_power_of_two_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_is_power_of_two_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SortingWithTwosPrefix.
  intros k Hk.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH4.
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
  unfold SortingWithTwosPrefix in *.
  intros k Hk.
  destruct (Z.lt_trichotomy k i) as [Hlt | [Heq | Hgt]].
  - apply PreH9.
    lia.
  - left.
    subst k.
    exact PreH1.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SortingWithTwosPrefix in *.
  intros k Hk.
  destruct (Z.lt_trichotomy k i) as [Hlt | [Heq | Hgt]].
  - apply PreH12.
    lia.
  - right.
    subst k.
    unfold PowerOfTwoPrefix in *.
    destruct PreH3 as [m [Hm [Hi Hle]]].
    exists m.
    repeat split; try assumption.
    rewrite <- PreH6.
    lia.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  split.
  - right. reflexivity.
  - split.
    + intros _.
      apply sorting_prefix_reachable_monotone__final_success.
      * rewrite <- PreH2. lia.
      * replace (Zlength input) with i by lia.
        exact PreH8.
    + intros _. reflexivity.
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
  split.
  - left. reflexivity.
  - split.
    + intros Hzeroone. discriminate.
    + intros Hreachable.
      exfalso.
      eapply (reachable_nonpower_descent_refutes_mono__final_failure input i).
      * exact PreH3.
      * lia.
      * exact PreH4.
      * exact Hreachable.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.
