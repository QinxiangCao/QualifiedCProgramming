Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.house_robber Require Import house_robber_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.
Local Open Scope sac.

Lemma proof_of_rob_entail_wit_1 : rob_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold HouseRobberDPState.
    split.
    + rewrite PreH3. lia.
    + split.
      * apply RobPrefixOpt_zero.
      * left. split; reflexivity.
Qed.

Lemma proof_of_rob_entail_wit_2_2 : rob_entail_wit_2_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; auto; try lia.
    eapply HouseRobberDPState_skip_step; eauto; lia.
Qed. 

Lemma proof_of_rob_entail_wit_2_1 : rob_entail_wit_2_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre n_pre l).
  - split_pures.
    all: dump_pre_spatial; auto; try lia.
    + apply house_robber_take_value_bound with (n := n_pre) (prev1 := prev1); auto; lia.
    + apply house_robber_dp_step_take with (n := n_pre); auto; lia.
Qed.

Lemma proof_of_rob_entail_wit_3_split_goal_1 : rob_entail_wit_3_split_goal_1.
Proof.
  pre_process.
  apply PreH4.
  exact H.
Qed.

Lemma proof_of_rob_entail_wit_3 : rob_entail_wit_3.
Proof.
  pre_process.
Qed.

Lemma proof_of_rob_return_wit_1 : rob_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold HouseRobberDPState in PreH12.
      destruct PreH12 as [_ [Hopt _]].
      unfold HouseRobberAnswer.
      replace (Zlength l) with i by lia.
      exact Hopt.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
Qed.
