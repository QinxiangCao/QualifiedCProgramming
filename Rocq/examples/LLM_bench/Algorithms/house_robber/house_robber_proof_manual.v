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
From SimpleC.EE.LLM_bench.Algorithms.house_robber Require Import house_robber_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.
Require Import AUXLib.MonotonicList.
Local Open Scope sac.

Lemma proof_of_rob_safety_wit_4 : rob_safety_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hrange : forall k, 0 <= k < n_pre ->
      0 <= Znth k l 0 <= 10000).
  { rewrite (Forall_Znth _ 0 _) in PreH4.
    rewrite (Forall_Znth _ 0 _) in PreH5.
    intros k Hk.
    specialize (PreH4 k ltac:(lia)).
    specialize (PreH5 k ltac:(lia)).
    lia. }
  pose proof (house_robber_take_value_bound l n_pre i prev2 prev1
    PreH3 PreH2 Hrange PreH6 PreH1 PreH8) as Hupper.
  assert (Hprev2 : 0 <= prev2).
  { destruct PreH8 as [_ [[Hi0 Hp0] | [Hi Hopt]]].
    - lia.
    - pose proof (rob_prefix_opt_bound_by_len l (i - 1) prev2 n_pre
        ltac:(lia) Hrange Hopt) as [Hnonneg _].
      exact Hnonneg. }
  pose proof (Hrange i ltac:(lia)) as [Hcurrent _].
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_rob_entail_wit_1 : rob_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    unfold HouseRobberDPState.
    split.
    + apply RobPrefixOpt_zero.
    + left. split; reflexivity.
Qed.

Lemma proof_of_rob_entail_wit_2_1 : rob_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; auto; try lia.
    apply house_robber_dp_step_take with (n := n_pre); auto; lia.
Qed.

Lemma proof_of_rob_entail_wit_2_2 : rob_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; auto; try lia.
    eapply HouseRobberDPState_skip_step; eauto; lia.
Qed.

Lemma proof_of_rob_return_wit_1 : rob_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures. dump_pre_spatial.
    destruct PreH8 as [Hopt _].
    unfold HouseRobberAnswer.
    replace (Zlength l) with i by lia.
    exact Hopt.
Qed.
