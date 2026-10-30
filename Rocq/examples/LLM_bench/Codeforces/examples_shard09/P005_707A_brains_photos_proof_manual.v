From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P005_707A_brains_photos_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P005_707A_brains_photos_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (pre_rectangular_facts__initialization
    photo n_pre m_pre __default__List_Z PreH5 PreH6).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre * m_pre) by lia.
  assert (Hnotcolor : ~ HasColor photo).
  {
    intros Hcolor.
    apply (proj1 (has_color_concat_characterization__results photo)) in Hcolor.
    destruct Hcolor as [c [Hc Hcolor]].
    destruct (In_Znth_Zlength__results (concat photo) c 0 Hc)
      as [k [[Hk0 Hklen] HZnth]].
    specialize (PreH12 k ltac:(rewrite Hi, <- PreH9; lia)).
    rewrite HZnth in PreH12.
    destruct Hcolor as [-> | [-> | ->]]; tauto.
  }
  assert (Hspec : Spec photo false).
  {
    unfold Spec.
    right.
    split; [reflexivity | exact Hnotcolor].
  }
  assert (Hbridge : SolverReturnBridge false 0).
  {
    unfold SolverReturnBridge.
    right.
    auto.
  }
  Exists false.
  split_pure_spatial.
  - cancel (CharArray.full px_pre (n_pre * m_pre) (concat photo)).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hbridge.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hin : In (Znth i (concat photo) 0) (concat photo)).
  {
    apply Znth_In_range__results.
    rewrite PreH11.
    lia.
  }
  assert (Hcolor : HasColor photo).
  {
    apply (proj2 (has_color_concat_characterization__results photo)).
    exists (Znth i (concat photo) 0).
    split; [exact Hin | tauto].
  }
  assert (Hspec : Spec photo true).
  {
    unfold Spec.
    left.
    split; [reflexivity | exact Hcolor].
  }
  assert (Hbridge : SolverReturnBridge true 1).
  {
    unfold SolverReturnBridge.
    left.
    auto.
  }
  Exists true.
  split_pure_spatial.
  - cancel (CharArray.full px_pre (n_pre * m_pre) (concat photo)).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hbridge.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hin : In (Znth i (concat photo) 0) (concat photo)).
  {
    apply Znth_In_range__results.
    rewrite PreH10.
    lia.
  }
  assert (Hcolor : HasColor photo).
  {
    apply (proj2 (has_color_concat_characterization__results photo)).
    exists (Znth i (concat photo) 0).
    split; [exact Hin | tauto].
  }
  assert (Hspec : Spec photo true).
  {
    unfold Spec.
    left.
    split; [reflexivity | exact Hcolor].
  }
  assert (Hbridge : SolverReturnBridge true 1).
  {
    unfold SolverReturnBridge.
    left.
    auto.
  }
  Exists true.
  split_pure_spatial.
  - cancel (CharArray.full px_pre (n_pre * m_pre) (concat photo)).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hbridge.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hin : In (Znth i (concat photo) 0) (concat photo)).
  {
    apply Znth_In_range__results.
    rewrite PreH12.
    lia.
  }
  assert (Hcolor : HasColor photo).
  {
    apply (proj2 (has_color_concat_characterization__results photo)).
    exists (Znth i (concat photo) 0).
    split; [exact Hin | tauto].
  }
  assert (Hspec : Spec photo true).
  {
    unfold Spec.
    left.
    split; [reflexivity | exact Hcolor].
  }
  assert (Hbridge : SolverReturnBridge true 1).
  {
    unfold SolverReturnBridge.
    left.
    auto.
  }
  Exists true.
  split_pure_spatial.
  - cancel (CharArray.full px_pre (n_pre * m_pre) (concat photo)).
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hbridge.
Qed.
