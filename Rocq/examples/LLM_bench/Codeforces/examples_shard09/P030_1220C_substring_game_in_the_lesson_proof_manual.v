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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P030_1220C_substring_game_in_the_lesson_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P030_1220C_substring_game_in_the_lesson_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SpecPrefix.
  split.
  - rewrite Zlength_nil. lia.
  - intros i Hi. lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixMinimum.
  split.
  - rewrite <- PreH4. lia.
  - left. lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH3. assumption.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply spec_prefix_snoc__prefix_transitions.
  - exact PreH11.
  - lia.
  - right. split; [reflexivity |].
    intro Hann.
    assert (Hchar : Znth k text 0 <= 122).
    { specialize (PreH6 k ltac:(lia)). lia. }
    apply (proj1 (ann_wins_iff_prefix_min_lt__prefix_transitions
      text k mn ltac:(lia) Hchar PreH10)) in Hann.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchar : Znth k text 0 <= 122).
  { specialize (PreH6 k ltac:(lia)). lia. }
  pose proof (prefix_minimum_step__prefix_transitions
    text k mn ltac:(lia) Hchar PreH10) as Hstep.
  rewrite Z.min_r in Hstep by lia.
  exact Hstep.
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
  eapply spec_prefix_snoc__prefix_transitions.
  - exact PreH11.
  - lia.
  - right. split; [reflexivity |].
    intro Hann.
    assert (Hchar : Znth k text 0 <= 122).
    { specialize (PreH6 k ltac:(lia)). lia. }
    apply (proj1 (ann_wins_iff_prefix_min_lt__prefix_transitions
      text k mn ltac:(lia) Hchar PreH10)) in Hann.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchar : Znth k text 0 <= 122).
  { specialize (PreH6 k ltac:(lia)). lia. }
  pose proof (prefix_minimum_step__prefix_transitions
    text k mn ltac:(lia) Hchar PreH10) as Hstep.
  rewrite Z.min_l in Hstep by lia.
  exact Hstep.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply spec_prefix_snoc__prefix_transitions.
  - exact PreH11.
  - lia.
  - left. split; [reflexivity |].
    assert (Hchar : Znth k text 0 <= 122).
    { specialize (PreH6 k ltac:(lia)). lia. }
    apply (proj2 (ann_wins_iff_prefix_min_lt__prefix_transitions
      text k mn ltac:(lia) Hchar PreH10)).
    exact PreH2.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchar : Znth k text 0 <= 122).
  { specialize (PreH6 k ltac:(lia)). lia. }
  pose proof (prefix_minimum_step__prefix_transitions
    text k mn ltac:(lia) Hchar PreH10) as Hstep.
  rewrite Z.min_l in Hstep by lia.
  exact Hstep.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (k = n_pre) by lia.
  subst k.
  Exists out_2.
  rewrite CharArray.undef_seg_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold SpecPrefix in PreH9.
    unfold Spec.
    destruct PreH9 as [Hlen Hspec].
    split.
    + lia.
    + intros i Hi.
      apply Hspec.
      lia.
Qed.
