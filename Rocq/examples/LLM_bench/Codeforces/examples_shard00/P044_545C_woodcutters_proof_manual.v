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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P044_545C_woodcutters_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P044_545C_woodcutters_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P044_545C_woodcutters_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH7 i ltac:(lia)).
  specialize (PreH9 i ltac:(lia)).
  destruct PreH7 as [[Hposition_lower Hposition_upper]
                     [Hheight_lower Hheight_upper]].
  destruct PreH9 as [Hposition_repr Hheight_repr].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH7 i ltac:(lia)).
  specialize (PreH9 i ltac:(lia)).
  destruct PreH7 as [[Hposition_lower Hposition_upper]
                     [Hheight_lower Hheight_upper]].
  destruct PreH9 as [Hposition_repr Hheight_repr].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_1 : solver_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH8 i ltac:(lia)).
  specialize (PreH10 i ltac:(lia)).
  destruct PreH8 as [[Hposition_lower Hposition_upper]
                     [Hheight_lower Hheight_upper]].
  destruct PreH10 as [Hposition_repr Hheight_repr].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_2 : solver_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH8 i ltac:(lia)).
  specialize (PreH10 i ltac:(lia)).
  destruct PreH8 as [[Hposition_lower Hposition_upper]
                     [Hheight_lower Hheight_upper]].
  destruct PreH10 as [Hposition_repr Hheight_repr].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_1 : solver_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH9 i ltac:(lia)).
  specialize (PreH11 i ltac:(lia)).
  destruct PreH9 as [[Hposition_lower Hposition_upper]
                     [Hheight_lower Hheight_upper]].
  destruct PreH11 as [Hposition_repr Hheight_repr].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_2 : solver_safety_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH9 i ltac:(lia)).
  specialize (PreH11 i ltac:(lia)).
  destruct PreH9 as [[Hposition_lower Hposition_upper]
                     [Hheight_lower Hheight_upper]].
  destruct PreH11 as [Hposition_repr Hheight_repr].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH9 0 ltac:(lia)) as [Hposition0 _].
  pose proof (Znth_indep trees 0 __default__Prod_Z_Z (0, 0) ltac:(lia))
    as Htree0.
  rewrite Htree0 in Hposition0.
  rewrite <- Hposition0.
  apply PrefixFellingState_init__prefix_transitions.
  - exact PreH5.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH9.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
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
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH10 i ltac:(lia)) as [Hposition Hheight].
  pose proof (Znth_indep trees i __default__Prod_Z_Z (0, 0) ltac:(lia))
    as Htree.
  rewrite Htree in Hposition, Hheight.
  rewrite <- Hposition, <- Hheight in PreH1.
  rewrite <- Hposition.
  eapply PrefixFellingState_step_left__prefix_transitions.
  - exact PreH9.
  - exact PreH11.
  - lia.
  - exact PreH15.
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
  destruct (PreH11 i ltac:(lia)) as [Hposition Hheight].
  destruct (PreH11 (i + 1) ltac:(lia)) as [Hposition_next _].
  pose proof (Znth_indep trees i __default__Prod_Z_Z (0, 0) ltac:(lia))
    as Htree.
  pose proof (Znth_indep trees (i + 1) __default__Prod_Z_Z (0, 0) ltac:(lia))
    as Htree_next.
  rewrite Htree in Hposition, Hheight.
  rewrite Htree_next in Hposition_next.
  rewrite <- Hposition, <- Hheight, <- Hposition_next in PreH1.
  rewrite <- Hposition, <- Hheight in PreH2.
  rewrite <- Hposition, <- Hheight.
  eapply PrefixFellingState_step_right__prefix_transitions.
  - exact PreH10.
  - exact PreH12.
  - lia.
  - exact PreH16.
  - lia.
  - exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH11 i ltac:(lia)) as [Hposition Hheight].
  destruct (PreH11 (i + 1) ltac:(lia)) as [Hposition_next _].
  pose proof (Znth_indep trees i __default__Prod_Z_Z (0, 0) ltac:(lia))
    as Htree.
  pose proof (Znth_indep trees (i + 1) __default__Prod_Z_Z (0, 0) ltac:(lia))
    as Htree_next.
  rewrite Htree in Hposition, Hheight.
  rewrite Htree_next in Hposition_next.
  rewrite <- Hposition, <- Hheight, <- Hposition_next in PreH1.
  rewrite <- Hposition, <- Hheight in PreH2.
  rewrite <- Hposition.
  eapply PrefixFellingState_step_stand__prefix_transitions.
  - exact PreH10.
  - exact PreH12.
  - lia.
  - exact PreH16.
  - lia.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (PrefixFellingState_complete__final_general trees i occupied answer);
    auto; lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst n_pre.
  apply Spec_small_trees__final_small; assumption.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.
