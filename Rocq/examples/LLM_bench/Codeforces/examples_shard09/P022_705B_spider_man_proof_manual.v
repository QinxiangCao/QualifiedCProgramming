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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P022_705B_spider_man_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P022_705B_spider_man_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_lib.
Local Open Scope sac.

Lemma proof_of_next_parity_return_wit_1_split_goal_1 : next_parity_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NextParity.
  repeat split; try lia.
  apply land_one_eq_rem_two_nonnegative__parity_foundation.
  lia.
Qed.

Lemma proof_of_next_parity_return_wit_1 : next_parity_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_parity_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SpiderPrefixState, CycleMoveCount.
  rewrite Zsublist_nil by lia.
  simpl.
  dump_pre_spatial.
  split; [reflexivity |].
  split; [lia |].
  split; [reflexivity |].
  intros i Hi. rewrite Zlength_nil in Hi. exfalso. lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply IntArray.full_shape_to_seg_shape.
  apply IntArray.seg_shape_to_undef_seg.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_entail_wit_1_split_goal_spatial
      out_pre n_pre added_values PreH1 PreH2 PreH3 PreH4).
  - Goal_apply (proof_of_solver_entail_wit_1_split_goal_1
      out_pre n_pre added_values PreH1 PreH2 PreH3 PreH4).
  - Goal_apply (proof_of_solver_entail_wit_1_split_goal_2
      out_pre n_pre added_values PreH1 PreH2 PreH3 PreH4).
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply spider_prefix_state_extend__prefix_evolution with (par := par).
  - lia.
  - intros j Hj. specialize (PreH7 j ltac:(lia)). lia.
  - exact PreH2.
  - exact PreH10.
  - left. split; [reflexivity |].
    unfold NextParity in PreH2.
    pose proof (Z.rem_bound_pos
      (par + (Znth i added_values 0 - 1)) 2 ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_solver_entail_wit_2_1_split_goal_1
    n_pre added_values written_2 par i retval
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10).
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval.
  apply spider_prefix_state_extend__prefix_evolution with (par := par).
  - lia.
  - intros j Hj. specialize (PreH7 j ltac:(lia)). lia.
  - exact PreH2.
  - exact PreH10.
  - right. split; reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_solver_entail_wit_2_2_split_goal_1
    n_pre added_values written_2 par i retval
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10).
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Hsub : sublist 0 n_pre added_values = added_values).
  { apply sublist_self. exact PreH4. }
  rewrite Hsub in PreH8.
  assert (Hspec : Spec added_values written).
  {
    apply (spider_prefix_state_implies_spec__final_result
      added_values written par).
    - intros j Hj. specialize (PreH5 j ltac:(lia)). lia.
    - exact PreH8.
  }
  Exists written.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    cancel (Int64Array.full added_pre n_pre added_values).
    cancel (IntArray.full out_pre n_pre written).
    cancel emp.
  - dump_pre_spatial. exact Hspec.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SpiderPrefixState in PreH14.
  destruct PreH14 as [_ [[Hpar_nonneg Hpar_le] _]].
  dump_pre_spatial.
  exact Hpar_nonneg.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_2 : solver_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SpiderPrefixState in PreH14.
  destruct PreH14 as [_ [[Hpar_nonneg Hpar_le] _]].
  dump_pre_spatial.
  exact Hpar_le.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_2.
Qed.
