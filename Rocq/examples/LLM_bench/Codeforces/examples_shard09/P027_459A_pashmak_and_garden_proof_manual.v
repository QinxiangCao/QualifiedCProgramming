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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P027_459A_pashmak_and_garden_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P027_459A_pashmak_and_garden_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_lib.
Local Open Scope sac.

Lemma proof_of_iabs_return_wit_1_split_goal_1 : iabs_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_iabs_return_wit_1 : iabs_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_iabs_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_iabs_return_wit_2_split_goal_1 : iabs_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_iabs_return_wit_2 : iabs_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_iabs_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_3_split_goal_1 : solver_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia || nia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_3_split_goal_2 : solver_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia || nia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_1 : solver_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia || nia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia || nia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply no_completion_of_nonaxis_unequal_abs_diffs__final_results; eauto.
  congruence.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists x1_pre y2_pre x2_pre y1_pre.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    rewrite IntArray.full_unfold.
    repeat rewrite IntArray.seg_unfold.
    rewrite IntArray.seg_empty.
    replace (1 + 1) with 2 by lia.
    replace (2 + 1) with 3 by lia.
    replace (3 + 1) with 4 by lia.
    cancel (((out_pre + (0 * sizeof(INT)))) # Int |-> x1_pre).
    cancel (((out_pre + (1 * sizeof(INT)))) # Int |-> y2_pre).
    cancel (((out_pre + (2 * sizeof(INT)))) # Int |-> x2_pre).
    cancel (((out_pre + (3 * sizeof(INT)))) # Int |-> y1_pre).
    split_pure_spatial.
    + cancel emp.
    + dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial.
    + lia.
    + eapply completes_square_diagonal__final_results; eauto; congruence.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists x1_pre (y1_pre + retval) x2_pre (y2_pre + retval).
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    rewrite IntArray.full_unfold.
    repeat rewrite IntArray.seg_unfold.
    rewrite IntArray.seg_empty.
    replace (1 + 1) with 2 by lia.
    replace (2 + 1) with 3 by lia.
    replace (3 + 1) with 4 by lia.
    cancel (((out_pre + (0 * sizeof(INT)))) # Int |-> x1_pre).
    cancel (((out_pre + (1 * sizeof(INT)))) # Int |-> (y1_pre + retval)).
    cancel (((out_pre + (2 * sizeof(INT)))) # Int |-> x2_pre).
    cancel (((out_pre + (3 * sizeof(INT)))) # Int |-> (y2_pre + retval)).
    split_pure_spatial.
    + cancel emp.
    + dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial.
    + lia.
    + eapply completes_square_horizontal__final_results; eauto.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (x1_pre + retval) y1_pre (x2_pre + retval) y2_pre.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    rewrite IntArray.full_unfold.
    repeat rewrite IntArray.seg_unfold.
    rewrite IntArray.seg_empty.
    replace (1 + 1) with 2 by lia.
    replace (2 + 1) with 3 by lia.
    replace (3 + 1) with 4 by lia.
    cancel (((out_pre + (0 * sizeof(INT)))) # Int |-> (x1_pre + retval)).
    cancel (((out_pre + (1 * sizeof(INT)))) # Int |-> y1_pre).
    cancel (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre + retval)).
    cancel (((out_pre + (3 * sizeof(INT)))) # Int |-> y2_pre).
    split_pure_spatial.
    + cancel emp.
    + dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial.
    + lia.
    + eapply completes_square_vertical__final_results; eauto.
Qed.
