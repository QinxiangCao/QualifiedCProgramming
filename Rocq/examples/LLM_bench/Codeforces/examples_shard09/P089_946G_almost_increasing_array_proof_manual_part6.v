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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_lib.
Local Open Scope sac.



Lemma proof_of_solver_partial_solve_wit_109_pure : solver_partial_solve_wit_109_pure.
Proof.
  aggressive_pre_process.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    assumption.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_112_pure_split_goal_1 : solver_partial_solve_wit_112_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_112_pure_split_goal_2 : solver_partial_solve_wit_112_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_112_pure_split_goal_3 : solver_partial_solve_wit_112_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_112_pure_split_goal_4 : solver_partial_solve_wit_112_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_112_pure_split_goal_5 : solver_partial_solve_wit_112_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_112_pure : solver_partial_solve_wit_112_pure.
Proof.
  aggressive_pre_process.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    assumption.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_115_pure_split_goal_1 : solver_partial_solve_wit_115_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_115_pure_split_goal_2 : solver_partial_solve_wit_115_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_115_pure_split_goal_3 : solver_partial_solve_wit_115_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_115_pure_split_goal_4 : solver_partial_solve_wit_115_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_115_pure_split_goal_5 : solver_partial_solve_wit_115_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_115_pure : solver_partial_solve_wit_115_pure.
Proof.
  aggressive_pre_process.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    assumption.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_118_pure_split_goal_1 : solver_partial_solve_wit_118_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_118_pure_split_goal_2 : solver_partial_solve_wit_118_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_118_pure_split_goal_3 : solver_partial_solve_wit_118_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_118_pure_split_goal_4 : solver_partial_solve_wit_118_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_118_pure_split_goal_5 : solver_partial_solve_wit_118_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_118_pure : solver_partial_solve_wit_118_pure.
Proof.
  aggressive_pre_process.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    assumption.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_121_pure_split_goal_1 : solver_partial_solve_wit_121_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_121_pure_split_goal_2 : solver_partial_solve_wit_121_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_121_pure_split_goal_3 : solver_partial_solve_wit_121_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_121_pure_split_goal_4 : solver_partial_solve_wit_121_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_121_pure_split_goal_5 : solver_partial_solve_wit_121_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_121_pure : solver_partial_solve_wit_121_pure.
Proof.
  aggressive_pre_process.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    assumption.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_124_pure_split_goal_1 : solver_partial_solve_wit_124_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_124_pure_split_goal_2 : solver_partial_solve_wit_124_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_124_pure_split_goal_3 : solver_partial_solve_wit_124_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_124_pure_split_goal_4 : solver_partial_solve_wit_124_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_124_pure_split_goal_5 : solver_partial_solve_wit_124_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_124_pure : solver_partial_solve_wit_124_pure.
Proof.
  aggressive_pre_process.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    assumption.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_127_pure_split_goal_1 : solver_partial_solve_wit_127_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_127_pure_split_goal_2 : solver_partial_solve_wit_127_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_127_pure_split_goal_3 : solver_partial_solve_wit_127_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_127_pure_split_goal_4 : solver_partial_solve_wit_127_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_127_pure_split_goal_5 : solver_partial_solve_wit_127_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_127_pure : solver_partial_solve_wit_127_pure.
Proof.
  aggressive_pre_process.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    assumption.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_130_pure_split_goal_1 : solver_partial_solve_wit_130_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_130_pure_split_goal_2 : solver_partial_solve_wit_130_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_130_pure_split_goal_3 : solver_partial_solve_wit_130_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_130_pure_split_goal_4 : solver_partial_solve_wit_130_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_130_pure_split_goal_5 : solver_partial_solve_wit_130_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_130_pure : solver_partial_solve_wit_130_pure.
Proof.
  aggressive_pre_process.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    assumption.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_133_pure_split_goal_1 : solver_partial_solve_wit_133_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_133_pure_split_goal_2 : solver_partial_solve_wit_133_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_133_pure_split_goal_3 : solver_partial_solve_wit_133_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_133_pure_split_goal_4 : solver_partial_solve_wit_133_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_133_pure_split_goal_5 : solver_partial_solve_wit_133_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_133_pure : solver_partial_solve_wit_133_pure.
Proof.
  aggressive_pre_process.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    assumption.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_136_pure_split_goal_1 : solver_partial_solve_wit_136_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_136_pure_split_goal_2 : solver_partial_solve_wit_136_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_136_pure_split_goal_3 : solver_partial_solve_wit_136_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_136_pure_split_goal_4 : solver_partial_solve_wit_136_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_136_pure_split_goal_5 : solver_partial_solve_wit_136_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_136_pure : solver_partial_solve_wit_136_pure.
Proof.
  aggressive_pre_process.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    assumption.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_139_pure_split_goal_1 : solver_partial_solve_wit_139_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_139_pure_split_goal_2 : solver_partial_solve_wit_139_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_139_pure_split_goal_3 : solver_partial_solve_wit_139_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_139_pure_split_goal_4 : solver_partial_solve_wit_139_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_139_pure_split_goal_5 : solver_partial_solve_wit_139_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_139_pure : solver_partial_solve_wit_139_pure.
Proof.
  aggressive_pre_process.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    assumption.
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
    match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H (i - 1)) by lia end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact (proj1 (HMEM (i - 1) ltac:(lia))).
  -
    dump_pre_spatial.
    match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
    match goal with H : nvals = uniq |- _ => rewrite <- H end.
    exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_142_pure_split_goal_1 : solver_partial_solve_wit_142_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_142_pure_split_goal_2 : solver_partial_solve_wit_142_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_142_pure_split_goal_3 : solver_partial_solve_wit_142_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_142_pure_split_goal_4 : solver_partial_solve_wit_142_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_142_pure_split_goal_5 : solver_partial_solve_wit_142_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_142_pure : solver_partial_solve_wit_142_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; assumption)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ forall (k: Z) , (((0 <= k) /\ (k < (2 * n_pre ))) -> (((-2000000000) <= (Znth k vals_l 0)) /\ ((Znth k vals_l 0) <= 2000000000))) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_145_pure_split_goal_1 : solver_partial_solve_wit_145_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_145_pure_split_goal_2 : solver_partial_solve_wit_145_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_145_pure_split_goal_3 : solver_partial_solve_wit_145_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_145_pure_split_goal_4 : solver_partial_solve_wit_145_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_145_pure_split_goal_5 : solver_partial_solve_wit_145_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_145_pure : solver_partial_solve_wit_145_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; assumption)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ forall (k: Z) , (((0 <= k) /\ (k < (2 * n_pre ))) -> (((-2000000000) <= (Znth k vals_l 0)) /\ ((Znth k vals_l 0) <= 2000000000))) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_148_pure_split_goal_1 : solver_partial_solve_wit_148_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_148_pure_split_goal_2 : solver_partial_solve_wit_148_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_148_pure_split_goal_3 : solver_partial_solve_wit_148_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_148_pure_split_goal_4 : solver_partial_solve_wit_148_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_148_pure_split_goal_5 : solver_partial_solve_wit_148_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_148_pure : solver_partial_solve_wit_148_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; assumption)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ forall (k: Z) , (((0 <= k) /\ (k < (2 * n_pre ))) -> (((-2000000000) <= (Znth k vals_l 0)) /\ ((Znth k vals_l 0) <= 2000000000))) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_151_pure_split_goal_1 : solver_partial_solve_wit_151_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_151_pure_split_goal_2 : solver_partial_solve_wit_151_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_151_pure_split_goal_3 : solver_partial_solve_wit_151_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_151_pure_split_goal_4 : solver_partial_solve_wit_151_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_151_pure_split_goal_5 : solver_partial_solve_wit_151_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_151_pure : solver_partial_solve_wit_151_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; assumption)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ forall (k: Z) , (((0 <= k) /\ (k < (2 * n_pre ))) -> (((-2000000000) <= (Znth k vals_l 0)) /\ ((Znth k vals_l 0) <= 2000000000))) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_154_pure_split_goal_1 : solver_partial_solve_wit_154_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_154_pure_split_goal_2 : solver_partial_solve_wit_154_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_154_pure_split_goal_3 : solver_partial_solve_wit_154_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_154_pure_split_goal_4 : solver_partial_solve_wit_154_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_154_pure_split_goal_5 : solver_partial_solve_wit_154_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_154_pure : solver_partial_solve_wit_154_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; assumption)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ forall (k: Z) , (((0 <= k) /\ (k < (2 * n_pre ))) -> (((-2000000000) <= (Znth k vals_l 0)) /\ ((Znth k vals_l 0) <= 2000000000))) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> best0) ** (((( &( "best1" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_157_pure_split_goal_1 : solver_partial_solve_wit_157_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_157_pure_split_goal_2 : solver_partial_solve_wit_157_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_157_pure_split_goal_3 : solver_partial_solve_wit_157_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_157_pure_split_goal_4 : solver_partial_solve_wit_157_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_157_pure_split_goal_5 : solver_partial_solve_wit_157_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_157_pure : solver_partial_solve_wit_157_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; assumption)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ forall (k: Z) , (((0 <= k) /\ (k < (2 * n_pre ))) -> (((-2000000000) <= (Znth k vals_l 0)) /\ ((Znth k vals_l 0) <= 2000000000))) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_160_pure_split_goal_1 : solver_partial_solve_wit_160_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_160_pure_split_goal_2 : solver_partial_solve_wit_160_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_160_pure_split_goal_3 : solver_partial_solve_wit_160_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_160_pure_split_goal_4 : solver_partial_solve_wit_160_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_160_pure_split_goal_5 : solver_partial_solve_wit_160_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_160_pure : solver_partial_solve_wit_160_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; assumption)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ forall (k: Z) , (((0 <= k) /\ (k < (2 * n_pre ))) -> (((-2000000000) <= (Znth k vals_l 0)) /\ ((Znth k vals_l 0) <= 2000000000))) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_163_pure_split_goal_1 : solver_partial_solve_wit_163_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_163_pure_split_goal_2 : solver_partial_solve_wit_163_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_163_pure_split_goal_3 : solver_partial_solve_wit_163_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_163_pure_split_goal_4 : solver_partial_solve_wit_163_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_163_pure_split_goal_5 : solver_partial_solve_wit_163_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_163_pure : solver_partial_solve_wit_163_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; assumption)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ forall (k: Z) , (((0 <= k) /\ (k < (2 * n_pre ))) -> (((-2000000000) <= (Znth k vals_l 0)) /\ ((Znth k vals_l 0) <= 2000000000))) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_166_pure_split_goal_1 : solver_partial_solve_wit_166_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_166_pure_split_goal_2 : solver_partial_solve_wit_166_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_166_pure_split_goal_3 : solver_partial_solve_wit_166_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_166_pure_split_goal_4 : solver_partial_solve_wit_166_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_166_pure_split_goal_5 : solver_partial_solve_wit_166_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_166_pure : solver_partial_solve_wit_166_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; assumption)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ forall (k: Z) , (((0 <= k) /\ (k < (2 * n_pre ))) -> (((-2000000000) <= (Znth k vals_l 0)) /\ ((Znth k vals_l 0) <= 2000000000))) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_5 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_169_pure_split_goal_1 : solver_partial_solve_wit_169_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_169_pure_split_goal_2 : solver_partial_solve_wit_169_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_169_pure_split_goal_3 : solver_partial_solve_wit_169_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_169_pure_split_goal_4 : solver_partial_solve_wit_169_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_169_pure_split_goal_5 : solver_partial_solve_wit_169_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_169_pure : solver_partial_solve_wit_169_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; assumption)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ forall (k: Z) , (((0 <= k) /\ (k < (2 * n_pre ))) -> (((-2000000000) <= (Znth k vals_l 0)) /\ ((Znth k vals_l 0) <= 2000000000))) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((retval_3 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (retval_3 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_172_pure_split_goal_1 : solver_partial_solve_wit_172_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_172_pure_split_goal_2 : solver_partial_solve_wit_172_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_172_pure_split_goal_3 : solver_partial_solve_wit_172_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_172_pure_split_goal_4 : solver_partial_solve_wit_172_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end.
  match goal with H : CompressedKeys _ _ _ |- _ =>
    exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_172_pure_split_goal_5 : solver_partial_solve_wit_172_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace uniq with nvals by lia.
  match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_solver_partial_solve_wit_172_pure : solver_partial_solve_wit_172_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; assumption)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ forall (k: Z) , (((0 <= k) /\ (k < (2 * n_pre ))) -> (((-2000000000) <= (Znth k vals_l 0)) /\ ((Znth k vals_l 0) <= 2000000000))) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with HK : KeyPrefix _ _ _ |- _ => rewrite (HK (i - 1) ltac:(lia)) end; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 (proj1 (proj2 H) (i - 1) ltac:(lia))) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (MemberPrefix vals_l uniq (Znth (i - 1 ) c_l 0) ) ”)).
  - Goal_apply ((ltac:(dump_pre_spatial; replace uniq with nvals by lia; match goal with H : CompressedKeys _ _ _ |- _ => exact (proj1 H) end)) :
      ((Int64Array.full c_pre n_pre c_l ) ** ((IntArray.full bit1_pre (nvals + 1 ) bit_l1_2 ) ** ((IntArray.full bit0_pre (nvals + 1 ) bit_l1 ) ** ((IntArray.full dp0_pre n_pre (replace_Znth (i) ((0 + 1 )) (dp0_l)) ) ** ((IntArray.full bitX_pre (nvals + 1 ) bitX_l ) ** (((( &( "d1" ) )) # Int  |-> (retval_4 + 1 )) ** (((( &( "d0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "prev0" ) )) # Int  |-> retval_3) ** ((IntArray.full vals_pre (2 * n_pre ) vals_l ) ** (((( &( "r1" ) )) # Int  |-> retval_2) ** (((( &( "r0" ) )) # Int  |-> retval) ** (((( &( "a" ) )) # Ptr  |-> a_pre) ** (((( &( "n" ) )) # Int  |-> n_pre) ** (((( &( "c" ) )) # Ptr  |-> c_pre) ** (((( &( "dp0" ) )) # Ptr  |-> dp0_pre) ** (((( &( "vals" ) )) # Ptr  |-> vals_pre) ** (((( &( "bit0" ) )) # Ptr  |-> bit0_pre) ** (((( &( "bit1" ) )) # Ptr  |-> bit1_pre) ** (((( &( "bitX" ) )) # Ptr  |-> bitX_pre) ** (((( &( "nvals" ) )) # Int  |-> nvals) ** (((( &( "uniq" ) )) # Int  |-> uniq) ** (((( &( "i" ) )) # Int  |-> i) ** (((( &( "best0" ) )) # Int  |-> (0 + 1 )) ** (((( &( "best1" ) )) # Int  |-> best1) ** (((( &( "best0_prefix" ) )) # Int  |-> best0_prefix) ** ((IntArray.full a_pre n_pre values ) ** ((IntArray.seg_shape bit0_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bit1_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) ) ** ((IntArray.seg_shape bitX_pre (nvals + 1 ) ((2 * n_pre ) + 1 ) )))))))))))))))))))))))))))))
       |--
       “ (StrictIncPrefix vals_l uniq ) ”)).
Qed.

Lemma proof_of_solver_partial_solve_wit_175_pure_split_goal_1 : solver_partial_solve_wit_175_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_175_pure_split_goal_2 : solver_partial_solve_wit_175_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_175_pure_split_goal_3 : solver_partial_solve_wit_175_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(assumption || lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_175_pure_split_goal_4 : solver_partial_solve_wit_175_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_175_pure_split_goal_5 : solver_partial_solve_wit_175_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_175_pure : solver_partial_solve_wit_175_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_175_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_175_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_175_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_175_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_175_pure_split_goal_5 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_178_pure_split_goal_1 : solver_partial_solve_wit_178_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_178_pure_split_goal_2 : solver_partial_solve_wit_178_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_178_pure_split_goal_3 : solver_partial_solve_wit_178_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(assumption || lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_178_pure_split_goal_4 : solver_partial_solve_wit_178_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_178_pure_split_goal_5 : solver_partial_solve_wit_178_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_178_pure : solver_partial_solve_wit_178_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_178_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_178_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_178_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_178_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_178_pure_split_goal_5 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_181_pure_split_goal_1 : solver_partial_solve_wit_181_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_181_pure_split_goal_2 : solver_partial_solve_wit_181_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_181_pure_split_goal_3 : solver_partial_solve_wit_181_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(assumption || lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_181_pure_split_goal_4 : solver_partial_solve_wit_181_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_181_pure_split_goal_5 : solver_partial_solve_wit_181_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_181_pure : solver_partial_solve_wit_181_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_181_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_181_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_181_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_181_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_181_pure_split_goal_5 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_184_pure_split_goal_1 : solver_partial_solve_wit_184_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_184_pure_split_goal_2 : solver_partial_solve_wit_184_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_184_pure_split_goal_3 : solver_partial_solve_wit_184_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(assumption || lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_184_pure_split_goal_4 : solver_partial_solve_wit_184_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_184_pure_split_goal_5 : solver_partial_solve_wit_184_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_184_pure : solver_partial_solve_wit_184_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_184_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_184_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_184_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_184_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_184_pure_split_goal_5 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval retval_2 retval_3 retval_4 retval_5 bit_l1 bit_l1_2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_187_pure_split_goal_1 : solver_partial_solve_wit_187_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_187_pure_split_goal_2 : solver_partial_solve_wit_187_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_187_pure_split_goal_3 : solver_partial_solve_wit_187_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(assumption || lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_187_pure_split_goal_4 : solver_partial_solve_wit_187_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_187_pure_split_goal_5 : solver_partial_solve_wit_187_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_187_pure : solver_partial_solve_wit_187_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_187_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_187_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_187_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_187_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_187_pure_split_goal_5.
Qed.

Lemma proof_of_solver_partial_solve_wit_190_pure_split_goal_1 : solver_partial_solve_wit_190_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_190_pure_split_goal_2 : solver_partial_solve_wit_190_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_190_pure_split_goal_3 : solver_partial_solve_wit_190_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(assumption || lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_190_pure_split_goal_4 : solver_partial_solve_wit_190_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [_ [Hmem _]]
  end.
  match goal with
  | H : KeyPrefix _ _ _ |- _ => rewrite H by lia
  end.
  replace uniq with nvals by lia.
  apply (proj1 (Hmem (i - 1) ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_190_pure_split_goal_5 : solver_partial_solve_wit_190_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_190_pure : solver_partial_solve_wit_190_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_190_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_190_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_190_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_190_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_190_pure_split_goal_5.
Qed.
