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



Lemma proof_of_solver_partial_solve_wit_193_pure_split_goal_1 : solver_partial_solve_wit_193_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_193_pure_split_goal_2 : solver_partial_solve_wit_193_pure_split_goal_2.
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

Lemma proof_of_solver_partial_solve_wit_193_pure_split_goal_3 : solver_partial_solve_wit_193_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(assumption || lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_193_pure_split_goal_4 : solver_partial_solve_wit_193_pure_split_goal_4.
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

Lemma proof_of_solver_partial_solve_wit_193_pure_split_goal_5 : solver_partial_solve_wit_193_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_193_pure : solver_partial_solve_wit_193_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_193_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_193_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_193_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_193_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_193_pure_split_goal_5.
Qed.

Lemma proof_of_solver_partial_solve_wit_196_pure_split_goal_1 : solver_partial_solve_wit_196_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_196_pure_split_goal_2 : solver_partial_solve_wit_196_pure_split_goal_2.
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

Lemma proof_of_solver_partial_solve_wit_196_pure_split_goal_3 : solver_partial_solve_wit_196_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(assumption || lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_196_pure_split_goal_4 : solver_partial_solve_wit_196_pure_split_goal_4.
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

Lemma proof_of_solver_partial_solve_wit_196_pure_split_goal_5 : solver_partial_solve_wit_196_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_196_pure : solver_partial_solve_wit_196_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_196_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_196_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_196_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_196_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_196_pure_split_goal_5.
Qed.

Lemma proof_of_solver_partial_solve_wit_199_pure_split_goal_1 : solver_partial_solve_wit_199_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_199_pure_split_goal_2 : solver_partial_solve_wit_199_pure_split_goal_2.
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

Lemma proof_of_solver_partial_solve_wit_199_pure_split_goal_3 : solver_partial_solve_wit_199_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(assumption || lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_199_pure_split_goal_4 : solver_partial_solve_wit_199_pure_split_goal_4.
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

Lemma proof_of_solver_partial_solve_wit_199_pure_split_goal_5 : solver_partial_solve_wit_199_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_199_pure : solver_partial_solve_wit_199_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_199_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_199_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_199_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_199_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_199_pure_split_goal_5.
Qed.

Lemma proof_of_solver_partial_solve_wit_202_pure_split_goal_1 : solver_partial_solve_wit_202_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_202_pure_split_goal_2 : solver_partial_solve_wit_202_pure_split_goal_2.
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

Lemma proof_of_solver_partial_solve_wit_202_pure_split_goal_3 : solver_partial_solve_wit_202_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(assumption || lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_202_pure_split_goal_4 : solver_partial_solve_wit_202_pure_split_goal_4.
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

Lemma proof_of_solver_partial_solve_wit_202_pure_split_goal_5 : solver_partial_solve_wit_202_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : CompressedKeys _ _ _ |- _ => destruct H as [Hinc [_ _]]
  end.
  replace uniq with nvals by lia.
  exact Hinc.
Qed.

Lemma proof_of_solver_partial_solve_wit_202_pure : solver_partial_solve_wit_202_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_202_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_202_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_202_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_202_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_202_pure_split_goal_5.
Qed.

Lemma proof_of_solver_partial_solve_wit_204_pure_split_goal_1 : solver_partial_solve_wit_204_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_204_pure_split_goal_2 : solver_partial_solve_wit_204_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_204_pure_split_goal_3 : solver_partial_solve_wit_204_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_204_pure_split_goal_4 : solver_partial_solve_wit_204_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_204_pure : solver_partial_solve_wit_204_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_204_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_204_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_204_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_204_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_205_pure_split_goal_1 : solver_partial_solve_wit_205_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_205_pure_split_goal_2 : solver_partial_solve_wit_205_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_205_pure_split_goal_3 : solver_partial_solve_wit_205_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_205_pure_split_goal_4 : solver_partial_solve_wit_205_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_205_pure : solver_partial_solve_wit_205_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_205_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_205_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_205_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_205_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_206_pure_split_goal_1 : solver_partial_solve_wit_206_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_206_pure_split_goal_2 : solver_partial_solve_wit_206_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_206_pure_split_goal_3 : solver_partial_solve_wit_206_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_206_pure_split_goal_4 : solver_partial_solve_wit_206_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_206_pure : solver_partial_solve_wit_206_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_206_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_206_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_206_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_206_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_207_pure_split_goal_1 : solver_partial_solve_wit_207_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_207_pure_split_goal_2 : solver_partial_solve_wit_207_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_207_pure_split_goal_3 : solver_partial_solve_wit_207_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_207_pure_split_goal_4 : solver_partial_solve_wit_207_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_207_pure : solver_partial_solve_wit_207_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_207_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_207_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_207_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_207_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_208_pure_split_goal_1 : solver_partial_solve_wit_208_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_208_pure_split_goal_2 : solver_partial_solve_wit_208_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_208_pure_split_goal_3 : solver_partial_solve_wit_208_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_208_pure_split_goal_4 : solver_partial_solve_wit_208_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_208_pure : solver_partial_solve_wit_208_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_208_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_208_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_208_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_208_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_209_pure_split_goal_1 : solver_partial_solve_wit_209_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_209_pure_split_goal_2 : solver_partial_solve_wit_209_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_209_pure_split_goal_3 : solver_partial_solve_wit_209_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_209_pure_split_goal_4 : solver_partial_solve_wit_209_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_209_pure : solver_partial_solve_wit_209_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_209_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_209_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_209_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_209_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_210_pure_split_goal_1 : solver_partial_solve_wit_210_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_210_pure_split_goal_2 : solver_partial_solve_wit_210_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_210_pure_split_goal_3 : solver_partial_solve_wit_210_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_210_pure_split_goal_4 : solver_partial_solve_wit_210_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_210_pure : solver_partial_solve_wit_210_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_210_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_210_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_210_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_210_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_211_pure_split_goal_1 : solver_partial_solve_wit_211_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_211_pure_split_goal_2 : solver_partial_solve_wit_211_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_211_pure_split_goal_3 : solver_partial_solve_wit_211_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_211_pure_split_goal_4 : solver_partial_solve_wit_211_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_211_pure : solver_partial_solve_wit_211_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_211_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_211_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_211_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_211_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_212_pure_split_goal_1 : solver_partial_solve_wit_212_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_212_pure_split_goal_2 : solver_partial_solve_wit_212_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_212_pure_split_goal_3 : solver_partial_solve_wit_212_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_212_pure_split_goal_4 : solver_partial_solve_wit_212_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_212_pure : solver_partial_solve_wit_212_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_212_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_212_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_212_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_212_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_213_pure_split_goal_1 : solver_partial_solve_wit_213_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_213_pure_split_goal_2 : solver_partial_solve_wit_213_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_213_pure_split_goal_3 : solver_partial_solve_wit_213_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_213_pure_split_goal_4 : solver_partial_solve_wit_213_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_213_pure : solver_partial_solve_wit_213_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_213_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_213_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_213_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_213_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_214_pure_split_goal_1 : solver_partial_solve_wit_214_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_214_pure_split_goal_2 : solver_partial_solve_wit_214_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_214_pure_split_goal_3 : solver_partial_solve_wit_214_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_214_pure_split_goal_4 : solver_partial_solve_wit_214_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_214_pure : solver_partial_solve_wit_214_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_214_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_214_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_214_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_214_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_215_pure_split_goal_1 : solver_partial_solve_wit_215_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_215_pure_split_goal_2 : solver_partial_solve_wit_215_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_215_pure_split_goal_3 : solver_partial_solve_wit_215_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_215_pure_split_goal_4 : solver_partial_solve_wit_215_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_215_pure : solver_partial_solve_wit_215_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_215_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_215_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_215_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_215_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_216_pure_split_goal_1 : solver_partial_solve_wit_216_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_216_pure_split_goal_2 : solver_partial_solve_wit_216_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_216_pure_split_goal_3 : solver_partial_solve_wit_216_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_216_pure_split_goal_4 : solver_partial_solve_wit_216_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_216_pure : solver_partial_solve_wit_216_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_216_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_216_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_216_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_216_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_217_pure_split_goal_1 : solver_partial_solve_wit_217_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_217_pure_split_goal_2 : solver_partial_solve_wit_217_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_217_pure_split_goal_3 : solver_partial_solve_wit_217_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_217_pure_split_goal_4 : solver_partial_solve_wit_217_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_217_pure : solver_partial_solve_wit_217_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_217_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_217_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_217_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_217_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_218_pure_split_goal_1 : solver_partial_solve_wit_218_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_218_pure_split_goal_2 : solver_partial_solve_wit_218_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> _ |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hb
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_218_pure_split_goal_3 : solver_partial_solve_wit_218_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_218_pure_split_goal_4 : solver_partial_solve_wit_218_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  repeat match goal with
  | H : forall r : Z, (0 <= r /\ r < nvals + 1) -> _ |- _ =>
      pose proof (H k ltac:(lia)); clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_218_pure : solver_partial_solve_wit_218_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_218_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_218_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_218_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_218_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_219_pure_split_goal_1 : solver_partial_solve_wit_219_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_219_pure_split_goal_2 : solver_partial_solve_wit_219_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Znth_replace_Znth_Diff by lia.
  match goal with
  | H : forall k : Z, (0 <= k /\ k < i) -> (1 <= Znth k dp0_l 0 /\ Znth k dp0_l 0 <= n_pre) |- _ =>
      pose proof (H (i - 1) ltac:(lia)) as Hdp
  end.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_219_pure_split_goal_3 : solver_partial_solve_wit_219_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_219_pure_split_goal_4 : solver_partial_solve_wit_219_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k [Hk1 Hk2].
  repeat match goal with
  | H : forall k0 : Z, (0 <= k0 /\ k0 < nvals + 1) -> _ |- _ =>
      let Hb := fresh "Hbit" in pose proof (H k ltac:(lia)) as Hb; clear H
  end.
  tauto.
Qed.

Lemma proof_of_solver_partial_solve_wit_219_pure : solver_partial_solve_wit_219_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_solver_partial_solve_wit_219_pure_split_goal_1 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_219_pure_split_goal_2 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_219_pure_split_goal_3 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  - Goal_apply (proof_of_solver_partial_solve_wit_219_pure_split_goal_4 bitX_pre bit1_pre bit0_pre vals_pre dp0_pre c_pre n_pre a_pre values best0_prefix best1 best0 mX m1 m0 bitX_l bit1_l bit0_l dp0_l vals_l c_l i uniq nvals retval_2 retval_3 retval_4 retval_5 retval_6 bit_l1 bit_l1_2 retval ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

Lemma proof_of_solver_partial_solve_wit_220_pure_split_goal_1 : solver_partial_solve_wit_220_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH81 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_220_pure_split_goal_2 : solver_partial_solve_wit_220_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH81 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_220_pure_split_goal_3 : solver_partial_solve_wit_220_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH72 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_220_pure_split_goal_4 : solver_partial_solve_wit_220_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH72 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_220_pure : solver_partial_solve_wit_220_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_220_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_220_pure_split_goal_2.
  Goal_apply proof_of_solver_partial_solve_wit_220_pure_split_goal_3.
  Goal_apply proof_of_solver_partial_solve_wit_220_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_221_pure_split_goal_1 : solver_partial_solve_wit_221_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH81 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_221_pure_split_goal_2 : solver_partial_solve_wit_221_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH81 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_221_pure_split_goal_3 : solver_partial_solve_wit_221_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_221_pure_split_goal_4 : solver_partial_solve_wit_221_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_221_pure : solver_partial_solve_wit_221_pure.
Proof.
  aggressive_pre_process.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH81 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH81 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_222_pure_split_goal_1 : solver_partial_solve_wit_222_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH81 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_222_pure_split_goal_2 : solver_partial_solve_wit_222_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH81 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_222_pure_split_goal_3 : solver_partial_solve_wit_222_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH72 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_222_pure_split_goal_4 : solver_partial_solve_wit_222_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH72 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_222_pure : solver_partial_solve_wit_222_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_222_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_222_pure_split_goal_2.
  Goal_apply proof_of_solver_partial_solve_wit_222_pure_split_goal_3.
  Goal_apply proof_of_solver_partial_solve_wit_222_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_223_pure_split_goal_1 : solver_partial_solve_wit_223_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH81 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_223_pure_split_goal_2 : solver_partial_solve_wit_223_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH81 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_223_pure_split_goal_3 : solver_partial_solve_wit_223_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_223_pure_split_goal_4 : solver_partial_solve_wit_223_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_223_pure : solver_partial_solve_wit_223_pure.
Proof.
  aggressive_pre_process.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH81 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH81 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_224_pure_split_goal_1 : solver_partial_solve_wit_224_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH81 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_224_pure_split_goal_2 : solver_partial_solve_wit_224_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH81 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_224_pure_split_goal_3 : solver_partial_solve_wit_224_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH72 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_224_pure_split_goal_4 : solver_partial_solve_wit_224_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH72 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_224_pure : solver_partial_solve_wit_224_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_224_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_224_pure_split_goal_2.
  Goal_apply proof_of_solver_partial_solve_wit_224_pure_split_goal_3.
  Goal_apply proof_of_solver_partial_solve_wit_224_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_225_pure_split_goal_1 : solver_partial_solve_wit_225_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH81 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_225_pure_split_goal_2 : solver_partial_solve_wit_225_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH81 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_225_pure_split_goal_3 : solver_partial_solve_wit_225_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_225_pure_split_goal_4 : solver_partial_solve_wit_225_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_225_pure : solver_partial_solve_wit_225_pure.
Proof.
  aggressive_pre_process.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH81 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH81 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_226_pure_split_goal_1 : solver_partial_solve_wit_226_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH81 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_226_pure_split_goal_2 : solver_partial_solve_wit_226_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH81 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_226_pure_split_goal_3 : solver_partial_solve_wit_226_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH72 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_226_pure_split_goal_4 : solver_partial_solve_wit_226_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH72 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_226_pure : solver_partial_solve_wit_226_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_226_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_226_pure_split_goal_2.
  Goal_apply proof_of_solver_partial_solve_wit_226_pure_split_goal_3.
  Goal_apply proof_of_solver_partial_solve_wit_226_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_227_pure_split_goal_1 : solver_partial_solve_wit_227_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH79 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_227_pure_split_goal_2 : solver_partial_solve_wit_227_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH79 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_227_pure_split_goal_3 : solver_partial_solve_wit_227_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH70 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_227_pure_split_goal_4 : solver_partial_solve_wit_227_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH70 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_227_pure : solver_partial_solve_wit_227_pure.
Proof.
  aggressive_pre_process.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH79 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH79 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH70 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH70 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_228_pure_split_goal_1 : solver_partial_solve_wit_228_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH83 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_228_pure_split_goal_2 : solver_partial_solve_wit_228_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH83 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_228_pure_split_goal_3 : solver_partial_solve_wit_228_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH74 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_228_pure_split_goal_4 : solver_partial_solve_wit_228_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH74 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_228_pure : solver_partial_solve_wit_228_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_228_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_228_pure_split_goal_2.
  Goal_apply proof_of_solver_partial_solve_wit_228_pure_split_goal_3.
  Goal_apply proof_of_solver_partial_solve_wit_228_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_229_pure_split_goal_1 : solver_partial_solve_wit_229_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH83 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_229_pure_split_goal_2 : solver_partial_solve_wit_229_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH83 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_229_pure_split_goal_3 : solver_partial_solve_wit_229_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_229_pure_split_goal_4 : solver_partial_solve_wit_229_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_229_pure : solver_partial_solve_wit_229_pure.
Proof.
  aggressive_pre_process.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH83 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH83 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_230_pure_split_goal_1 : solver_partial_solve_wit_230_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH83 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_230_pure_split_goal_2 : solver_partial_solve_wit_230_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH83 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_230_pure_split_goal_3 : solver_partial_solve_wit_230_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH74 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_230_pure_split_goal_4 : solver_partial_solve_wit_230_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH74 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_230_pure : solver_partial_solve_wit_230_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_230_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_230_pure_split_goal_2.
  Goal_apply proof_of_solver_partial_solve_wit_230_pure_split_goal_3.
  Goal_apply proof_of_solver_partial_solve_wit_230_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_231_pure_split_goal_1 : solver_partial_solve_wit_231_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH83 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_231_pure_split_goal_2 : solver_partial_solve_wit_231_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH83 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_231_pure_split_goal_3 : solver_partial_solve_wit_231_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_231_pure_split_goal_4 : solver_partial_solve_wit_231_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_231_pure : solver_partial_solve_wit_231_pure.
Proof.
  aggressive_pre_process.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH83 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH83 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_232_pure_split_goal_1 : solver_partial_solve_wit_232_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH83 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_232_pure_split_goal_2 : solver_partial_solve_wit_232_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH83 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_232_pure_split_goal_3 : solver_partial_solve_wit_232_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH74 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_232_pure_split_goal_4 : solver_partial_solve_wit_232_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH74 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_232_pure : solver_partial_solve_wit_232_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_232_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_232_pure_split_goal_2.
  Goal_apply proof_of_solver_partial_solve_wit_232_pure_split_goal_3.
  Goal_apply proof_of_solver_partial_solve_wit_232_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_233_pure_split_goal_1 : solver_partial_solve_wit_233_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH83 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_233_pure_split_goal_2 : solver_partial_solve_wit_233_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH83 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_233_pure_split_goal_3 : solver_partial_solve_wit_233_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_233_pure_split_goal_4 : solver_partial_solve_wit_233_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_233_pure : solver_partial_solve_wit_233_pure.
Proof.
  aggressive_pre_process.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH83 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH83 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH74 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_234_pure_split_goal_1 : solver_partial_solve_wit_234_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH83 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_234_pure_split_goal_2 : solver_partial_solve_wit_234_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (retval + 1)) by lia;
    pose proof (PreH83 (i - 1) ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_partial_solve_wit_234_pure_split_goal_3 : solver_partial_solve_wit_234_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH74 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_234_pure_split_goal_4 : solver_partial_solve_wit_234_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(
    intros k Hk; pose proof (PreH74 k ltac:(lia)) as Hb; tauto).
Qed.

Lemma proof_of_solver_partial_solve_wit_234_pure : solver_partial_solve_wit_234_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_234_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_234_pure_split_goal_2.
  Goal_apply proof_of_solver_partial_solve_wit_234_pure_split_goal_3.
  Goal_apply proof_of_solver_partial_solve_wit_234_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_235_pure_split_goal_1 : solver_partial_solve_wit_235_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH81 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_235_pure_split_goal_2 : solver_partial_solve_wit_235_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
  specialize (PreH81 (i - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_235_pure_split_goal_3 : solver_partial_solve_wit_235_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_235_pure_split_goal_4 : solver_partial_solve_wit_235_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_235_pure : solver_partial_solve_wit_235_pure.
Proof.
  aggressive_pre_process.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH81 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    rewrite (Znth_replace_Znth_Diff 0 dp0_l i (i - 1) (0 + 1)) by lia.
    specialize (PreH81 (i - 1) ltac:(lia)).
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
  - dump_pre_spatial.
    intros k Hk.
    destruct (PreH72 k ltac:(lia)) as [[_ Hlo] Hhi].
    lia.
Qed.

