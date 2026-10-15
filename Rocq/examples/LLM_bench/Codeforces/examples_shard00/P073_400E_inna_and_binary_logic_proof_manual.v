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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P073_400E_inna_and_binary_logic_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P073_400E_inna_and_binary_logic_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P073_400E_inna_and_binary_logic_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P073_400E_inna_and_binary_logic_lib.
Local Open Scope sac.

Lemma proof_of_pull_safety_wit_8_split_goal_1 : pull_safety_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_8_split_goal_2 : pull_safety_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_8 : pull_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_8_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_9_split_goal_1 : pull_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_9_split_goal_2 : pull_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_9 : pull_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_16_split_goal_1 : pull_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_16_split_goal_2 : pull_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_16 : pull_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_16_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_17_split_goal_1 : pull_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_17_split_goal_2 : pull_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_17 : pull_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_22_split_goal_1 : pull_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_22_split_goal_2 : pull_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_22 : pull_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_23_split_goal_1 : pull_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_23_split_goal_2 : pull_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with H : P073BufferBounds _ _ _ _ _ |- _ =>
    destruct H as [Hcells Hlengths];
    pose proof (Hcells (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft;
    pose proof (Hcells (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright
  end.
  destruct Hleft as [? [? ?]].
  destruct Hright as [? [? ?]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_23 : pull_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_32_split_goal_1 : pull_safety_wit_32_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_other__pull_total_safety by lia.
  pose proof (total_bounds__pull_total_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1)) ltac:(lia) PreH32 ltac:(lia) ltac:(lia)) as Htotal.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_32_split_goal_2 : pull_safety_wit_32_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_other__pull_total_safety by lia.
  pose proof (total_bounds__pull_total_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1)) ltac:(lia) PreH32 ltac:(lia) ltac:(lia)) as Htotal.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_32 : pull_safety_wit_32.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_32_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_32_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_33_split_goal_1 : pull_safety_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_distinct__pull_product_safety by lia.
  destruct PreH32 as [Hbuffers Hlengths].
  pose proof (Hbuffers (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft.
  pose proof (Hbuffers (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright.
  nia.
Qed.

Lemma proof_of_pull_safety_wit_33_split_goal_2 : pull_safety_wit_33_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_distinct__pull_product_safety by lia.
  destruct PreH32 as [Hbuffers Hlengths].
  pose proof (Hbuffers (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft.
  pose proof (Hbuffers (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright.
  nia.
Qed.

Lemma proof_of_pull_safety_wit_33 : pull_safety_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_33_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_33_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_34_split_goal_1 : pull_safety_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (P073_count_pair_bound__pull_count_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1))
    (conj PreH16 PreH17) PreH32 (conj PreH5 PreH6) (conj PreH7 PreH8)) as HB.
  int_auto.
Qed.

Lemma proof_of_pull_safety_wit_34_split_goal_2 : pull_safety_wit_34_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (P073_count_pair_bound__pull_count_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1))
    (conj PreH16 PreH17) PreH32 (conj PreH5 PreH6) (conj PreH7 PreH8)) as HB.
  int_auto.
Qed.

Lemma proof_of_pull_safety_wit_34 : pull_safety_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_34_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_34_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_39_split_goal_1 : pull_safety_wit_39_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_other__pull_total_safety by lia.
  pose proof (total_bounds__pull_total_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1)) ltac:(lia) PreH32 ltac:(lia) ltac:(lia)) as Htotal.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_39_split_goal_2 : pull_safety_wit_39_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_other__pull_total_safety by lia.
  pose proof (total_bounds__pull_total_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1)) ltac:(lia) PreH32 ltac:(lia) ltac:(lia)) as Htotal.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_39 : pull_safety_wit_39.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_39_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_39_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_40_split_goal_1 : pull_safety_wit_40_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_distinct__pull_product_safety by lia.
  destruct PreH32 as [Hbuffers Hlengths].
  pose proof (Hbuffers (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft.
  pose proof (Hbuffers (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright.
  nia.
Qed.

Lemma proof_of_pull_safety_wit_40_split_goal_2 : pull_safety_wit_40_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_distinct__pull_product_safety by lia.
  destruct PreH32 as [Hbuffers Hlengths].
  pose proof (Hbuffers (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft.
  pose proof (Hbuffers (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright.
  nia.
Qed.

Lemma proof_of_pull_safety_wit_40 : pull_safety_wit_40.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_40_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_40_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_41_split_goal_1 : pull_safety_wit_41_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (P073_count_pair_bound__pull_count_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1))
    (conj PreH16 PreH17) PreH32 (conj PreH5 PreH6) (conj PreH7 PreH8)) as HB.
  int_auto.
Qed.

Lemma proof_of_pull_safety_wit_41_split_goal_2 : pull_safety_wit_41_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (P073_count_pair_bound__pull_count_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1))
    (conj PreH16 PreH17) PreH32 (conj PreH5 PreH6) (conj PreH7 PreH8)) as HB.
  int_auto.
Qed.

Lemma proof_of_pull_safety_wit_41 : pull_safety_wit_41.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_41_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_41_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_46_split_goal_1 : pull_safety_wit_46_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_other__pull_total_safety by lia.
  pose proof (total_bounds__pull_total_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1)) ltac:(lia) PreH32 ltac:(lia) ltac:(lia)) as Htotal.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_46_split_goal_2 : pull_safety_wit_46_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_other__pull_total_safety by lia.
  pose proof (total_bounds__pull_total_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1)) ltac:(lia) PreH32 ltac:(lia) ltac:(lia)) as Htotal.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_46 : pull_safety_wit_46.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_46_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_46_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_47_split_goal_1 : pull_safety_wit_47_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_distinct__pull_product_safety by lia.
  destruct PreH32 as [Hbuffers Hlengths].
  pose proof (Hbuffers (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft.
  pose proof (Hbuffers (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright.
  nia.
Qed.

Lemma proof_of_pull_safety_wit_47_split_goal_2 : pull_safety_wit_47_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_distinct__pull_product_safety by lia.
  destruct PreH32 as [Hbuffers Hlengths].
  pose proof (Hbuffers (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft.
  pose proof (Hbuffers (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright.
  nia.
Qed.

Lemma proof_of_pull_safety_wit_47 : pull_safety_wit_47.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_47_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_47_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_48_split_goal_1 : pull_safety_wit_48_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (P073_count_pair_bound__pull_count_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1))
    (conj PreH16 PreH17) PreH32 (conj PreH5 PreH6) (conj PreH7 PreH8)) as HB.
  int_auto.
Qed.

Lemma proof_of_pull_safety_wit_48_split_goal_2 : pull_safety_wit_48_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (P073_count_pair_bound__pull_count_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1))
    (conj PreH16 PreH17) PreH32 (conj PreH5 PreH6) (conj PreH7 PreH8)) as HB.
  int_auto.
Qed.

Lemma proof_of_pull_safety_wit_48 : pull_safety_wit_48.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_48_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_48_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_53_split_goal_1 : pull_safety_wit_53_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_other__pull_total_safety by lia.
  pose proof (total_bounds__pull_total_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1)) ltac:(lia) PreH32 ltac:(lia) ltac:(lia)) as Htotal.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_53_split_goal_2 : pull_safety_wit_53_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_other__pull_total_safety by lia.
  pose proof (total_bounds__pull_total_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1)) ltac:(lia) PreH32 ltac:(lia) ltac:(lia)) as Htotal.
  lia.
Qed.

Lemma proof_of_pull_safety_wit_53 : pull_safety_wit_53.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_53_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_53_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_54_split_goal_1 : pull_safety_wit_54_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_distinct__pull_product_safety by lia.
  destruct PreH32 as [Hbuffers Hlengths].
  pose proof (Hbuffers (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft.
  pose proof (Hbuffers (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright.
  nia.
Qed.

Lemma proof_of_pull_safety_wit_54_split_goal_2 : pull_safety_wit_54_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  repeat rewrite Znth_replace_distinct__pull_product_safety by lia.
  destruct PreH32 as [Hbuffers Hlengths].
  pose proof (Hbuffers (b * 4 * N + v_pre * 2) ltac:(lia)) as Hleft.
  pose proof (Hbuffers (b * 4 * N + (v_pre * 2 + 1)) ltac:(lia)) as Hright.
  nia.
Qed.

Lemma proof_of_pull_safety_wit_54 : pull_safety_wit_54.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_54_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_54_split_goal_2.
Qed.

Lemma proof_of_pull_safety_wit_55_split_goal_1 : pull_safety_wit_55_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (P073_count_pair_bound__pull_count_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1))
    (conj PreH16 PreH17) PreH32 (conj PreH5 PreH6) (conj PreH7 PreH8)) as HB.
  int_auto.
Qed.

Lemma proof_of_pull_safety_wit_55_split_goal_2 : pull_safety_wit_55_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (P073_count_pair_bound__pull_count_safety N pr1 su1 ct1 ln
    (b*4*N+v_pre*2) (b*4*N+(v_pre*2+1))
    (conj PreH16 PreH17) PreH32 (conj PreH5 PreH6) (conj PreH7 PreH8)) as HB.
  int_auto.
Qed.

Lemma proof_of_pull_safety_wit_55 : pull_safety_wit_55.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_safety_wit_55_split_goal_1.
  - Goal_apply proof_of_pull_safety_wit_55_split_goal_2.
Qed.

Lemma proof_of_pull_entail_wit_1_split_goal_1 : pull_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodeFrame. intros. repeat split; reflexivity.
Qed.

Lemma proof_of_pull_entail_wit_1_split_goal_2 : pull_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodePrefix. intros. lia.
Qed.

Lemma proof_of_pull_entail_wit_1 : pull_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_pull_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_pull_entail_wit_2_split_goal_1 : pull_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_pull_entail_wit_2_split_goal_2 : pull_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_pull_entail_wit_2_split_goal_3 : pull_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_pull_entail_wit_2 : pull_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_pull_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_pull_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_pull_entail_wit_3_1_split_goal_1 : pull_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v_pre*2) with (2*v_pre) in * by lia.
  repeat rewrite P073Packed_replace__pull_merge by nia.
  eapply P073Buffer_replace__pull_merge with (b:=b) (xs:=xs++ys); try lia.
  - rewrite Zlength_app; lia.
  - exact PreH32.
  - eapply P073Summary_concat__pull_merge.
    + apply PreH28; lia.
    + apply PreH29; lia.
    + left; split; lia.
    + left; split; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_1_split_goal_2 : pull_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodeFrame in *.
  intros d w Hd Hw Hframe.
  assert (Hne : b*4*N+v_pre <> d*4*N+w).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH31; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_1_split_goal_3 : pull_entail_wit_3_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v_pre*2) with (2*v_pre) in * by lia.
  repeat rewrite P073Packed_replace__pull_merge by nia.
  eapply P073Node_extend__pull_merge; try lia; try eassumption.
  eapply P073Summary_concat__pull_merge.
  - apply PreH28; lia.
  - apply PreH29; lia.
  - left; split; lia.
  - left; split; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_1_split_goal_4 : pull_entail_wit_3_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodePrefix in *.
  intros d Hd.
  assert (Hne : b*4*N+v_pre <> d*4*N+(2*v_pre+1)).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH29; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_1_split_goal_5 : pull_entail_wit_3_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodePrefix in *.
  intros d Hd.
  assert (Hne : b*4*N+v_pre <> d*4*N+(2*v_pre)).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH28; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_1 : pull_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_pull_entail_wit_3_1_split_goal_2.
  - Goal_apply proof_of_pull_entail_wit_3_1_split_goal_3.
  - Goal_apply proof_of_pull_entail_wit_3_1_split_goal_4.
  - Goal_apply proof_of_pull_entail_wit_3_1_split_goal_5.
Qed.

Lemma proof_of_pull_entail_wit_3_2_split_goal_1 : pull_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v_pre*2) with (2*v_pre) in * by lia.
  repeat rewrite P073Packed_replace__pull_merge by nia.
  eapply P073Buffer_replace__pull_merge with (b:=b) (xs:=xs++ys); try lia.
  - rewrite Zlength_app; lia.
  - exact PreH32.
  - eapply P073Summary_concat__pull_merge.
    + apply PreH28; lia.
    + apply PreH29; lia.
    + first [left; split; lia | right; split; lia].
    + first [left; split; lia | right; split; lia].
Qed.

Lemma proof_of_pull_entail_wit_3_2_split_goal_2 : pull_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodeFrame in *.
  intros d w Hd Hw Hframe.
  assert (Hne : b*4*N+v_pre <> d*4*N+w).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH31; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_2_split_goal_3 : pull_entail_wit_3_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v_pre*2) with (2*v_pre) in * by lia.
  repeat rewrite P073Packed_replace__pull_merge by nia.
  eapply P073Node_extend__pull_merge; try lia; try eassumption.
  eapply P073Summary_concat__pull_merge.
  - apply PreH28; lia.
  - apply PreH29; lia.
  - first [left; split; lia | right; split; lia].
  - first [left; split; lia | right; split; lia].
Qed.

Lemma proof_of_pull_entail_wit_3_2_split_goal_4 : pull_entail_wit_3_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodePrefix in *.
  intros d Hd.
  assert (Hne : b*4*N+v_pre <> d*4*N+(2*v_pre+1)).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH29; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_2_split_goal_5 : pull_entail_wit_3_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodePrefix in *.
  intros d Hd.
  assert (Hne : b*4*N+v_pre <> d*4*N+(2*v_pre)).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH28; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_2 : pull_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_entail_wit_3_2_split_goal_1.
  - Goal_apply proof_of_pull_entail_wit_3_2_split_goal_2.
  - Goal_apply proof_of_pull_entail_wit_3_2_split_goal_3.
  - Goal_apply proof_of_pull_entail_wit_3_2_split_goal_4.
  - Goal_apply proof_of_pull_entail_wit_3_2_split_goal_5.
Qed.

Lemma proof_of_pull_entail_wit_3_3_split_goal_1 : pull_entail_wit_3_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v_pre*2) with (2*v_pre) in * by lia.
  repeat rewrite P073Packed_replace__pull_merge by nia.
  eapply P073Buffer_replace__pull_merge with (b:=b) (xs:=xs++ys); try lia.
  - rewrite Zlength_app; lia.
  - exact PreH32.
  - eapply P073Summary_concat__pull_merge.
    + apply PreH28; lia.
    + apply PreH29; lia.
    + first [left; split; lia | right; split; lia].
    + first [left; split; lia | right; split; lia].
Qed.

Lemma proof_of_pull_entail_wit_3_3_split_goal_2 : pull_entail_wit_3_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodeFrame in *.
  intros d w Hd Hw Hframe.
  assert (Hne : b*4*N+v_pre <> d*4*N+w).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH31; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_3_split_goal_3 : pull_entail_wit_3_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v_pre*2) with (2*v_pre) in * by lia.
  repeat rewrite P073Packed_replace__pull_merge by nia.
  eapply P073Node_extend__pull_merge; try lia; try eassumption.
  eapply P073Summary_concat__pull_merge.
  - apply PreH28; lia.
  - apply PreH29; lia.
  - first [left; split; lia | right; split; lia].
  - first [left; split; lia | right; split; lia].
Qed.

Lemma proof_of_pull_entail_wit_3_3_split_goal_4 : pull_entail_wit_3_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodePrefix in *.
  intros d Hd.
  assert (Hne : b*4*N+v_pre <> d*4*N+(2*v_pre+1)).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH29; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_3_split_goal_5 : pull_entail_wit_3_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodePrefix in *.
  intros d Hd.
  assert (Hne : b*4*N+v_pre <> d*4*N+(2*v_pre)).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH28; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_3 : pull_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_entail_wit_3_3_split_goal_1.
  - Goal_apply proof_of_pull_entail_wit_3_3_split_goal_2.
  - Goal_apply proof_of_pull_entail_wit_3_3_split_goal_3.
  - Goal_apply proof_of_pull_entail_wit_3_3_split_goal_4.
  - Goal_apply proof_of_pull_entail_wit_3_3_split_goal_5.
Qed.

Lemma proof_of_pull_entail_wit_3_4_split_goal_1 : pull_entail_wit_3_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v_pre*2) with (2*v_pre) in * by lia.
  repeat rewrite P073Packed_replace__pull_merge by nia.
  eapply P073Buffer_replace__pull_merge with (b:=b) (xs:=xs++ys); try lia.
  - rewrite Zlength_app; lia.
  - exact PreH32.
  - eapply P073Summary_concat__pull_merge.
    + apply PreH28; lia.
    + apply PreH29; lia.
    + first [left; split; lia | right; split; lia].
    + first [left; split; lia | right; split; lia].
Qed.

Lemma proof_of_pull_entail_wit_3_4_split_goal_2 : pull_entail_wit_3_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodeFrame in *.
  intros d w Hd Hw Hframe.
  assert (Hne : b*4*N+v_pre <> d*4*N+w).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH31; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_4_split_goal_3 : pull_entail_wit_3_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v_pre*2) with (2*v_pre) in * by lia.
  repeat rewrite P073Packed_replace__pull_merge by nia.
  eapply P073Node_extend__pull_merge; try lia; try eassumption.
  eapply P073Summary_concat__pull_merge.
  - apply PreH28; lia.
  - apply PreH29; lia.
  - first [left; split; lia | right; split; lia].
  - first [left; split; lia | right; split; lia].
Qed.

Lemma proof_of_pull_entail_wit_3_4_split_goal_4 : pull_entail_wit_3_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodePrefix in *.
  intros d Hd.
  assert (Hne : b*4*N+v_pre <> d*4*N+(2*v_pre+1)).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH29; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_4_split_goal_5 : pull_entail_wit_3_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodePrefix in *.
  intros d Hd.
  assert (Hne : b*4*N+v_pre <> d*4*N+(2*v_pre)).
  { intro Heq. apply P073Packed_injective__pull_merge in Heq; lia. }
  repeat rewrite P073Packed_replace__pull_merge by nia.
  apply PreH28; lia.
Qed.

Lemma proof_of_pull_entail_wit_3_4 : pull_entail_wit_3_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_entail_wit_3_4_split_goal_1.
  - Goal_apply proof_of_pull_entail_wit_3_4_split_goal_2.
  - Goal_apply proof_of_pull_entail_wit_3_4_split_goal_3.
  - Goal_apply proof_of_pull_entail_wit_3_4_split_goal_4.
  - Goal_apply proof_of_pull_entail_wit_3_4_split_goal_5.
Qed.

Lemma proof_of_pull_return_wit_1_split_goal_1 : pull_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (b = 17) by lia. subst b. assumption.
Qed.

Lemma proof_of_pull_return_wit_1_split_goal_2 : pull_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (b = 17) by lia. subst b. assumption.
Qed.

Lemma proof_of_pull_return_wit_1 : pull_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pull_return_wit_1_split_goal_1.
  - Goal_apply proof_of_pull_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_1 : build_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073BufferBounds in *.
  destruct PreH14 as [Hbits Hln]. split; [exact Hbits|].
  intros k Hk. destruct (Z.eq_dec k v_pre) as [->|Hne].
  - rewrite Znth_replace_Znth_Same by lia. lia.
  - rewrite Znth_replace_Znth_Diff by lia. apply Hln; exact Hk.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_2 : build_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodeFrame. intros; repeat split; reflexivity.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_3 : build_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodePrefix. intros; lia.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_4 : build_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH11; assumption.
Qed.

Lemma proof_of_build_entail_wit_1 : build_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_build_entail_wit_2_1_split_goal_1 : build_entail_wit_2_1_split_goal_1.
Proof. Abort.

Lemma proof_of_build_entail_wit_2_1_split_goal_2 : build_entail_wit_2_1_split_goal_2.
Proof. Abort.

Lemma proof_of_build_entail_wit_2_1_split_goal_3 : build_entail_wit_2_1_split_goal_3.
Proof. Abort.

Lemma proof_of_build_entail_wit_2_1_split_goal_4 : build_entail_wit_2_1_split_goal_4.
Proof. Abort.

Lemma proof_of_build_entail_wit_2_1 : build_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (IntArray.full_Zlength PP (68*N) (replace_Znth (b*4*N+v_pre) 1 pr1_2)).
  Intros_p Hpr.
  prop_apply_p (IntArray.full_Zlength SP (68*N) (replace_Znth (b*4*N+v_pre) 1 su1_2)).
  Intros_p Hsu.
  prop_apply_p (Int64Array.full_Zlength CP (68*N) (replace_Znth (b*4*N+v_pre) 1 ct1_2)).
  Intros_p Hct.
  rewrite Zlength_replace_Znth in Hpr, Hsu, Hct.
  assert (Hsummary : P073Summary b (sublist l_pre r_pre xs) 1 1 1).
  { rewrite PreH7, (sublist_single 0) by lia.
    rewrite P073Bit_guard__build_leaf in PreH20.
    pose proof (P073Singleton_summary__build_leaf b (Znth l_pre xs 0)) as Hsingle.
    destruct (Z.testbit (Znth l_pre xs 0) b); simpl in *; [exact Hsingle|contradiction]. }
  assert (Hprefix : P073NodePrefix N v_pre (b+1) (sublist l_pre r_pre xs)
    (replace_Znth (b*4*N+v_pre) 1 pr1_2) (replace_Znth (b*4*N+v_pre) 1 su1_2)
    (replace_Znth (b*4*N+v_pre) 1 ct1_2)).
  { apply P073Written_prefix__build_leaf; try assumption; lia. }
  assert (Hframe : P073NodeFrame N v_pre (b+1) pr su ct
    (replace_Znth (b*4*N+v_pre) 1 pr1_2) (replace_Znth (b*4*N+v_pre) 1 su1_2)
    (replace_Znth (b*4*N+v_pre) 1 ct1_2)).
  { apply P073Leaf_frame__build_leaf; try assumption; lia. }
  assert (Hbounds : P073BufferBounds N
    (replace_Znth (b*4*N+v_pre) 1 pr1_2) (replace_Znth (b*4*N+v_pre) 1 su1_2)
    (replace_Znth (b*4*N+v_pre) 1 ct1_2) (replace_Znth v_pre (r_pre-l_pre) ln)).
  { apply P073Written_bounds__build_leaf; try assumption. apply PreH11; assumption. }
  Exists (replace_Znth (b*4*N+v_pre) 1 pr1_2)
    (replace_Znth (b*4*N+v_pre) 1 su1_2) (replace_Znth (b*4*N+v_pre) 1 ct1_2).
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try nia.
Qed.

Lemma proof_of_build_entail_wit_2_2_split_goal_1 : build_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodeFrame in *.
  intros j w Hj Hw Hunchanged. apply PreH18; try assumption.
  destruct Hunchanged; [left|right]; lia.
Qed.

Lemma proof_of_build_entail_wit_2_2_split_goal_2 : build_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst r_pre.
  unfold P073NodePrefix in *. intros j Hj.
  destruct (Z.eq_dec j b) as [->|Hne].
  - pose proof (PreH18 b v_pre ltac:(lia) ltac:(lia) (or_intror (Z.le_refl b))) as Hframe.
    pose proof (proj2 (PreH16 v_pre l_pre (l_pre+1) (P073Desc_here _ _ _)) b ltac:(lia)) as Hzero.
    destruct Hframe as [Hp [Hs Hc]]. destruct Hzero as [Hpr [Hsu Hct]].
    rewrite Hp, Hs, Hc, Hpr, Hsu, Hct.
    rewrite (sublist_single 0) by lia.
    rewrite P073Bit_guard__build_leaf in PreH20.
    pose proof (P073Singleton_summary__build_leaf b (Znth l_pre xs 0)) as Hsingle.
    rewrite PreH20 in Hsingle. exact Hsingle.
  - apply PreH17. lia.
Qed.

Lemma proof_of_build_entail_wit_2_2_split_goal_3 : build_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_build_entail_wit_2_2 : build_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_build_return_wit_1_split_goal_1 : build_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073OutsideTree. split.
  - intros w Hw Houtside.
    assert (w <> v_pre) as Hne.
    { intro H; subst w. apply (Houtside l_pre (l_pre+1)); constructor. }
    rewrite Znth_replace_Znth_Diff by lia. reflexivity.
  - intros w j Hw Hj Houtside.
    apply PreH18; try assumption.
    left. intro H; subst w.
    apply (Houtside l_pre (l_pre+1)); constructor.
Qed.

Lemma proof_of_build_return_wit_1_split_goal_2 : build_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073Tree. intros w lo hi Hd.
  inversion Hd; subst; try lia.
  split.
  - rewrite Znth_replace_Znth_Same by lia. reflexivity.
  - intros j Hj. apply PreH17. lia.
Qed.

Lemma proof_of_build_return_wit_1 : build_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_return_wit_1_split_goal_1.
  - Goal_apply proof_of_build_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_build_return_wit_2_split_goal_1 : build_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  replace (v_pre*2) with (2*v_pre) in * by ring.
  eapply P073Outside_parent__build_recursive; eauto; lia.
Qed.

Lemma proof_of_build_return_wit_2_split_goal_2 : build_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  replace (v_pre*2) with (2*v_pre) in * by ring.
  eapply P073Tree_frames__build_recursive; try eassumption; try lia.
  - eapply P073Root_length__build_recursive; eauto; lia.
  - eapply P073Left_tree__build_recursive; eauto; lia.
Qed.

Lemma proof_of_build_return_wit_2 : build_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_return_wit_2_split_goal_1.
  - Goal_apply proof_of_build_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_1 : build_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH22 (2*v_pre) l_pre ((l_pre+r_pre)/2)
    (P073Desc_left v_pre l_pre r_pre (2*v_pre) l_pre ((l_pre+r_pre)/2)
      ltac:(lia) (P073Desc_here _ _ _))). lia.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_2 : build_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Mid_sublist__build_recursive l_pre r_pre ltac:(lia) ltac:(lia)) as [Hmid Hquot].
  rewrite Hquot; lia.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_3 : build_partial_solve_wit_6_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Mid_sublist__build_recursive l_pre r_pre ltac:(lia) ltac:(lia)) as [Hmid Hquot].
  rewrite Hquot; lia.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_4 : build_partial_solve_wit_6_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_5 : build_partial_solve_wit_6_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  replace (v_pre*2) with (2*v_pre) by ring.
  apply (proj1 (P073Children_layout__build_recursive N v_pre l_pre r_pre ltac:(lia) PreH22)).
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_6 : build_partial_solve_wit_6_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  replace (v_pre*2) with (2*v_pre) by ring.
  apply (proj1 (P073Children_zero__build_recursive N v_pre l_pre r_pre pr su ct ln ltac:(lia) ltac:(lia) PreH20 PreH22 PreH23)).
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure_split_goal_7 : build_partial_solve_wit_6_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct PreH24 as [HA HL]. split; [exact HA|].
  intros k Hk; destruct (Z.eq_dec v_pre k) as [E|E].
  - subst k; rewrite Znth_replace_Znth_Same by lia; lia.
  - rewrite Znth_replace_Znth_Diff by lia; apply HL; assumption.
Qed.

Lemma proof_of_build_partial_solve_wit_6_pure : build_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_build_partial_solve_wit_6_pure_split_goal_2.
  - Goal_apply proof_of_build_partial_solve_wit_6_pure_split_goal_3.
  - Goal_apply proof_of_build_partial_solve_wit_6_pure_split_goal_4.
  - Goal_apply proof_of_build_partial_solve_wit_6_pure_split_goal_5.
  - Goal_apply proof_of_build_partial_solve_wit_6_pure_split_goal_6.
  - Goal_apply proof_of_build_partial_solve_wit_6_pure_split_goal_7.
Qed.

Lemma proof_of_build_partial_solve_wit_7_pure_split_goal_1 : build_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH25 (2*v_pre+1) ((l_pre+r_pre)/2) r_pre
    (P073Desc_right v_pre l_pre r_pre (2*v_pre+1) ((l_pre+r_pre)/2) r_pre
      ltac:(lia) (P073Desc_here _ _ _))). lia.
Qed.

Lemma proof_of_build_partial_solve_wit_7_pure_split_goal_2 : build_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Mid_sublist__build_recursive l_pre r_pre ltac:(lia) ltac:(lia)) as [Hmid Hquot].
  rewrite Hquot; lia.
Qed.

Lemma proof_of_build_partial_solve_wit_7_pure_split_goal_3 : build_partial_solve_wit_7_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Mid_sublist__build_recursive l_pre r_pre ltac:(lia) ltac:(lia)) as [Hmid Hquot].
  rewrite Hquot; lia.
Qed.

Lemma proof_of_build_partial_solve_wit_7_pure_split_goal_4 : build_partial_solve_wit_7_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (IntArray.full_Zlength LP (4*N) ln1).
  Intros_p Hlen. dump_pre_spatial. exact Hlen.
Qed.

Lemma proof_of_build_partial_solve_wit_7_pure_split_goal_5 : build_partial_solve_wit_7_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  replace (v_pre*2) with (2*v_pre) by ring.
  apply (proj2 (P073Children_layout__build_recursive N v_pre l_pre r_pre ltac:(lia) PreH25)).
Qed.

Lemma proof_of_build_partial_solve_wit_7_pure_split_goal_6 : build_partial_solve_wit_7_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg in * by lia.
  replace (v_pre*2) with (2*v_pre) in * by ring.
  eapply P073Right_zero__build_recursive; [lia|lia|exact PreH25| |exact PreH12].
  apply (proj2 (P073Children_zero__build_recursive N v_pre l_pre r_pre pr su ct ln ltac:(lia) ltac:(lia) PreH23 PreH25 PreH26)).
Qed.

Lemma proof_of_build_partial_solve_wit_7_pure : build_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_build_partial_solve_wit_7_pure_split_goal_2.
  - Goal_apply proof_of_build_partial_solve_wit_7_pure_split_goal_3.
  - Goal_apply proof_of_build_partial_solve_wit_7_pure_split_goal_4.
  - Goal_apply proof_of_build_partial_solve_wit_7_pure_split_goal_5.
  - Goal_apply proof_of_build_partial_solve_wit_7_pure_split_goal_6.
Qed.

Lemma proof_of_build_partial_solve_wit_8_pure_split_goal_1 : build_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH28 (2*v_pre+1) ((l_pre+r_pre)/2) r_pre
    (P073Desc_right v_pre l_pre r_pre (2*v_pre+1) ((l_pre+r_pre)/2) r_pre
      ltac:(lia) (P073Desc_here _ _ _))). lia.
Qed.

Lemma proof_of_build_partial_solve_wit_8_pure_split_goal_2 : build_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Mid_sublist__build_recursive l_pre r_pre ltac:(lia) ltac:(lia)) as [HM HQ].
  rewrite HQ, Zlength_sublist by lia; lia.
Qed.

Lemma proof_of_build_partial_solve_wit_8_pure_split_goal_3 : build_partial_solve_wit_8_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Mid_sublist__build_recursive l_pre r_pre ltac:(lia) ltac:(lia)) as [HM HQ].
  rewrite HQ, Zlength_sublist by lia; lia.
Qed.

Lemma proof_of_build_partial_solve_wit_8_pure_split_goal_4 : build_partial_solve_wit_8_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Mid_sublist__build_recursive l_pre r_pre ltac:(lia) ltac:(lia)) as [HM HQ].
  rewrite HQ; repeat rewrite Zlength_sublist by lia; lia.
Qed.

Lemma proof_of_build_partial_solve_wit_8_pure_split_goal_5 : build_partial_solve_wit_8_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Mid_sublist__build_recursive l_pre r_pre ltac:(lia) ltac:(lia)) as [HM HQ].
  rewrite HQ in *; replace (v_pre*2) with (2*v_pre) in * by ring.
  repeat rewrite Zlength_sublist by lia.
  replace ((l_pre+r_pre)/2-l_pre+(r_pre-(l_pre+r_pre)/2)) with (r_pre-l_pre) by ring.
  eapply P073Root_length__build_recursive; eauto; lia.
Qed.

Lemma proof_of_build_partial_solve_wit_8_pure_split_goal_6 : build_partial_solve_wit_8_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Mid_sublist__build_recursive l_pre r_pre ltac:(lia) ltac:(lia)) as [HM HQ].
  rewrite HQ in *; replace (v_pre*2) with (2*v_pre) in * by ring.
  rewrite Zlength_sublist by lia.
  pose proof (P073Left_tree__build_recursive N v_pre l_pre r_pre xs pr1_2 su1_2 ct1_2 ln1_2 pr1 su1 ct1 ln1 ltac:(lia) ltac:(lia) PreH28 PreH14 PreH12) as HT.
  exact (proj1 (HT _ _ _ (P073Desc_here _ _ _))).
Qed.

Lemma proof_of_build_partial_solve_wit_8_pure_split_goal_7 : build_partial_solve_wit_8_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Mid_sublist__build_recursive l_pre r_pre ltac:(lia) ltac:(lia)) as [HM HQ].
  rewrite HQ in *; replace (v_pre*2) with (2*v_pre) in * by ring.
  rewrite Zlength_sublist by lia.
  exact (proj1 (PreH11 _ _ _ (P073Desc_here _ _ _))).
Qed.

Lemma proof_of_build_partial_solve_wit_8_pure_split_goal_8 : build_partial_solve_wit_8_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg in * by lia.
  replace (v_pre*2) with (2*v_pre) in * by ring.
  pose proof (P073Left_tree__build_recursive N v_pre l_pre r_pre xs pr1_2 su1_2 ct1_2 ln1_2 pr1 su1 ct1 ln1 ltac:(lia) ltac:(lia) PreH28 PreH14 PreH12) as HT.
  exact (proj2 (HT _ _ _ (P073Desc_here _ _ _))).
Qed.

Lemma proof_of_build_partial_solve_wit_8_pure_split_goal_9 : build_partial_solve_wit_8_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace (v_pre*2) with (2*v_pre) in * by ring.
  exact (proj2 (PreH11 _ _ _ (P073Desc_here _ _ _))).
Qed.

Lemma proof_of_build_partial_solve_wit_8_pure : build_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_build_partial_solve_wit_8_pure_split_goal_2.
  - Goal_apply proof_of_build_partial_solve_wit_8_pure_split_goal_3.
  - Goal_apply proof_of_build_partial_solve_wit_8_pure_split_goal_4.
  - Goal_apply proof_of_build_partial_solve_wit_8_pure_split_goal_5.
  - Goal_apply proof_of_build_partial_solve_wit_8_pure_split_goal_6.
  - Goal_apply proof_of_build_partial_solve_wit_8_pure_split_goal_7.
  - Goal_apply proof_of_build_partial_solve_wit_8_pure_split_goal_8.
  - Goal_apply proof_of_build_partial_solve_wit_8_pure_split_goal_9.
Qed.

Lemma proof_of_update_entail_wit_1_split_goal_1 : update_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodeFrame. intros. repeat split; reflexivity.
Qed.

Lemma proof_of_update_entail_wit_1_split_goal_2 : update_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073NodePrefix. intros. lia.
Qed.

Lemma proof_of_update_entail_wit_1_split_goal_3 : update_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  auto.
Qed.

Lemma proof_of_update_entail_wit_1 : update_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_update_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_update_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_update_entail_wit_2_split_goal_1 : update_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_update_entail_wit_2_split_goal_2 : update_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_update_entail_wit_2_split_goal_3 : update_entail_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_update_entail_wit_2_split_goal_4 : update_entail_wit_2_split_goal_4.
Proof. Abort.

Lemma proof_of_update_entail_wit_2 : update_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (IntArray.full_Zlength PP (68*N)
    (replace_Znth (b*4*N+v_pre) (Z.land (Z.shiftr x_pre b) 1) pr1_2)).
  Intros_p Hpr.
  prop_apply_p (IntArray.full_Zlength SP (68*N)
    (replace_Znth (b*4*N+v_pre) (Z.land (Z.shiftr x_pre b) 1) su1_2)).
  Intros_p Hsu.
  prop_apply_p (Int64Array.full_Zlength CP (68*N)
    (replace_Znth (b*4*N+v_pre) (Z.land (Z.shiftr x_pre b) 1) ct1_2)).
  Intros_p Hct.
  rewrite !Zlength_replace_Znth in Hpr, Hsu, Hct.
  Exists (replace_Znth (b*4*N+v_pre) (Z.land (Z.shiftr x_pre b) 1) pr1_2)
    (replace_Znth (b*4*N+v_pre) (Z.land (Z.shiftr x_pre b) 1) su1_2)
    (replace_Znth (b*4*N+v_pre) (Z.land (Z.shiftr x_pre b) 1) ct1_2).
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try nia.
    + eapply P073Prefix_write__update_leaf; try eassumption; try lia.
      rewrite PreH7, PreH8, P073Singleton_update__update_leaf by lia.
      rewrite P073Bit_extract__update_leaf by lia.
      apply P073Singleton_summary__update_leaf.
    + eapply P073Frame_write__update_leaf; try eassumption; lia.
    + eapply P073Bounds_write__update_leaf; try eassumption; try lia.
      rewrite P073Bit_extract__update_leaf by lia.
      unfold P073Indicator. destruct (Z.testbit x_pre b); lia.
Qed.

Lemma proof_of_update_return_wit_1_split_goal_1 : update_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073OutsideTree. split; intros.
  - reflexivity.
  - apply PreH20; auto. left. intro E. subst w.
    apply (H1 p_pre (l_pre + 1)). constructor.
Qed.

Lemma proof_of_update_return_wit_1_split_goal_2 : update_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold P073Tree. intros w lo hi Hd.
  pose proof (proj1 (PreH18 _ _ _ (P073Desc_here _ _ _))) as Hlen.
  inversion Hd; subst; try lia.
  split.
  - exact Hlen.
  - intros bit Hb. apply PreH19. lia.
Qed.

Lemma proof_of_update_return_wit_1 : update_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_return_wit_1_split_goal_1.
  - Goal_apply proof_of_update_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_update_return_wit_2_split_goal_1 : update_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  replace (v_pre * 2) with (2*v_pre) in * by ring.
  eapply P073Outside_parent__update_merge; [|exact PreH5|exact PreH2].
  intros w lo hi HD. apply P073Desc_left; auto; lia.
Qed.

Lemma proof_of_update_return_wit_2_split_goal_2 : update_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  replace (v_pre * 2) with (2*v_pre) in * by ring.
  assert (Hmid : l_pre < (l_pre+r_pre)/2 < r_pre).
  { pose proof (Z.div_mod (l_pre+r_pre) 2 ltac:(lia)).
    pose proof (Z.mod_pos_bound (l_pre+r_pre) 2 ltac:(lia)). lia. }
  rewrite <- sublist_split in PreH1 by
    (rewrite ?P073Replace_length__update_merge; lia).
  eapply P073Updated_parent__update_merge;
    [lia|lia|exact PreH21| |exact PreH4| |exact PreH1|exact PreH2].
  - exact (proj1 (PreH22 _ _ _ (P073Desc_here _ _ _))).
  - eapply P073Unchanged_child__update_merge; [lia|lia|lia| |left; lia| | |exact PreH5].
    + intros w lo hi HD. apply PreH21. apply P073Desc_right; auto; lia.
    + intros w lo hi lo' hi' HD HD'.
      eapply (P073Desc_siblings__update_merge v_pre); [lia|exact HD'|exact HD].
    + intros w lo hi HD. apply PreH22. apply P073Desc_right; auto; lia.
Qed.

Lemma proof_of_update_return_wit_2 : update_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_return_wit_2_split_goal_1.
  - Goal_apply proof_of_update_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_update_return_wit_3_split_goal_1 : update_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  replace (v_pre * 2) with (2*v_pre) in * by ring.
  eapply P073Outside_parent__update_merge; [|exact PreH5|exact PreH2].
  intros w lo hi HD. apply P073Desc_right; auto; lia.
Qed.

Lemma proof_of_update_return_wit_3_split_goal_2 : update_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  replace (v_pre * 2) with (2*v_pre) in * by ring.
  assert (Hmid : l_pre < (l_pre+r_pre)/2 < r_pre).
  { pose proof (Z.div_mod (l_pre+r_pre) 2 ltac:(lia)).
    pose proof (Z.mod_pos_bound (l_pre+r_pre) 2 ltac:(lia)). lia. }
  rewrite <- sublist_split in PreH1 by
    (rewrite ?P073Replace_length__update_merge; lia).
  eapply P073Updated_parent__update_merge;
    [lia|lia|exact PreH21| | |exact PreH4|exact PreH1|exact PreH2].
  - exact (proj1 (PreH22 _ _ _ (P073Desc_here _ _ _))).
  - eapply P073Unchanged_child__update_merge; [lia|lia|lia| |right; lia| | |exact PreH5].
    + intros w lo hi HD. apply PreH21. apply P073Desc_left; auto; lia.
    + intros w lo hi lo' hi' HD HD'.
      eapply (P073Desc_siblings__update_merge v_pre); [lia|exact HD|exact HD'].
    + intros w lo hi HD. apply PreH22. apply P073Desc_left; auto; lia.
Qed.

Lemma proof_of_update_return_wit_3 : update_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_return_wit_3_split_goal_1.
  - Goal_apply proof_of_update_return_wit_3_split_goal_2.
Qed.

Lemma proof_of_update_partial_solve_wit_4_pure_split_goal_1 : update_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH29 (2*v_pre) l_pre ((l_pre+r_pre)/2)
    (P073Desc_left v_pre l_pre r_pre (2*v_pre) l_pre ((l_pre+r_pre)/2)
      ltac:(lia) (P073Desc_here _ _ _))) as Hchild.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_update_partial_solve_wit_4_pure_split_goal_2 : update_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (P073Mid_bounds__update_routing l_pre r_pre ltac:(lia) ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_update_partial_solve_wit_4_pure_split_goal_3 : update_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (P073Mid_bounds__update_routing l_pre r_pre ltac:(lia) ltac:(lia)) as [Heq Hb].
  rewrite Heq. replace (v_pre*2) with (2*v_pre) by lia.
  dump_pre_spatial.
  intros w lo hi Hd. apply PreH29.
  apply P073Desc_left; [lia | exact Hd].
Qed.

Lemma proof_of_update_partial_solve_wit_4_pure_split_goal_4 : update_partial_solve_wit_4_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (P073Mid_bounds__update_routing l_pre r_pre ltac:(lia) ltac:(lia)) as [Heq Hb].
  rewrite Heq. replace (v_pre*2) with (2*v_pre) by lia.
  dump_pre_spatial.
  intros w lo hi Hd. apply PreH30.
  apply P073Desc_left; [lia | exact Hd].
Qed.

Lemma proof_of_update_partial_solve_wit_4_pure : update_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_update_partial_solve_wit_4_pure_split_goal_2.
  - Goal_apply proof_of_update_partial_solve_wit_4_pure_split_goal_3.
  - Goal_apply proof_of_update_partial_solve_wit_4_pure_split_goal_4.
Qed.

Lemma proof_of_update_partial_solve_wit_5_pure_split_goal_1 : update_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH29 (2*v_pre+1) ((l_pre+r_pre)/2) r_pre
    (P073Desc_right v_pre l_pre r_pre (2*v_pre+1) ((l_pre+r_pre)/2) r_pre
      ltac:(lia) (P073Desc_here _ _ _))) as Hchild.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_update_partial_solve_wit_5_pure_split_goal_2 : update_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (P073Mid_bounds__update_routing l_pre r_pre ltac:(lia) ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_update_partial_solve_wit_5_pure_split_goal_3 : update_partial_solve_wit_5_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (P073Mid_bounds__update_routing l_pre r_pre ltac:(lia) ltac:(lia)) as [Heq Hb].
  rewrite Heq. replace (v_pre*2) with (2*v_pre) by lia.
  dump_pre_spatial.
  intros w lo hi Hd. apply PreH29.
  apply P073Desc_right; [lia | exact Hd].
Qed.

Lemma proof_of_update_partial_solve_wit_5_pure_split_goal_4 : update_partial_solve_wit_5_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (P073Mid_bounds__update_routing l_pre r_pre ltac:(lia) ltac:(lia)) as [Heq Hb].
  rewrite Heq. replace (v_pre*2) with (2*v_pre) by lia.
  dump_pre_spatial.
  intros w lo hi Hd. apply PreH30.
  apply P073Desc_right; [lia | exact Hd].
Qed.

Lemma proof_of_update_partial_solve_wit_5_pure : update_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_update_partial_solve_wit_5_pure_split_goal_2.
  - Goal_apply proof_of_update_partial_solve_wit_5_pure_split_goal_3.
  - Goal_apply proof_of_update_partial_solve_wit_5_pure_split_goal_4.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_1 : update_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH32 (2*v_pre+1) ((l_pre+r_pre)/2) r_pre
    (P073Desc_right v_pre l_pre r_pre _ _ _ ltac:(lia) (P073Desc_here _ _ _))) as H.
  tauto.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_2 : update_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  rewrite Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_3 : update_partial_solve_wit_6_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  rewrite Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_4 : update_partial_solve_wit_6_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  rewrite !Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_5 : update_partial_solve_wit_6_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  pose proof (proj1 (PreH33 _ _ _ (P073Desc_here v_pre l_pre r_pre))).
  rewrite !Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_6 : update_partial_solve_wit_6_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  pose proof (proj1 (PreH33 _ _ _ (P073Desc_left v_pre l_pre r_pre _ _ _ ltac:(lia) (P073Desc_here _ _ _)))).
  rewrite Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_7 : update_partial_solve_wit_6_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  pose proof (proj1 (PreH33 _ _ _ (P073Desc_right v_pre l_pre r_pre _ _ _ ltac:(lia) (P073Desc_here _ _ _)))).
  rewrite Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_8 : update_partial_solve_wit_6_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace (2*v_pre) with (v_pre*2) by lia.
  exact (proj2 (PreH15 _ _ _ (P073Desc_here _ _ _))).
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure_split_goal_9 : update_partial_solve_wit_6_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  replace (v_pre*2) with (2*v_pre) in PreH16 by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)) as Hmid.
  pose proof (P073Desc_right v_pre l_pre r_pre _ _ _ ltac:(lia)
    (P073Desc_here (2*v_pre+1) ((l_pre+r_pre)/2) r_pre)) as HD.
  pose proof (PreH32 _ _ _ HD) as Hbounds.
  pose proof (proj1 (P073Sibling_exclusion__update_pull_input v_pre l_pre ((l_pre+r_pre)/2) r_pre ltac:(lia))) as Houtside.
  unfold P073NodePrefix; intros b Hb.
  destruct (proj2 PreH16 (2*v_pre+1) b ltac:(lia) Hb Houtside) as [Hp [Hs Hc]].
  rewrite Hp, Hs, Hc.
  rewrite P073Sublist_update_outside__update_pull_input by lia.
  exact (proj2 (PreH33 _ _ _ HD) b Hb).
Qed.

Lemma proof_of_update_partial_solve_wit_6_pure : update_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_update_partial_solve_wit_6_pure_split_goal_2.
  - Goal_apply proof_of_update_partial_solve_wit_6_pure_split_goal_3.
  - Goal_apply proof_of_update_partial_solve_wit_6_pure_split_goal_4.
  - Goal_apply proof_of_update_partial_solve_wit_6_pure_split_goal_5.
  - Goal_apply proof_of_update_partial_solve_wit_6_pure_split_goal_6.
  - Goal_apply proof_of_update_partial_solve_wit_6_pure_split_goal_7.
  - Goal_apply proof_of_update_partial_solve_wit_6_pure_split_goal_8.
  - Goal_apply proof_of_update_partial_solve_wit_6_pure_split_goal_9.
Qed.

Lemma proof_of_update_partial_solve_wit_7_pure_split_goal_1 : update_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH32 (2*v_pre+1) ((l_pre+r_pre)/2) r_pre
    (P073Desc_right v_pre l_pre r_pre _ _ _ ltac:(lia) (P073Desc_here _ _ _))) as H.
  tauto.
Qed.

Lemma proof_of_update_partial_solve_wit_7_pure_split_goal_2 : update_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  rewrite Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_7_pure_split_goal_3 : update_partial_solve_wit_7_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  rewrite Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_7_pure_split_goal_4 : update_partial_solve_wit_7_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  rewrite !Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_7_pure_split_goal_5 : update_partial_solve_wit_7_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  pose proof (proj1 (PreH33 _ _ _ (P073Desc_here v_pre l_pre r_pre))).
  rewrite !Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_7_pure_split_goal_6 : update_partial_solve_wit_7_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  pose proof (proj1 (PreH33 _ _ _ (P073Desc_left v_pre l_pre r_pre _ _ _ ltac:(lia) (P073Desc_here _ _ _)))).
  rewrite Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_7_pure_split_goal_7 : update_partial_solve_wit_7_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)).
  pose proof (proj1 (PreH33 _ _ _ (P073Desc_right v_pre l_pre r_pre _ _ _ ltac:(lia) (P073Desc_here _ _ _)))).
  rewrite Zlength_sublist by (rewrite Zlength_replace_Znth; lia). lia.
Qed.

Lemma proof_of_update_partial_solve_wit_7_pure_split_goal_8 : update_partial_solve_wit_7_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in * by lia.
  replace (v_pre*2) with (2*v_pre) in PreH16 by lia.
  pose proof (P073Midpoint__update_pull_input l_pre r_pre ltac:(lia) ltac:(lia)) as Hmid.
  pose proof (P073Desc_left v_pre l_pre r_pre _ _ _ ltac:(lia)
    (P073Desc_here (2*v_pre) l_pre ((l_pre+r_pre)/2))) as HD.
  pose proof (PreH32 _ _ _ HD) as Hbounds.
  pose proof (proj2 (P073Sibling_exclusion__update_pull_input v_pre l_pre ((l_pre+r_pre)/2) r_pre ltac:(lia))) as Houtside.
  unfold P073NodePrefix; intros b Hb.
  destruct (proj2 PreH16 (2*v_pre) b ltac:(lia) Hb Houtside) as [Hp [Hs Hc]].
  rewrite Hp, Hs, Hc.
  rewrite P073Sublist_update_outside__update_pull_input by lia.
  exact (proj2 (PreH33 _ _ _ HD) b Hb).
Qed.

Lemma proof_of_update_partial_solve_wit_7_pure_split_goal_9 : update_partial_solve_wit_7_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace (2*v_pre) with (v_pre*2) by lia.
  exact (proj2 (PreH15 _ _ _ (P073Desc_here _ _ _))).
Qed.

Lemma proof_of_update_partial_solve_wit_7_pure : update_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_update_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_update_partial_solve_wit_7_pure_split_goal_2.
  - Goal_apply proof_of_update_partial_solve_wit_7_pure_split_goal_3.
  - Goal_apply proof_of_update_partial_solve_wit_7_pure_split_goal_4.
  - Goal_apply proof_of_update_partial_solve_wit_7_pure_split_goal_5.
  - Goal_apply proof_of_update_partial_solve_wit_7_pure_split_goal_6.
  - Goal_apply proof_of_update_partial_solve_wit_7_pure_split_goal_7.
  - Goal_apply proof_of_update_partial_solve_wit_7_pure_split_goal_8.
  - Goal_apply proof_of_update_partial_solve_wit_7_pure_split_goal_9.
Qed.

Lemma proof_of_solver_safety_wit_15_split_goal_1 : solver_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Shift17__solver_safety b ltac:(lia)) as [Hs Hp]. rewrite Hs.
  rewrite signed_last_nbits_eq; [|lia|change (-2147483648 <= 2^b < 2147483648); lia].
  destruct PreH27 as [HB HL].
  specialize (HB (b*4*size_pre+1) (PreH32 PreH1)).
  assert (Hcap : size_pre*(size_pre+1)/2 <= 5000050000).
  { apply Z.div_le_upper_bound; nia. }
  nia.
Qed.

Lemma proof_of_solver_safety_wit_15_split_goal_2 : solver_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Shift17__solver_safety b ltac:(lia)) as [Hs Hp]. rewrite Hs.
  rewrite signed_last_nbits_eq; [|lia|change (-2147483648 <= 2^b < 2147483648); lia].
  destruct PreH27 as [HB HL].
  specialize (HB (b*4*size_pre+1) (PreH32 PreH1)).
  nia.
Qed.

Lemma proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_16_split_goal_1 : solver_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Shift17__solver_safety b ltac:(lia)) as [Hs Hp]. rewrite Hs.
  rewrite signed_last_nbits_eq; [|lia|change (-2147483648 <= 2^b < 2147483648); lia].
  destruct PreH27 as [HB HL].
  specialize (HB (b*4*size_pre+1) (PreH32 PreH1)).
  assert (Hcap : size_pre*(size_pre+1)/2 <= 5000050000).
  { apply Z.div_le_upper_bound; nia. }
  nia.
Qed.

Lemma proof_of_solver_safety_wit_16_split_goal_2 : solver_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (P073Shift17__solver_safety b ltac:(lia)) as [Hs Hp]. rewrite Hs.
  rewrite signed_last_nbits_eq; [|lia|change (-2147483648 <= 2^b < 2147483648); lia].
  destruct PreH27 as [HB HL].
  specialize (HB (b*4*size_pre+1) (PreH32 PreH1)).
  nia.
Qed.

Lemma proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (P073Pow17__solver_safety b ltac:(lia)) as Hp.
  rewrite Z.mul_1_l, signed_last_nbits_eq; [lia|lia|].
  change (-2147483648 <= 2^b < 2147483648). lia.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (P073Pow17__solver_safety b ltac:(lia)) as Hp.
  rewrite Z.mul_1_l, signed_last_nbits_eq; [lia|lia|].
  change (-2147483648 <= 2^b < 2147483648). lia.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_3 : solver_safety_wit_17_split_goal_3.
Proof. LLM_pre_process ltac:(lia || nia || int_auto). Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_4 : solver_safety_wit_17_split_goal_4.
Proof. LLM_pre_process ltac:(lia || nia || int_auto). Qed.

Lemma proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_2.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_3.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  repeat match goal with H : forall j : Z, _ -> _ |- _ =>
    specialize (H k_2 ltac:(lia))
  end.
  intuition lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst; eauto.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  eauto.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst.
  rewrite (sublist_split 0 (i + 1) i) by lia.
  rewrite (sublist_single 0 i) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_spatial : solver_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  assert (i = size_pre) by lia.
  subst i.
  rewrite sublist_self by lia.
  sep_apply_l_atomic (IntArray.seg_to_full a 0 size_pre original).
  rewrite Z.mul_0_l, Z.add_0_r, Z.sub_0_r.
  cancel (IntArray.full a size_pre original).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply (proj1 (P073Zero_buffers__solver_layout size_pre ltac:(lia))).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply (proj2 (P073Zero_buffers__solver_layout size_pre ltac:(lia))).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply P073Root_layout__solver_layout. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_5 : solver_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_spatial : solver_entail_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (17 * 4) with 68 by reflexivity.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption).
  unfold P073History.
  exists (initial_a :: nil).
  repeat split; try reflexivity; intros; lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || assumption).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || assumption).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || assumption).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || assumption).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof. LLM_pre_process ltac:(lia || nia). Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia).
  destruct (P073Shift17__solver_weighted b ltac:(lia)) as [Hshift Hp].
  rewrite Hshift, signed_last_nbits_eq, PreH29; try (change (-2147483648 <= 2^b < 2147483648); lia); try lia.
  assert (Hlen : Zlength (replace_Znth p v current) = size_pre).
  { rewrite Zlength_replace_Znth. exact PreH19. }
  rewrite (P073Root_count__solver_weighted size_pre (replace_Znth p v current)
    pr_2 su_2 ct_2 ln_2 b Hlen ltac:(lia) PreH26).
  rewrite <- P073Weighted_step__solver_weighted by lia.
  pose proof (P073TreeWeighted_bound__solver_weighted size_pre
    (replace_Znth p v current) pr_2 su_2 ct_2 ln_2 (b+1)
    ltac:(lia) Hlen ltac:(lia) PreH26 PreH27). lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia).
  destruct (P073Shift17__solver_weighted b ltac:(lia)) as [Hshift Hp].
  rewrite Hshift, signed_last_nbits_eq; try (change (-2147483648 <= 2^b < 2147483648); lia); try lia.
  destruct PreH27 as [Hbounds _].
  specialize (Hbounds (b*4*size_pre+1) ltac:(nia)). nia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia).
  destruct (P073Shift17__solver_weighted b ltac:(lia)) as [Hshift Hp].
  rewrite Hshift, signed_last_nbits_eq, PreH29; try (change (-2147483648 <= 2^b < 2147483648); lia); try lia.
  assert (Hlen : Zlength (replace_Znth p v current) = size_pre).
  { rewrite Zlength_replace_Znth. exact PreH19. }
  rewrite (P073Root_count__solver_weighted size_pre (replace_Znth p v current)
    pr_2 su_2 ct_2 ln_2 b Hlen ltac:(lia) PreH26).
  symmetry. apply P073Weighted_step__solver_weighted. lia.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hupd : Znth i updates (0,0) = (p,v)).
  { rewrite (Znth_indep updates i (0,0) __default__Prod_Z_Z) by lia.
    specialize (PreH24 i ltac:(lia)).
    destruct (Znth i updates __default__Prod_Z_Z) as [q w]; cbn in PreH24.
    f_equal; lia. }
  assert (Hnext : ApplyPointUpdate current (Znth i updates (0,0)) = replace_Znth p v current).
  { rewrite Hupd; reflexivity. }
  rewrite <- Hnext.
  apply P073History_snoc__solver_history; try lia.
  - now rewrite <- PreH2.
  - rewrite Hnext, PreH29.
    replace b with 17 by lia.
    apply P073Weighted17_spec__solver_history.
    apply P073Replace_bounds__solver_history; try lia.
    intros k Hk; apply PreH23; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  auto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_3 : solver_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply P073Replace_bounds__solver_history; try lia.
  - intros j Hj; apply PreH23; lia.
  - rewrite Zlength_replace_Znth; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_4 : solver_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth; exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_4.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = m_pre) by lia.
  subst i original.
  Exists result_2.
  split_pure_spatial.
  - sep_apply_l_atomic (Int64Array.seg_to_full out_pre 0 m_pre result_2).
    replace (out_pre + 0 * sizeof(INT64)) with out_pre by ring.
    replace (m_pre - 0) with m_pre by ring.
    cancel.
  - split_pures.
    dump_pre_spatial.
    apply (P073History_finish initial_a updates final_values result_2).
    rewrite PreH12.
    exact PreH20.
Qed.

Lemma proof_of_solver_partial_solve_wit_8_pure_split_goal_1 : solver_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (IntArray.full_Zlength LP (4*size_pre) (repeat_Z 0 (4*size_pre))).
  Intros_p Hlen. dump_pre_spatial. exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_8_pure_split_goal_2 : solver_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_8_pure : solver_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_8_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_12_pure_split_goal_1 : solver_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption).
Qed.

Lemma proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_12_pure_split_goal_1.
Qed.
