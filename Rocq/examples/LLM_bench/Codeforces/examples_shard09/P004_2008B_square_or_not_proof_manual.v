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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P004_2008B_square_or_not_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P004_2008B_square_or_not_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_1 : solver_entail_wit_5_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_1 : solver_entail_wit_5_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_5_split_goal_1 : solver_entail_wit_5_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct H as [[Hx Hy0] Hyr].
  destruct Hx as [Hx0 Hxlt].
  assert (Hjr : j = r) by lia.
  assert (Hxcase : x < i \/ x = i) by lia.
  destruct Hxcase as [Hxi | Hxi].
  - apply PreH14.
    repeat split; assumption.
  - subst x.
    apply PreH15.
    split; [exact Hy0 | lia].
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec, BeautifulFlat, OnBorder.
  left.
  split; [reflexivity |].
  exists r.
  assert (i = r) by lia.
  subst i.
  repeat split; try lia.
  intros x y Hx Hy.
  specialize (PreH12 x y).
  tauto.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  right.
  split; [reflexivity |].
  intros [q Hbeautiful].
  unfold BeautifulFlat in Hbeautiful.
  destruct Hbeautiful as (Hqpos & _ & Hqlen & Hcells).
  assert (q = r) by nia.
  subst q j.
  specialize (Hcells i 0 ltac:(lia) ltac:(lia)).
  destruct Hcells as [[_ Hcell] | [Hnotborder _]].
  - contradiction.
  - apply Hnotborder. unfold OnBorder. tauto.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  right.
  split; [reflexivity |].
  intros [q Hbeautiful].
  unfold BeautifulFlat in Hbeautiful.
  destruct Hbeautiful as (Hqpos & _ & Hqlen & Hcells).
  assert (q = r) by nia.
  subst q i.
  specialize (Hcells 0 j ltac:(lia) ltac:(lia)).
  destruct Hcells as [[_ Hcell] | [Hnotborder _]].
  - contradiction.
  - apply Hnotborder. unfold OnBorder. tauto.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  right.
  split; [reflexivity |].
  intros [q Hbeautiful].
  unfold BeautifulFlat in Hbeautiful.
  destruct Hbeautiful as (Hqpos & _ & Hqlen & Hcells).
  assert (q = r) by nia.
  subst q i.
  specialize (Hcells (r - 1) j ltac:(lia) ltac:(lia)).
  destruct Hcells as [[_ Hcell] | [Hnotborder _]].
  - contradiction.
  - apply Hnotborder. unfold OnBorder. tauto.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_5_split_goal_1 : solver_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  right.
  split; [reflexivity |].
  intros [q Hbeautiful].
  unfold BeautifulFlat in Hbeautiful.
  destruct Hbeautiful as (Hqpos & _ & Hqlen & Hcells).
  assert (q = r) by nia.
  subst q j.
  specialize (Hcells i (r - 1) ltac:(lia) ltac:(lia)).
  destruct Hcells as [[_ Hcell] | [Hnotborder _]].
  - contradiction.
  - apply Hnotborder. unfold OnBorder. tauto.
Qed.

Lemma proof_of_solver_return_wit_5 : solver_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_6_split_goal_1 : solver_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  right.
  split; [reflexivity |].
  intros [q Hbeautiful].
  unfold BeautifulFlat in Hbeautiful.
  destruct Hbeautiful as (Hqpos & _ & Hqlen & Hcells).
  assert (q = r) by nia.
  subst q.
  specialize (Hcells i j ltac:(lia) ltac:(lia)).
  destruct Hcells as [[Hborder _] | [_ Hcell]].
  - unfold OnBorder in Hborder. tauto.
  - contradiction.
Qed.

Lemma proof_of_solver_return_wit_6 : solver_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_7_split_goal_1 : solver_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec, BeautifulFlat.
  right.
  split; [reflexivity |].
  intros [q [Hqpos [_ [Hqlen _]]]].
  destruct (Z_le_gt_dec q r); nia.
Qed.

Lemma proof_of_solver_return_wit_7 : solver_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_7_split_goal_1.
Qed.
