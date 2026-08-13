Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import avl_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import avl_shape.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma avl_strategy0_correctness : avl_strategy0.
Proof.
  pre_process_default.
  Intros_p H0.
  subst tr1.
  cancel.
Qed.

Lemma avl_strategy9_correctness : avl_strategy9.
  pre_process_default.
Qed.

Lemma avl_strategy12_correctness : avl_strategy12.
  pre_process_default.
Qed.

Lemma avl_strategy7_correctness : avl_strategy7.
Proof.
  pre_process_default.
  unfold single_tree_node.
  cancel.
  cancel.
  cancel.
  cancel.
Qed.

Lemma avl_strategy8_correctness : avl_strategy8.
Proof.
  pre_process_default.
  unfold single_tree_node.
  cancel.
  cancel.
  cancel.
  cancel.
Qed.

Lemma avl_strategy1_correctness : avl_strategy1.
Proof.
  pre_process_default.
  destruct tr.
  - simpl.
    Intros_p H0.
    contradiction.
  - simpl.
    Intros l.
    Intros r.
    Intros k.
    Intros v.
    Intros h.
    Exists k.
    Exists v.
    Exists h.
    Exists l.
    Exists r.
    Exists tr1.
    Exists tr2.
    normalize.
    wand_elim.
    cancel.
    split_pures.
    split_pure_spatial.
    + unfold single_tree_node.
      cancel.
      cancel.
      cancel.
      cancel.
      cancel.
      cancel.
    + split_pures.
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        reflexivity.
Qed.

Lemma avl_strategy2_correctness : avl_strategy2.
Proof.
  pre_process_default.
  split_pure_spatial.
  - Intros_r tr.
    Intros_r tr1.
    Intros_r tr2.
    Intros_r l.
    Intros_r v.
    Intros_r h.
    Intros_r k.
    Intros_r r.
    apply_sepcon_adjoint.
    cancel.
    Intros_p H0.
    subst tr.
    simpl.
    Exists l.
    Exists r.
    Exists k.
    Exists v.
    Exists h.
    split_pure_spatial.
    + unfold single_tree_node.
      cancel.
      cancel.
    + dump_pre_spatial.
      exact H.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma avl_strategy3_correctness : avl_strategy3.
Proof.
  pre_process_default.
  destruct tr.
  - simpl.
    split_pure_spatial.
    + Intros_p H0.
      cancel.
    + split_pures.
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        reflexivity.
  - simpl.
    Intros l.
    Intros r.
    Intros k.
    Intros v.
    Intros h.
    contradiction.
Qed.

Lemma avl_strategy4_correctness : avl_strategy4.
Proof.
  pre_process_default.
  split_pure_spatial.
  - Intros_r tr.
    apply_sepcon_adjoint.
    cancel.
    Intros_p H0.
    subst tr p.
    simpl.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      reflexivity.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma avl_strategy10_correctness : avl_strategy10.
Proof.
  pre_process_default.
  Intros tr.
  Exists tr.
  normalize.
  wand_elim.
  cancel.
Qed.

Lemma avl_strategy11_correctness : avl_strategy11.
Proof.
  pre_process_default.
  unfold store_tree_shape.
  Exists tr.
  cancel.
Qed.

Lemma avl_strategy13_correctness : avl_strategy13.
Proof.
  pre_process_default.
  unfold store_non_empty_tree.
  Intros_p H.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma avl_strategy15_correctness : avl_strategy15.
Proof.
  pre_process_default.
  split_pure_spatial.
  - apply_sepcon_adjoint.
    cancel.
    unfold store_non_empty_tree.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      exact H.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma avl_strategy16_correctness : avl_strategy16.
Proof.
  pre_process_default.
  split_pure_spatial.
  - Intros_r tr.
    Intros_r tr1.
    Intros_r tr2.
    Intros_r l.
    Intros_r v.
    Intros_r h.
    Intros_r k.
    Intros_r r.
    apply_sepcon_adjoint.
    cancel.
    Intros_p H0.
    subst tr.
    simpl.
    Exists l.
    Exists r.
    Exists k.
    Exists v.
    Exists h.
    split_pure_spatial.
    + unfold single_tree_node.
      repeat cancel.
    + dump_pre_spatial.
      exact H.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma avl_strategy17_correctness : avl_strategy17.
Proof.
  pre_process_default.
  Intros_p H.
  subst tr.
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma avl_strategy5_correctness : avl_strategy5.
Proof.
  pre_process_default.
  unfold single_tree_node.
  cancel.
  cancel.
  cancel.
  cancel.
Qed.

Lemma avl_strategy6_correctness : avl_strategy6.
Proof.
  pre_process_default.
  unfold single_tree_node.
  cancel.
  cancel.
  cancel.
  cancel.
Qed.

Lemma avl_strategy25_correctness : avl_strategy25.
Proof.
  pre_process_default.
  prop_apply (valid_store_uchar p).
  Intros.
  split_pure_spatial.
  - cancel.
  - destruct H as [Hrange _].
    dump_pre_spatial.
    destruct Hrange as [Hmin _].
    lia.
Qed.

Lemma avl_strategy26_correctness : avl_strategy26.
Proof.
  pre_process_default.
  prop_apply (valid_store_uchar p).
  Intros.
  split_pure_spatial.
  - cancel.
  - destruct H as [Hrange _].
    dump_pre_spatial.
    destruct Hrange as [_ Hmax].
    replace Byte.max_unsigned with (2 ^ 8 - 1) in Hmax by reflexivity.
    lia.
Qed.
