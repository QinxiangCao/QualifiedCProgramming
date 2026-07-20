Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import poly_sll_strategy_goal.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import poly_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma poly_sll_strategy1_correctness : poly_sll_strategy1.
  pre_process_default.
Qed.

Lemma poly_sll_strategy2_correctness : poly_sll_strategy2.
  pre_process_default.
Qed.

Lemma poly_sll_strategy4_correctness : poly_sll_strategy4.
Proof.
  pre_process_default.
  sep_apply_l_atomic (sll_zero A storeA 0 l eq_refl).
  Intros_p H.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma poly_sll_strategy5_correctness : poly_sll_strategy5.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma poly_sll_strategy16_correctness : poly_sll_strategy16.
Proof.
  pre_process_default.
  Intros_p H.
  subst y.
  cancel.
Qed.

Lemma poly_sll_strategy17_correctness : poly_sll_strategy17.
Proof.
  pre_process_default.
  destruct l.
  - simpl.
    Intros_p H.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      reflexivity.
  - simpl.
    destruct l0.
    + simpl.
      split_pure_spatial.
      * Intros h.
        Intros q.
        split_pures.
        contradiction.
      * Intros h.
        Intros q.
        split_pures.
        contradiction.
        contradiction.
    + simpl.
      split_pure_spatial.
      * Intros h.
        Intros q.
        Intros h0.
        Intros y.
        sep_apply_l_atomic (dup_store_ptr (&( p # "list" ->ₛ "data")) h h0).
        Intros_p H1.
        contradiction.
      * Intros h.
        Intros q.
        Intros h0.
        Intros y.
        sep_apply_l_atomic (dup_store_ptr (&( p # "list" ->ₛ "data")) h h0).
        Intros_p H1.
        contradiction.
Qed.

Lemma poly_sll_strategy18_correctness : poly_sll_strategy18.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  simpl.
  cancel (sll storeA p l0).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma poly_sll_strategy7_correctness : poly_sll_strategy7.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  cancel.
Qed.

Lemma poly_sll_strategy10_correctness : poly_sll_strategy10.
Proof.
  pre_process_default.
  Intros h.
  Intros y.
  Exists y.
  Exists h.
  normalize.
  wand_elim.
  elim_emp.
  cancel.
  cancel.
  cancel.
Qed.

Lemma poly_sll_strategy11_correctness : poly_sll_strategy11.
Proof.
  pre_process_default.
  Intros_p H.
  Exists h.
  Exists y.
  split_pure_spatial.
  - cancel.
    cancel.
    cancel.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma poly_sll_strategy12_correctness : poly_sll_strategy12.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  sep_apply_l_atomic (sllseg_sll A storeA p q l0 l2).
  cancel.
Qed.

Lemma poly_sll_strategy8_correctness : poly_sll_strategy8.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  assert (Hp : p <> 0).
  {
    destruct Hnz as [Hnz | Hnz].
    - exact Hnz.
    - intro Hp0.
      apply Hnz.
      symmetry.
      exact Hp0.
  }
  sep_apply_l_atomic (sll_not_zero A storeA p l Hp).
  Intros h.
  Intros y.
  Intros x.
  Intros l0.
  Exists x.
  Exists l0.
  simpl.
  normalize.
  Exists h.
  Exists y.
  wand_elim.
  elim_emp.
  rewrite <- logic_equiv_coq_prop_or.
  split_pure_spatial.
  - cancel.
    cancel.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      exact Hnz.
    + dump_pre_spatial.
      exact H.
    + dump_pre_spatial.
      exact Hp.
Qed.

Lemma poly_sll_strategy9_correctness : poly_sll_strategy9.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  split_pure_spatial.
  - Intros_r A.
    Intros_r l.
    Intros_r x.
    Intros_r l0.
    Intros_r storeA.
    apply_sepcon_adjoint.
    Intros_p H.
    subst l.
    cancel.
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma poly_sll_strategy19_correctness : poly_sll_strategy19.
  pre_process_default.
Qed.
