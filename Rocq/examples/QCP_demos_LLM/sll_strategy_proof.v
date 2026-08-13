Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sll_strategy3_correctness : sll_strategy3.
Proof.
  pre_process_default.
  simpl.
  split_pure_spatial.
  - Intros_p H.
    cancel.
  - Intros_p H.
    dump_pre_spatial.
    exact H.
Qed.

Lemma sll_strategy4_correctness : sll_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst p.
  simpl.
  cancel.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_strategy5_correctness : sll_strategy5.
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

Lemma sll_strategy6_correctness : sll_strategy6.
Proof.
  pre_process_default.
  Intros_p H.
  Intros_p H0.
  subst x1 l1.
  cancel.
Qed.

Lemma sll_strategy14_correctness : sll_strategy14.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  simpl.
  cancel (sll p l0).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_strategy15_correctness : sll_strategy15.  
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  simpl.
  cancel ((poly_store FET_int &(p # "list" ->ₛ "data") h)).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_strategy16_correctness : sll_strategy16.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  simpl.
  cancel (poly_store FET_ptr p q).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_strategy17_correctness : sll_strategy17.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  simpl.
  cancel (poly_undef_store ty p).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_strategy18_correctness : sll_strategy18.
Proof.
  pre_process_default.
  cancel (q # Ptr |-> v1).
  Intros_r l2.
  Intros_r v2.
  wand_elim.
  Intros_p H.
  subst l2.
  cancel (q # Ptr |-> v2).
  cancel (sllbseg p q l1).
Qed.

Lemma sll_strategy19_correctness : sll_strategy19.
Proof.
  pre_process_default.
  cancel (poly_undef_store ty q).
  Intros_r l2.
  Intros_r r.
  wand_elim.
  Intros_p H.
  Intros_p H0.
  subst r l2.
  cancel (sllbseg p q l1).
  cancel.
Qed.

Lemma sll_strategy20_correctness : sll_strategy20.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p H.
  split_pure_spatial.
  - Intros_r l.
    apply_sepcon_adjoint.
    Intros_p Hnil.
    subst l.
    destruct H as [H | H].
    + subst p.
      simpl.
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial.
        reflexivity.
    + subst p.
      simpl.
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial.
        reflexivity.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma sll_strategy21_correctness : sll_strategy21.
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
  sep_apply_l_atomic (sll_not_zero p l Hp).
  Intros q.
  Intros d.
  Intros l0.
  Exists d.
  Exists q.
  Exists l0.
  normalize.
  wand_elim.
  cancel.
  split_pures.
  rewrite <- logic_equiv_coq_prop_or.
  split_pure_spatial.
  - cancel.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      exact Hnz.
    + dump_pre_spatial.
      exact H.
Qed.

Lemma sll_strategy22_correctness : sll_strategy22.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  Exists (d :: l0).
  simpl.
  Exists q.
  normalize.
  wand_elim.
  cancel.
  split_pures.
  rewrite <- logic_equiv_coq_prop_or.
  split_pure_spatial.
  - cancel.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      exact Hnz.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      destruct Hnz as [Hnz | Hnz].
      * exact Hnz.
      * intro Hp0.
        apply Hnz.
        symmetry.
        exact Hp0.
Qed.

Lemma sll_strategy7_correctness : sll_strategy7.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  cancel.
Qed.

Lemma sll_strategy10_correctness : sll_strategy10.
Proof.
  pre_process_default.
  Intros y.
  Exists y.
  normalize.
  wand_elim.
  cancel.
  cancel.
Qed.

Lemma sll_strategy11_correctness : sll_strategy11.
Proof.
  pre_process_default.
  Intros_p H.
  Exists y.
  split_pure_spatial.
  - cancel.
    cancel.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma sll_strategy8_correctness : sll_strategy8.
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
  sep_apply_l_atomic (sll_not_zero p l Hp).
  Intros y.
  Intros x.
  Intros l0.
  Exists x.
  Exists l0.
  normalize.
  Exists y.
  rewrite <- logic_equiv_coq_prop_or.
  split_pure_spatial.
  - cancel (sll y l0).
    cancel (&( p # "list" ->ₛ "next") # Ptr |-> y).
    cancel (&( p # "list" ->ₛ "data") # Int |-> x).
    Intros_r q.
    apply_sepcon_adjoint.
    normalize.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      exact Hnz.
    + dump_pre_spatial.
      exact H.
    + dump_pre_spatial.
      exact Hp.
Qed.

Lemma sll_strategy9_correctness : sll_strategy9.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  split_pure_spatial.
  - Intros_r l.
    Intros_r x.
    Intros_r l0.
    apply_sepcon_adjoint.
    Intros_p H.
    subst l.
    cancel.
  - dump_pre_spatial.
    exact Hnz.
Qed.
