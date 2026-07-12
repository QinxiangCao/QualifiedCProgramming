Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import sll_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_shape_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sll_shape_strategy3_correctness : sll_shape_strategy3.
Proof.
  pre_process_default.
  sep_apply_l_atomic (listrep_zero 0 eq_refl).
  cancel.
Qed.

Lemma sll_shape_strategy4_correctness : sll_shape_strategy4.
Proof.
  pre_process_default.
  unfold listrep.
  Exists (@nil Z).
  normalize.
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_shape_strategy5_correctness : sll_shape_strategy5.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p H.
  split_pure_spatial.
  - apply_sepcon_adjoint.
    elim_emp.
    destruct H as [H | H].
    + subst p.
      unfold listrep.
      Exists (@nil Z).
      normalize.
      simpl.
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial.
        reflexivity.
    + subst p.
      unfold listrep.
      Exists (@nil Z).
      normalize.
      simpl.
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial.
        reflexivity.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma sll_shape_strategy6_correctness : sll_shape_strategy6.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p H0.
  split_pure_spatial.
  - destruct H0 as [H0 | H0];
    subst p;
    sep_apply_l_atomic (listrep_zero 0 eq_refl);
    cancel.
  - dump_pre_spatial.
    exact H0.
Qed.

Lemma sll_shape_strategy14_correctness : sll_shape_strategy14.
Proof.
  pre_process_default.
  unfold lseg.
  Exists (@nil Z).
  normalize.
  cancel (listrep p).
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_shape_strategy15_correctness : sll_shape_strategy15.
Proof.
  pre_process_default.
  unfold lseg.
  Exists (@nil Z).
  normalize.
  cancel ((poly_store FET_int &(p # "list" ->ₛ "data") q) || (poly_store FET_ptr &(p # "list" ->ₛ "next") q)).
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_shape_strategy7_correctness : sll_shape_strategy7.
Proof.
  pre_process_default.
Qed.

Lemma sll_shape_strategy10_correctness : sll_shape_strategy10.
Proof.
  pre_process_default.
  sep_apply_l_atomic (lseg_listrep p q).
  cancel.
Qed.

Lemma sll_shape_strategy16_correctness : sll_shape_strategy16.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  split_pure_spatial.
  - cancel (&(q # "list" ->ₛ "next") # Ptr |-> z).
    Intros_r h.
    apply_sepcon_adjoint.
    elim_emp.
    sep_apply_l_atomic (lseg_len1 q h z).
    + dump_pre_spatial.
      destruct Hnz as [Hnz | Hnz].
      * exact Hnz.
      * intro Hq0.
        apply Hnz.
        symmetry.
        exact Hq0.
    + sep_apply_l_atomic (lseg_lseg p q z).
      cancel.
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma sll_shape_strategy8_correctness : sll_shape_strategy8.
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
  sep_apply_l_atomic (listrep_nonzero p Hp).
  Intros y.
  Intros x.
  Exists x.
  Exists y.
  normalize.
  rewrite <- logic_equiv_coq_prop_or.
  split_pure_spatial.
  - cancel (listrep y).
    cancel (&(p # "list" ->ₛ "next") # Ptr |-> y).
    cancel (&(p # "list" ->ₛ "data") # Int |-> x).
    Intros_r q.
    apply_sepcon_adjoint.
    elim_emp.
    cancel.
  - dump_pre_spatial.
    left.
    exact Hp.
Qed.

Lemma sll_shape_strategy9_correctness : sll_shape_strategy9.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  split_pure_spatial.
  - Intros_r x.
    Intros_r y.
    apply_sepcon_adjoint.
    elim_emp.
    unfold listrep.
    Intros l.
    Exists (x :: l).
    simpl.
    Exists y.
    split_pure_spatial.
    + cancel (&(p # "list" ->ₛ "data") # Int |-> x).
      cancel (&(p # "list" ->ₛ "next") # Ptr |-> y).
      cancel (sll y l).
    + dump_pre_spatial.
      destruct Hnz as [Hnz | Hnz].
      * exact Hnz.
      * intro Hp0.
        apply Hnz.
        symmetry.
        exact Hp0.
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma sll_shape_strategy11_correctness : sll_shape_strategy11.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  split_pure_spatial.
  - cancel ((poly_store FET_int &(p # "list" ->ₛ "data") q) || (poly_store FET_ptr &(p # "list" ->ₛ "next") q)).
    Intros_r x.
    Intros_r y.
    apply_sepcon_adjoint.
    elim_emp.
    unfold listrep.
    Intros l.
    Exists (x :: l).
    simpl.
    Exists y.
    split_pure_spatial.
    + cancel (&(p # "list" ->ₛ "data") # Int |-> x).
      cancel (&(p # "list" ->ₛ "next") # Ptr |-> y).
      cancel (sll y l).
    + dump_pre_spatial.
      destruct Hnz as [Hnz | Hnz].
      * exact Hnz.
      * intro Hp0.
        apply Hnz.
        symmetry.
        exact Hp0.
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma sll_shape_strategy17_correctness : sll_shape_strategy17.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  split_pure_spatial.
  - cancel (&(p # "list" ->ₛ "next") # Ptr |-> q).
    Intros_r x.
    Intros_r y.
    Intros_r z.
    apply_sepcon_adjoint.
    elim_emp.
    sep_apply_l_atomic (lseg_len1 p x y).
    + dump_pre_spatial.
      destruct Hnz as [Hnz | Hnz].
      * exact Hnz.
      * intro Hp0.
        apply Hnz.
        symmetry.
        exact Hp0.
    + sep_apply_l_atomic (lseg_lseg p y z).
      cancel.
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma sll_shape_strategy18_correctness : sll_shape_strategy18.
Proof.
  pre_process_default.
  sep_apply_l_atomic (lseg_lseg p q z).
  cancel.
Qed.

Lemma sll_shape_strategy19_correctness : sll_shape_strategy19.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  unfold lseg.
  Exists (@nil Z).
  normalize.
  split_pure_spatial.
  - simpl.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      reflexivity.
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma sll_shape_strategy20_correctness : sll_shape_strategy20.
Proof.
  pre_process_default.
  subst p q.
  unfold lseg.
  Exists (@nil Z).
  normalize.
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_shape_strategy21_correctness : sll_shape_strategy21.
Proof.
  pre_process_default.
  subst q.
  unfold listrep, lseg.
  Intros l.
  Exists l.
  revert p.
  induction l; intros p.
  - simpl. entailer!.
  - simpl. Intros y. Exists y. sep_apply IHl. entailer!.
Qed.

Lemma sll_shape_strategy23_correctness : sll_shape_strategy23.
Proof.
  pre_process_default.
  unfold lseg.
  Exists (@nil Z).
  normalize.
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_shape_strategy24_correctness : sll_shape_strategy24.
Proof.
  pre_process_default.
  subst p.
  unfold lseg.
  Intros l.
  destruct l as [| a l0].
  - simpl. Intros_p Hq. subst q. entailer!.
  - simpl. Intros z. contradiction.
Qed.

Lemma sll_shape_strategy25_correctness : sll_shape_strategy25.
Proof.
  pre_process_default.
  subst p.
  unfold lseg, listrep.
  Intros l.
  Intros l'.
  sep_apply (sllseg_sll q q l l').
  Exists (@app Z l l').
  entailer!.
Qed.

Lemma sll_shape_strategy22_correctness : sll_shape_strategy22.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hpq.
  Intros_p Hp.
  assert (Hpne : p <> q) by (destruct Hpq as [H | H]; [exact H | intro Hc; apply H; symmetry; exact Hc]).
  unfold lseg.
  Intros l.
  sep_apply (sllseg_unfold_head p q l Hpne).
  Intros a z l'.
  Exists a z.
  unfold lseg.
  Exists l'.
  rewrite <- logic_equiv_coq_prop_or.
  rewrite <- logic_equiv_coq_prop_or.
  normalize.
  split_pure_spatial.
  - cancel (&(p # "list" ->ₛ "data") # Int |-> a).
    cancel (&(p # "list" ->ₛ "next") # Ptr |-> z).
    cancel (sllseg z q l').
    Intros_r v.
    Intros_r n.
    apply_sepcon_adjoint.
    elim_emp.
    cancel.
  - entailer!.
Qed.
