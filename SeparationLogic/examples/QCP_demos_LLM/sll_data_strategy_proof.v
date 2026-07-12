Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import sll_data_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sll_data_strategy3_correctness : sll_data_strategy3.
Proof.
  pre_process_default.
  sep_apply (sll_zero 0 l eq_refl).
  entailer!.
Qed.

Lemma sll_data_strategy4_correctness : sll_data_strategy4.
Proof.
  pre_process_default.
  Intros_p Hl.
  subst l.
  simpl.
  entailer!.
Qed.

Lemma sll_data_strategy5_correctness : sll_data_strategy5.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p H.
  split_pure_spatial.
  - Intros_r l.
    apply_sepcon_adjoint.
    Intros_p Hl.
    subst l.
    simpl.
    destruct H as [H | H]; subst p; entailer!.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma sll_data_strategy6_correctness : sll_data_strategy6.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p H.
  assert (Hp : p = 0) by (destruct H; lia).
  sep_apply (sll_zero p l Hp).
  entailer!.
Qed.

Lemma sll_data_strategy7_correctness : sll_data_strategy7.
Proof.
  pre_process_default.
  Intros_p Hl.
  subst l2.
  cancel.
Qed.

Lemma sll_data_strategy8_correctness : sll_data_strategy8.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  assert (Hp : p <> 0) by (destruct Hnz as [H | H]; [exact H | intro Hc; apply H; symmetry; exact Hc]).
  sep_apply (sll_not_zero p l Hp).
  Intros y a l0.
  Exists a y l0.
  rewrite <- logic_equiv_coq_prop_or.
  split_pure_spatial.
  - cancel (&(p # "list" ->ₛ "data") # Int |-> a).
    cancel (&(p # "list" ->ₛ "next") # Ptr |-> y).
    cancel (sll y l0).
    Intros_r q.
    apply_sepcon_adjoint.
    elim_emp.
    cancel.
  - entailer!.
Qed.

Lemma sll_data_strategy9_correctness : sll_data_strategy9.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  split_pure_spatial.
  - Intros_r l x l0 y.
    apply_sepcon_adjoint.
    Intros_p Hl.
    subst l.
    simpl.
    Exists y.
    split_pure_spatial.
    + cancel.
      cancel.
    + dump_pre_spatial.
      destruct Hnz as [H | H]; [exact H | intro Hc; apply H; symmetry; exact Hc].
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma sll_data_strategy10_correctness : sll_data_strategy10.
Proof.
  pre_process_default.
  Intros_p Hl2.
  subst l2.
  sep_apply (sllseg_sll p q l1 l3).
  cancel.
Qed.

Lemma sll_data_strategy11_correctness : sll_data_strategy11.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  split_pure_spatial.
  - cancel ((poly_store FET_int &(p # "list" ->ₛ "data") q) || (poly_store FET_ptr &(p # "list" ->ₛ "next") q)).
    Intros_r l x l0 y.
    apply_sepcon_adjoint.
    Intros_p Hl.
    subst l.
    simpl.
    Exists y.
    split_pure_spatial.
    + cancel.
      cancel.
    + dump_pre_spatial.
      destruct Hnz as [H | H]; [exact H | intro Hc; apply H; symmetry; exact Hc].
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma sll_data_strategy14_correctness : sll_data_strategy14.
Proof.
  pre_process_default.
  Intros_p Hl.
  subst l.
  simpl.
  entailer!.
Qed.

Lemma sll_data_strategy15_correctness : sll_data_strategy15.
Proof.
  pre_process_default.
  Intros_p Hl.
  subst l.
  simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma sll_data_strategy16_correctness : sll_data_strategy16.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  assert (Hq : q <> 0) by (destruct Hnz as [H | H]; [exact H | intro Hc; apply H; symmetry; exact Hc]).
  split_pure_spatial.
  - Intros_r l2 h.
    apply_sepcon_adjoint.
    Intros_p Hl2.
    subst l2.
    sep_apply (sllseg_len1 q h z Hq).
    sep_apply (sllseg_sllseg p q z l1 (h :: nil)).
    cancel.
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma sll_data_strategy17_correctness : sll_data_strategy17.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  assert (Hp : p <> 0) by (destruct Hnz as [H | H]; [exact H | intro Hc; apply H; symmetry; exact Hc]).
  split_pure_spatial.
  - cancel (&(p # "list" ->ₛ "next") # Ptr |-> q).
    Intros_r l x l0 y z.
    apply_sepcon_adjoint.
    Intros_p Hl.
    subst l.
    sep_apply (sllseg_len1 p x y Hp).
    sep_apply (sllseg_sllseg p y z (x :: nil) l0).
    simpl ((x :: nil) ++ l0)%list.
    cancel.
  - dump_pre_spatial.
    exact Hnz.
Qed.

Lemma sll_data_strategy18_correctness : sll_data_strategy18.
Proof.
  pre_process_default.
  Intros_p Hl2.
  subst l2.
  sep_apply (sllseg_sllseg p q z l1 l3).
  cancel.
Qed.

Lemma sll_data_strategy19_correctness : sll_data_strategy19.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  Intros_p Hl.
  subst l.
  simpl.
  entailer!.
Qed.

Lemma sll_data_strategy20_correctness : sll_data_strategy20.
Proof.
  pre_process_default.
  Intros_p Hl.
  subst l.
  subst p.
  subst q.
  simpl.
  entailer!.
Qed.

Lemma sll_data_strategy21_correctness : sll_data_strategy21.
Proof.
  pre_process_default.
  Intros_p Hl.
  subst l2.
  subst q.
  revert p.
  induction l1; intros p.
  - simpl. entailer!.
  - simpl. Intros y. Exists y. sep_apply IHl1. entailer!.
Qed.

Lemma sll_data_strategy23_correctness : sll_data_strategy23.
Proof.
  pre_process_default.
  Intros_p Hl.
  subst l.
  simpl.
  entailer!.
Qed.

Lemma sll_data_strategy24_correctness : sll_data_strategy24.
Proof.
  pre_process_default.
  subst p.
  destruct l as [| a l0].
  - simpl. Intros_p Hq. subst q. entailer!.
  - simpl. Intros z. contradiction.
Qed.

Lemma sll_data_strategy25_correctness : sll_data_strategy25.
Proof.
  pre_process_default.
  subst p.
  Exists (@app Z l1 l2).
  sep_apply (sllseg_sll q q l1 l2).
  entailer!.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
Qed.

Lemma sll_data_strategy22_correctness : sll_data_strategy22.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hpq.
  Intros_p Hp.
  assert (Hpne : p <> q) by (destruct Hpq as [H | H]; [exact H | intro Hc; apply H; symmetry; exact Hc]).
  sep_apply (sllseg_unfold_head p q l Hpne).
  Intros a z l0.
  Exists a z l0.
  rewrite <- logic_equiv_coq_prop_or.
  rewrite <- logic_equiv_coq_prop_or.
  normalize.
  split_pure_spatial.
  - cancel (&(p # "list" ->ₛ "data") # Int |-> a).
    cancel (&(p # "list" ->ₛ "next") # Ptr |-> z).
    cancel (sllseg z q l0).
    Intros_r v.
    Intros_r n.
    apply_sepcon_adjoint.
    elim_emp.
    cancel.
  - entailer!.
Qed.
