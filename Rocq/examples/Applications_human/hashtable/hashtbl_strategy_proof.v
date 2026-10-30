From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_strategy_goal.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_lib.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string.

Lemma hashtbl_strategy0_correctness : hashtbl_strategy0.
Proof.
  pre_process_default.
  simpl. unfold hashtbl_strategy0. reflexivity.
Qed.

Lemma hashtbl_strategy1_correctness : hashtbl_strategy1.
Proof.
  pre_process_default.
  simpl. unfold hashtbl_strategy1. reflexivity.
Qed.

Lemma hashtbl_strategy2_correctness : hashtbl_strategy2.
Proof.
  pre_process_default.
  Intros.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy3_correctness : hashtbl_strategy3.
Proof.
  pre_process_default.
  Intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma hashtbl_strategy9_correctness : hashtbl_strategy9.
Proof.
  pre_process_default.
  Intros.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy10_correctness : hashtbl_strategy10.
Proof.
  pre_process_default.
  Intros.
  rewrite H.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy11_correctness : hashtbl_strategy11.
Proof.
  pre_process_default.
  Intros.
  rewrite H0.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy12_correctness : hashtbl_strategy12.
Proof.
  pre_process_default.
  Intros.
  rewrite H0.
  simpl.
  entailer!.
Qed.

Lemma hashtbl_strategy13_correctness : hashtbl_strategy13.
Proof.
  pre_process_default.
  entailer!.
  Intros_r l2.
  Intros_r v2.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  reflexivity.
Qed.
  
Lemma hashtbl_strategy14_correctness : hashtbl_strategy14.
Proof.
  pre_process_default.
  entailer!.
  Intros_r l2 r.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  reflexivity.
Qed.

Lemma hashtbl_strategy15_correctness : hashtbl_strategy15.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  assert (p = 0) by (destruct H; congruence).
  clear H.
  subst p.
  entailer!.
  Intros_r l.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  rewrite H.
  simpl sll.
  entailer!.
Qed.

Lemma hashtbl_strategy22_correctness : hashtbl_strategy22.
Proof.
  pre_process_default.
  Intros.
  rewrite H, H0.
  simpl dllseg.
  entailer!.
Qed.

Lemma hashtbl_strategy26_correctness : hashtbl_strategy26.
Proof.
  pre_process_default.
  Intros.
  subst l.
  unfold sllseg.
  entailer!.
Qed.

Lemma hashtbl_strategy27_correctness : hashtbl_strategy27.
Proof.
  pre_process_default.
  rewrite sll_zero.
  + Intros; easy.
  + entailer!.
Qed.

Lemma hashtbl_strategy16_correctness : hashtbl_strategy16.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  sep_apply (sll_not_zero p l).
  - Intros q l0.
    Exists p q l0.
    entailer!.
    rewrite <- logic_equiv_coq_prop_or.
    entailer!.
    cancel.
    rewrite <- derivable1_wand_sepcon_adjoint.
    entailer!.
  - assert (p <> 0) by (destruct H; congruence).
    unfold NULL.
    congruence.
Qed.


Lemma hashtbl_strategy17_correctness : hashtbl_strategy17.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Hnz.
  Intros_p Hnext.
  cbn [sll].
  Exists q.
  entailer!; unfold NULL in *; lia.
Qed.

Lemma hashtbl_strategy20_correctness : hashtbl_strategy20.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  assert (p <> 0) by (destruct H; congruence).
  clear H.
  sep_apply (dll_not_zero p up l); [ | unfold NULL; exact H0 ].
  Intros down l0.
  Exists down l0.
  rewrite <- logic_equiv_coq_prop_or.
  entailer!.
  cancel.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma hashtbl_strategy21_correctness : hashtbl_strategy21.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  assert (p <> 0) by (destruct H; congruence).
  clear H.
  Exists (p :: l0).
  rewrite <- logic_equiv_coq_prop_or.
  entailer!.
  simpl dll.
  unfold NULL.
  Exists down.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma hashtbl_strategy4_correctness : hashtbl_strategy4.
Proof.
  pre_process_default.
  Intros.
  subst.
  reflexivity.
Qed.

Lemma hashtbl_strategy24_correctness : hashtbl_strategy24.
Proof.
  pre_process_default.
  Intros.
  subst.
  reflexivity.
Qed.

Lemma hashtbl_strategy25_correctness : hashtbl_strategy25.
Proof.
  pre_process_default.
  revert p.
  induction l; simpl sll; simpl sllseg; intros.
  - entailer!.
  - Intros y.
    Exists y.
    sep_apply IHl.
    entailer!.
Qed.

Lemma hashtbl_strategy18_correctness : hashtbl_strategy18.
Proof.
  pre_process_default.
  Intros.
  subst.
  reflexivity.
Qed.

Lemma hashtbl_strategy7_correctness : hashtbl_strategy7.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  cbn [sll].
  Intros x0.
  Exists x0.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma hashtbl_strategy8_correctness : hashtbl_strategy8.
  pre_process_default.
Proof.
  cbn [sll].
  Intros.
  Exists y.
  entailer!.
Qed.

Lemma hashtbl_strategy23_correctness : hashtbl_strategy23.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  Intros.
  sep_apply (dllseg_head_neq x y x_up y_up l); [  | tauto ].
  Intros z l0.
  Exists z l0.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.
  

Lemma hashtbl_strategy5_correctness : hashtbl_strategy5.
Proof.
  pre_process_default.
  destruct l; simpl.
  + entailer!.
    rewrite <- logic_equiv_coq_prop_or.
    Intros.
    subst p.
    tauto.
  + Exists p l.
    Intros x.
    rewrite <- logic_equiv_coq_prop_or.
    Exists x.
    entailer!.
    apply sepcon_cancel_end; subst z.
    - entailer!.
      easy.
    - apply derivable1s_allp_r.
      intros.
      rewrite <- derivable1_wand_sepcon_adjoint.
      entailer!.
Qed.

Lemma hashtbl_strategy6_correctness : hashtbl_strategy6.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  apply sepcon_cancel_end; [entailer! | ].
  apply derivable1s_allp_r.
  intros.
  apply derivable1s_allp_r.
  intros.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.
