Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import sll_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sll_strategy3_correctness : sll_strategy3.
  pre_process_default.
  simpl sll.
  entailer!.
Qed.

Lemma sll_strategy4_correctness : sll_strategy4.
  pre_process_default.
  simpl sll.
  entailer!.
Qed.

Lemma sll_strategy5_correctness : sll_strategy5.
  pre_process_default.
  entailer!.
  subst; simpl.
  entailer!.
Qed.

Lemma sll_strategy6_correctness : sll_strategy6.
  pre_process_default.
  Intros.
  subst.
  entailer!.
Qed.

Lemma sll_strategy14_correctness : sll_strategy14.
  pre_process_default.
  Intros.
  subst.
  simpl.
  entailer!.
Qed.

Lemma sll_strategy15_correctness : sll_strategy15.  
  pre_process_default.
  Intros; subst; simpl; entailer!.
Qed.

Lemma sll_strategy16_correctness : sll_strategy16.
  pre_process_default.
  Intros; subst; simpl; entailer!.
Qed.

Lemma sll_strategy17_correctness : sll_strategy17.
  pre_process_default.
  Intros; subst; simpl; entailer!.
Qed.

Lemma sll_strategy18_correctness : sll_strategy18.
  pre_process_default.
  entailer!.
  Intros_r l2.
  Intros_r v0.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma sll_strategy19_correctness : sll_strategy19.
  pre_process_default.
  entailer!.
  Intros_r l2.
  Intros_r r.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma sll_strategy20_correctness : sll_strategy20.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  assert (p = 0) by (destruct H;congruence).
  clear H.
  subst p.
  entailer!.
  Intros_r_any.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst x.
  cbn [sll].
  entailer!.
Qed.

Lemma sll_strategy21_correctness : sll_strategy21.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  assert (p <> 0) by (destruct H; congruence).
  sep_apply sll_not_zero; [ | tauto].
  Intros y a l0.
  Exists a y l0.
  rewrite <- logic_equiv_coq_prop_or.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma sll_strategy22_correctness : sll_strategy22.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  assert (p <> 0) by (destruct H; congruence).
  Exists (d :: l0).
  rewrite <- logic_equiv_coq_prop_or.
  entailer!.
  cbn [sll].
  Exists q.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma sll_strategy7_correctness : sll_strategy7.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma sll_strategy10_correctness : sll_strategy10.
  pre_process_default.
  simpl.
  Intros y.
  Exists y.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma sll_strategy11_correctness : sll_strategy11.
  pre_process_default.
  simpl.
  Exists y.
  entailer!.
Qed.

Lemma sll_strategy8_correctness : sll_strategy8.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  Intros.
  sep_apply (sll_not_zero p); [ | destruct H; intuition].
  Intros y a l0.
  Exists a l0.
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  entailer!.
  simpl.
  Exists y.
  entailer!.
  Intros_r x.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma sll_strategy9_correctness : sll_strategy9.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  entailer!.
  Intros_r l.
  Intros_r x.
  Intros_r l0.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.


