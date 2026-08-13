Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import sll_shape_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import sll_shape_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sll_shape_strategy3_correctness : sll_shape_strategy3.
Proof.
  pre_process_default.
  sep_apply listrep_zero; auto.
  entailer!.
Qed.

Lemma sll_shape_strategy4_correctness : sll_shape_strategy4.
Proof.  
  pre_process_default.
  unfold listrep. Exists nil.
  simpl sll. entailer!.
Qed.

Lemma sll_shape_strategy5_correctness : sll_shape_strategy5.
Proof.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p = 0) (0 = p)).
  Intros.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  destruct H ; subst ; unfold listrep ; Exists nil ; simpl sll ;entailer!. 
Qed.

Lemma sll_shape_strategy6_correctness : sll_shape_strategy6.
Proof.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p = 0) (0 = p)).
  Intros.
  sep_apply listrep_zero.
  - entailer!.
  - destruct H ; auto.
Qed.

Lemma sll_shape_strategy14_correctness : sll_shape_strategy14.
Proof.
  pre_process_default.
  entailer!.
  unfold lseg. Exists nil. simpl sllseg. entailer!.
Qed.

Lemma sll_shape_strategy15_correctness : sll_shape_strategy15.
Proof.
  pre_process_default.
  entailer!.
  unfold lseg. Exists nil. simpl sllseg. Split ; [Left | Right] ; entailer!.
Qed.

Lemma sll_shape_strategy7_correctness : sll_shape_strategy7.
Proof.
  pre_process_default.
Qed.

Lemma sll_shape_strategy10_correctness : sll_shape_strategy10.
Proof.
  pre_process_default.
  sep_apply lseg_listrep. entailer!.
Qed.

Lemma sll_shape_strategy16_correctness : sll_shape_strategy16.
Proof.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (q <> 0) (0 <> q)).
  Intros. entailer!.
  pre_process_default.
  sep_apply (lseg_len1 q h z).
  - sep_apply (lseg_lseg p q z). entailer!.
  - destruct H ; auto.
Qed.

Lemma sll_shape_strategy8_correctness : sll_shape_strategy8.
Proof.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  Intros. 
  assert (p <> 0) by (destruct H; auto). 
  sep_apply (listrep_nonzero p) ; auto.
  Intros y a.
  Exists a y. entailer!.
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  entailer!.
  pre_process_default.
Qed.

Lemma sll_shape_strategy9_correctness : sll_shape_strategy9.
Proof.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  Intros.
  assert (p <> 0) by (destruct H; auto).
  entailer!.
  pre_process_default.
  sep_apply (lseg_len1 p) ; auto.
  sep_apply lseg_listrep. entailer!.
Qed. 

Lemma sll_shape_strategy11_correctness : sll_shape_strategy11.
Proof.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  Intros.
  assert (p <> 0) by (destruct H; auto).
  Split ; [Left | Right] ; entailer!;
  pre_process_default;
  sep_apply (lseg_len1 p) ; auto;
  sep_apply lseg_listrep; entailer!.
Qed.

Lemma sll_shape_strategy17_correctness : sll_shape_strategy17.
Proof.
  pre_process_default. 
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  Intros.
  assert (p <> 0) by (destruct H; auto).
  entailer!.
  pre_process_default.
  sep_apply (lseg_len1 p); auto.
  sep_apply lseg_lseg. entailer!.
Qed.

Lemma sll_shape_strategy18_correctness : sll_shape_strategy18.
Proof.
  pre_process_default.
  sep_apply lseg_lseg.
  entailer!.
Qed.

Lemma sll_shape_strategy19_correctness : sll_shape_strategy19.
Proof.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  Intros.
  assert (p <> 0) by (destruct H; auto).
  entailer!.
  unfold lseg. Exists nil. simpl sllseg. entailer!.
Qed.

Lemma sll_shape_strategy20_correctness : sll_shape_strategy20.
Proof.
  pre_process_default.
  subst.
  unfold lseg. Exists nil. simpl. entailer!.
Qed.