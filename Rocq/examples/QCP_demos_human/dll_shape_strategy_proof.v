Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import dll_shape_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import dll_shape_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma dll_shape_strategy1_correctness : dll_shape_strategy1.
  pre_process_default.
  sep_apply dlistrep_zero.
  - entailer!.
  - unfold NULL. lia.
Qed.

Lemma dll_shape_strategy2_correctness : dll_shape_strategy2.
  pre_process_default.
  Exists nil.
  simpl. entailer!.
Qed.

Lemma dll_shape_strategy3_correctness : dll_shape_strategy3.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p = 0) (0 = p)).
  Intros.
  entailer!.
  Intros_r x.
  rewrite <- derivable1_wand_sepcon_adjoint.
  destruct H ; subst ; Exists nil ; simpl; entailer!.
Qed.

Lemma dll_shape_strategy4_correctness : dll_shape_strategy4.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p = 0) (0 = p)).
  Intros.
  sep_apply dlistrep_zero.
  - entailer!.
  - destruct H ; auto.
Qed.

Lemma dll_shape_strategy12_correctness : dll_shape_strategy12.
  pre_process_default.
  Intros.
  subst. entailer!.
  Exists nil. simpl. entailer!.
Qed.

Lemma dll_shape_strategy7_correctness : dll_shape_strategy7.
  pre_process_default.
  subst.
  sep_apply dllseg_dlistrep_shape. entailer!.
Qed.


Lemma dll_shape_strategy13_correctness : dll_shape_strategy13.
  pre_process_default.
  entailer!. Intros_r x p. Intros_r y q.
  subst.
  rewrite <- derivable1_wand_sepcon_adjoint.
  sep_apply dllseg_shape_len1 ; auto.
  sep_apply (dllseg_dllseg_shape p s n q y s). entailer!.
Qed.

Lemma dll_shape_strategy14_correctness : dll_shape_strategy14.
  pre_process_default.
  sep_apply dllseg_split_tail ; try lia. 
  Intros z a. 
  Exists a z.
  entailer!. 
  Intros_r n. 
  rewrite <- derivable1_wand_sepcon_adjoint. 
  entailer!.
Qed.

Lemma dll_shape_strategy8_correctness : dll_shape_strategy8.
  pre_process_default.
  Intros. subst. entailer!.
Qed.

Lemma dll_shape_strategy11_correctness : dll_shape_strategy11.
  pre_process_default.
  subst. Exists nil. simpl. entailer!.
Qed.

Lemma dll_shape_strategy15_correctness : dll_shape_strategy15.
  pre_process_default.
  subst.
  sep_apply dllseg_dlistrep_shape. entailer!. 
Qed.

Lemma dll_shape_strategy5_correctness : dll_shape_strategy5.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  Intros.
  assert (p <> 0) by (destruct H ; auto).
  sep_apply dlistrep_not_zero ; unfold NULL ; try auto.
  Intros v y.
  Exists v y. entailer!.
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  entailer!. Intros_r q.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma dll_shape_strategy6_correctness : dll_shape_strategy6.
  pre_process_default.
  rewrite <- (logic_equiv_coq_prop_or (p <> 0) (0 <> p)).
  Intros. entailer!.
  Intros_r prev x.
  Intros_r y. 
  rewrite <- derivable1_wand_sepcon_adjoint.
  assert (p <> 0) by (destruct H ; auto).
  sep_apply dllseg_shape_len1 ; try (unfold NULL ; auto).
  sep_apply dllseg_dlistrep_shape. entailer!.
Qed.

Lemma dll_shape_strategy16_correctness : dll_shape_strategy16.
  pre_process_default.
  sep_apply dllseg_split_tail' ; try lia.
  Intros z a. 
  Exists a z.
  entailer!. 
  Intros_r n. 
  rewrite <- derivable1_wand_sepcon_adjoint. 
  entailer!.
Qed.