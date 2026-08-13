Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple5_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.int_pair_additional_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma swap_simple5_strategy0_correctness : swap_simple5_strategy0.
Proof.
  pre_process_default.
  unfold store_int_pair.
  unfold store_int_pair_y_only.
  cancel.
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p H.
  subst v.
  cancel.
Qed.

Lemma swap_simple5_strategy1_correctness : swap_simple5_strategy1.
Proof.
  pre_process_default.
  unfold store_int_pair.
  unfold store_int_pair_x_only.
  cancel.
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p H.
  subst v.
  cancel.
Qed.

Lemma swap_simple5_strategy2_correctness : swap_simple5_strategy2.
Proof.
  pre_process_default.
  unfold store_int_pair.
  unfold store_int_pair_y_only.
  cancel.
  apply_sepcon_adjoint.
  elim_emp.
  apply store_int_undef_store_int.
Qed.

Lemma swap_simple5_strategy3_correctness : swap_simple5_strategy3.
Proof.
  pre_process_default.
  unfold store_int_pair.
  unfold store_int_pair_x_only.
  cancel.
  apply_sepcon_adjoint.
  elim_emp.
  apply store_int_undef_store_int.
Qed.

Lemma swap_simple5_strategy4_correctness : swap_simple5_strategy4.
Proof.
  pre_process_default.
Qed.

Lemma swap_simple5_strategy5_correctness : swap_simple5_strategy5.
Proof.
  pre_process_default.
  unfold store_int_pair.
  unfold store_int_pair_x_only.
  cancel.
Qed.

Lemma swap_simple5_strategy6_correctness : swap_simple5_strategy6.
Proof.
  pre_process_default.
Qed.

Lemma swap_simple5_strategy7_correctness : swap_simple5_strategy7.
Proof.
  pre_process_default.
Qed.
