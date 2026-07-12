Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple3_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma swap_simple3_strategy0_correctness : swap_simple3_strategy0.
Proof.
  pre_process_default.
  unfold store_int_pair.
  cancel.
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p H.
  subst v.
  cancel.
Qed.

Lemma swap_simple3_strategy1_correctness : swap_simple3_strategy1.
Proof.
  pre_process_default.
  unfold store_int_pair.
  cancel.
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p H.
  subst v.
  cancel.
Qed.

Lemma swap_simple3_strategy2_correctness : swap_simple3_strategy2.
Proof.
  pre_process_default.
  unfold store_int_pair.
  cancel.
  apply_sepcon_adjoint.
  elim_emp.
  apply store_int_undef_store_int.
Qed.

Lemma swap_simple3_strategy3_correctness : swap_simple3_strategy3.
Proof.
  pre_process_default.
  unfold store_int_pair.
  cancel.
  apply_sepcon_adjoint.
  elim_emp.
  apply store_int_undef_store_int.
Qed.

Lemma swap_simple3_strategy4_correctness : swap_simple3_strategy4.
Proof.
  pre_process_default.
Qed.
