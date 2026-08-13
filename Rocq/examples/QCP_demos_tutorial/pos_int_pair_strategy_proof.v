Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_tutorial Require Import pos_int_pair_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.pos_int_pair_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma pos_int_pair_strategy0_correctness : pos_int_pair_strategy0.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  unfold store_pos_int_pair_y_only.
  entailer!.
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p Hv.
  subst v.
  cancel.
Qed.

Lemma pos_int_pair_strategy1_correctness : pos_int_pair_strategy1.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  unfold store_pos_int_pair_x_only.
  entailer!.
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p Hv.
  subst v.
  cancel.
Qed.

Lemma pos_int_pair_strategy2_correctness : pos_int_pair_strategy2.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  unfold store_pos_int_pair_y_only.
  entailer!.
  apply_sepcon_adjoint.
  elim_emp.
  apply store_int_undef_store_int.
Qed.

Lemma pos_int_pair_strategy3_correctness : pos_int_pair_strategy3.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  unfold store_pos_int_pair_x_only.
  entailer!.
  apply_sepcon_adjoint.
  elim_emp.
  apply store_int_undef_store_int.
Qed.

Lemma pos_int_pair_strategy4_correctness : pos_int_pair_strategy4.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  unfold store_pos_int_pair_y_only.
  entailer!.
Qed.

Lemma pos_int_pair_strategy6_correctness : pos_int_pair_strategy6.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  unfold store_pos_int_pair_x_only.
  entailer!.
Qed.

Lemma pos_int_pair_strategy8_correctness : pos_int_pair_strategy8.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  entailer!.
Qed.

Lemma pos_int_pair_strategy9_correctness : pos_int_pair_strategy9.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  entailer!.
Qed.

Lemma pos_int_pair_strategy10_correctness : pos_int_pair_strategy10.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  entailer!.
Qed.

Lemma pos_int_pair_strategy11_correctness : pos_int_pair_strategy11.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  entailer!.
Qed.

Lemma pos_int_pair_strategy12_correctness : pos_int_pair_strategy12.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  Intros_p Hx_nonneg.
  Intros_p Hy_nonneg.
  prop_apply (store_int_range (&(p # "int_pair" ->ₛ "a")) x).
  entailer!.
Qed.

Lemma pos_int_pair_strategy13_correctness : pos_int_pair_strategy13.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  Intros_p Hx_nonneg.
  Intros_p Hy_nonneg.
  prop_apply (store_int_range (&(p # "int_pair" ->ₛ "b")) y).
  entailer!.
Qed.

Lemma pos_int_pair_strategy5_correctness : pos_int_pair_strategy5.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  unfold store_pos_int_pair_y_only.
  entailer!.
Qed.

Lemma pos_int_pair_strategy7_correctness : pos_int_pair_strategy7.
Proof.
  pre_process_default.
  unfold store_pos_int_pair.
  unfold store_pos_int_pair_x_only.
  entailer!.
Qed.
