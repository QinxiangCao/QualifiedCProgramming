From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple2_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope sac.
Local Open Scope string.

Lemma swap_simple2_strategy0_correctness : swap_simple2_strategy0.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  unfold store_int_pair.
  cancel.
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p H.
  subst v.
  cancel.
Qed.

Lemma swap_simple2_strategy1_correctness : swap_simple2_strategy1.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  unfold store_int_pair.
  cancel.
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p H.
  subst v.
  cancel.
Qed.

Lemma swap_simple2_strategy2_correctness : swap_simple2_strategy2.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  unfold store_int_pair.
  cancel.
  apply_sepcon_adjoint.
  cancel.
  sep_apply store_int_undef_store_int.
  cancel.
Qed.

Lemma swap_simple2_strategy3_correctness : swap_simple2_strategy3.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  unfold store_int_pair.
  cancel.
  apply_sepcon_adjoint.
  cancel.
  sep_apply store_int_undef_store_int.
  cancel.
Qed.
