Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import common_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma common_strategy0_correctness : common_strategy0.
  pre_process_default.
Qed.

Lemma common_strategy1_correctness : common_strategy1.
  pre_process_default.
Qed.

Lemma common_strategy6_correctness : common_strategy6.
Proof.
  pre_process_default.
  unfold should_be_equal.
  normalize.
  apply split_pure_and_spatial_goals.
  - cancel.
    apply_sepcon_adjoint.
    Intros_p H.
    cancel.
  - dump_pre_spatial.
    exact I.
Qed.

Lemma common_strategy3_correctness : common_strategy3.
  pre_process_default.
Qed.

Lemma common_strategy7_correctness : common_strategy7.
  pre_process_default.
Qed.

Lemma common_strategy8_correctness : common_strategy8.
Proof.
  pre_process_default.
  Intros_p H.
  subst y.
  split_pure_spatial.
  2: {
    dump_pre_spatial.
    reflexivity.
  }
  cancel.
Qed.

Lemma common_strategy9_correctness : common_strategy9.
  pre_process_default.
  apply poly_store_poly_undef_store.
Qed.

Lemma common_strategy10_correctness : common_strategy10.
  pre_process_default.
Qed.

Lemma common_strategy11_correctness : common_strategy11.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p H.
  destruct H as [H | H].
  - subst q.
    split_pure_spatial.
    + Intros_r y.
      apply_sepcon_adjoint.
      Intros_p Hxy.
      subst y.
      cancel.
    + dump_pre_spatial.
      tauto.
  - subst p.
    split_pure_spatial.
    + Intros_r y.
      apply_sepcon_adjoint.
      Intros_p Hxy.
      subst y.
      cancel.
    + dump_pre_spatial.
      tauto.
Qed.

Lemma common_strategy12_correctness : common_strategy12.
Proof.
  pre_process_default.
Qed.

Lemma common_strategy13_correctness : common_strategy13.
Proof. 
  pre_process_default.
Qed.

Lemma common_strategy14_correctness : common_strategy14.
Proof.
  pre_process_default.
  apply poly_store_poly_undef_store.
Qed.

Lemma common_strategy15_correctness : common_strategy15.
Proof.
  pre_process_default.
  unfold dup_data_at_error_prop.
  split_pures.
  cancel.
  apply_sepcon_adjoint.
  unfold dup_data_at_error.
  Intros_p Hfalse.
  contradiction.
Qed.

Lemma common_strategy16_correctness : common_strategy16.
Proof.
  pre_process_default.
  unfold dup_data_at_error_prop.
  split_pures.
  cancel.
  apply_sepcon_adjoint.
  unfold dup_data_at_error.
  Intros_p Hfalse.
  contradiction.
Qed.

Lemma common_strategy17_correctness : common_strategy17.
Proof.
  pre_process_default.
  unfold dup_data_at_error_prop.
  split_pures.
  cancel.
  apply_sepcon_adjoint.
  unfold dup_data_at_error.
  Intros_p Hfalse.
  contradiction.
Qed.

Lemma common_strategy18_correctness : common_strategy18.
Proof.
  pre_process_default.
Qed.

Lemma common_strategy19_correctness : common_strategy19.
Proof.
  pre_process_default.
  prop_apply (valid_store_int p).
  Intros.
  split_pure_spatial.
  2: {
    dump_pre_spatial.
    replace Int.min_signed with (-2147483648) in H by reflexivity.
    lia.
  }
  cancel.
Qed.

Lemma common_strategy20_correctness : common_strategy20.
Proof.
  pre_process_default.
  prop_apply (valid_store_int p).
  Intros.
  split_pure_spatial.
  2: {
    dump_pre_spatial.
    destruct H as [[_ Hmax] _].
    exact Hmax.
  }
  cancel.
Qed.

Lemma common_strategy21_correctness : common_strategy21.
Proof.
  pre_process_default.
  prop_apply (valid_store_uint p).
  Intros.
  split_pure_spatial.
  2: {
    dump_pre_spatial.
    destruct H as [[Hmin _] _].
    lia.
  }
  cancel.
Qed.

Lemma common_strategy22_correctness : common_strategy22.
Proof.
  pre_process_default.
  prop_apply (valid_store_uint p).
  Intros.
  split_pure_spatial.
  2: {
    dump_pre_spatial.
    destruct H as [[_ Hmax] _].
    exact Hmax.
  }
  cancel.
Qed.

Lemma common_strategy23_correctness : common_strategy23.
Proof.
  pre_process_default.
  split_pure_spatial.
  2: {
    dump_pre_spatial.
    pose proof (unsigned_Lastnbits_range x n H).
    lia.
  }
  cancel.
Qed.
