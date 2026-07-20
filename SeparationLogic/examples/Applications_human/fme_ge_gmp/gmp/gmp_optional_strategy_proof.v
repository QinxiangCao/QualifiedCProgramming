Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma gmp_optional_strategy1_correctness : gmp_optional_strategy1.
Proof.
  unfold gmp_optional_strategy1.
  pre_process_default.
  unfold optional_store_Z.
  Split.
  - Intros_p Hnull. entailer!.
  - Intros_p Hnonnull. entailer!.
Qed.

Lemma gmp_optional_strategy2_correctness : gmp_optional_strategy2.
Proof.
  unfold gmp_optional_strategy2.
  pre_process_default.
  split_pure_spatial.
  - Intros_r z.
    apply_sepcon_adjoint.
    unfold optional_store_Z.
    Right.
    entailer!.
  - entailer!.
Qed.

Lemma gmp_optional_strategy3_correctness : gmp_optional_strategy3.
Proof.
  unfold gmp_optional_strategy3.
  pre_process_default.
  unfold optional_store_Z.
  Split.
  - Intros_p Hnull. entailer!.
  - Intros_p Hnonnull. entailer!.
Qed.

Lemma gmp_optional_strategy4_correctness : gmp_optional_strategy4.
Proof.
  unfold gmp_optional_strategy4.
  pre_process_default.
  split_pure_spatial.
  - Intros_r z.
    apply_sepcon_adjoint.
    unfold optional_store_Z.
    Left.
    entailer!.
  - entailer!.
Qed.

Lemma gmp_optional_strategy5_correctness : gmp_optional_strategy5.
Proof.
  unfold gmp_optional_strategy5.
  pre_process_default.
  unfold optional_q_undef.
  Split.
  - Intros_p Hnull. entailer!.
  - Intros_p Hnonnull. entailer!.
Qed.

Lemma gmp_optional_strategy6_correctness : gmp_optional_strategy6.
Proof.
  unfold gmp_optional_strategy6.
  pre_process_default.
  split_pure_spatial.
  - Intros_r n.
    apply_sepcon_adjoint.
    unfold optional_q_undef.
    Right.
    entailer!.
  - entailer!.
Qed.

Lemma gmp_optional_strategy7_correctness : gmp_optional_strategy7.
Proof.
  unfold gmp_optional_strategy7.
  pre_process_default.
  unfold optional_q_undef.
  Split.
  - Intros_p Hnull. entailer!.
  - Intros_p Hnonnull. entailer!.
Qed.

Lemma gmp_optional_strategy8_correctness : gmp_optional_strategy8.
Proof.
  unfold gmp_optional_strategy8.
  pre_process_default.
  split_pure_spatial.
  - Intros_r n.
    apply_sepcon_adjoint.
    unfold optional_q_undef.
    Left.
    entailer!.
  - entailer!.
Qed.

Lemma gmp_optional_strategy9_correctness : gmp_optional_strategy9.
Proof.
  unfold gmp_optional_strategy9.
  pre_process_default.
  unfold optional_q_full.
  Split.
  - Intros_p Hnull. entailer!.
  - Intros_p Hnonnull. entailer!.
Qed.

Lemma gmp_optional_strategy10_correctness : gmp_optional_strategy10.
Proof.
  unfold gmp_optional_strategy10.
  pre_process_default.
  split_pure_spatial.
  - Intros_r l.
    Intros_r n.
    apply_sepcon_adjoint.
    unfold optional_q_full.
    Right.
    entailer!.
  - entailer!.
Qed.

Lemma gmp_optional_strategy11_correctness : gmp_optional_strategy11.
Proof.
  unfold gmp_optional_strategy11.
  pre_process_default.
  unfold optional_q_full.
  Split.
  - Intros_p Hnull. entailer!.
  - Intros_p Hnonnull. entailer!.
Qed.

Lemma gmp_optional_strategy12_correctness : gmp_optional_strategy12.
Proof.
  unfold gmp_optional_strategy12.
  pre_process_default.
  split_pure_spatial.
  - Intros_r l.
    Intros_r n.
    apply_sepcon_adjoint.
    unfold optional_q_full.
    Left.
    entailer!.
  - entailer!.
Qed.
