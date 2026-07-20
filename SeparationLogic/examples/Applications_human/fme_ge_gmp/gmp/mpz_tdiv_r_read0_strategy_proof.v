Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma mpz_tdiv_r_read0_strategy3_correctness : mpz_tdiv_r_read0_strategy3.
Proof.
  pre_process_default.
  Intros_p Hv.
  Intros_p Hs.
  subst.
  cancel.
Qed.

Lemma mpz_tdiv_r_read0_strategy1_correctness : mpz_tdiv_r_read0_strategy1.
Proof.
  unfold mpz_tdiv_r_read0_strategy1.
  pre_process_default.
  unfold store_Z_read0.
  Intros ptr size cap.
  Exists ptr size cap.
  entailer!.
  Intros_r y.
  apply_sepcon_adjoint.
  cancel.
  entailer!.
Qed.

Lemma mpz_tdiv_r_read0_strategy2_correctness : mpz_tdiv_r_read0_strategy2.
Proof.
  unfold mpz_tdiv_r_read0_strategy2.
  pre_process_default.
  apply sepcon_cancel_res_emp.
  Intros_r size n cap ptr.
  apply_sepcon_adjoint.
  pre_process_default.
  unfold store_Z_read0.
  Exists ptr size cap.
  entailer!.
Qed.
