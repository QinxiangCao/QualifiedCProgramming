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
  LLM_pre_process ltac:(lia).
  split_pure_spatial.
  - cancel (&( x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size).
    cancel (&( x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap).
    cancel (&( x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr).
    cancel (mpd_store_Z_compact_read0 ptr (Zabs n) (Zabs size)).
    cancel (UIntArray.undef_seg ptr (Zmax (Zabs size) 1) cap).
    Intros_r y.
    apply_sepcon_adjoint.
    normalize.
    Split.
    + Split.
      * Left; Left.
        cancel.
      * Left; Right.
        cancel.
    + Right.
      cancel.
  - split_pures.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
Qed.

Lemma mpz_tdiv_r_read0_strategy2_correctness : mpz_tdiv_r_read0_strategy2.
Proof.
  unfold mpz_tdiv_r_read0_strategy2.
  pre_process_default.
  apply sepcon_cancel_res_emp.
  Intros_r size n cap ptr.
  apply_sepcon_adjoint.
  Intros_p Hcap.
  Intros_p Hsign.
  unfold store_Z_read0.
  Exists ptr size cap.
  LLM_pre_process ltac:(lia).
Qed.
