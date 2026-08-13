Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import ge_gmp_array_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma ge_gmp_array_strategy201_correctness : ge_gmp_array_strategy201.
Proof.
  pre_process_default.
  sep_apply_l_atomic (mpz_array_split p i n l 0).
  - dump_pre_spatial.
    lia.
  - unfold mpz_store.
    cancel (mpz_missing_i p i 0 n l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p Hv.
    subst v.
    unfold mpz_sizeof.
    cancel.
Qed.

Lemma ge_gmp_array_strategy206_correctness : ge_gmp_array_strategy206.
Proof.
  pre_process_default.
  change
    (store_Z (p + i * sizeof ("__mpz_struct")) (Znth i l 0))
    with (mpz_store p i (Znth i l 0)).
  sep_apply_l_atomic (mpz_array_merge p i n (Znth i l 0) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma ge_gmp_array_strategy204_correctness : ge_gmp_array_strategy204.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  cancel.
Qed.

Lemma ge_gmp_array_strategy205_correctness : ge_gmp_array_strategy205.
Proof.
  pre_process_default.
Qed.

Lemma ge_gmp_array_strategy202_correctness : ge_gmp_array_strategy202.
Proof.
  pre_process_default.
  change
    (store_Z (p + i * sizeof ("__mpz_struct")) (Znth i l 0))
    with (mpz_store p i (Znth i l 0)).
  sep_apply_l_atomic (mpz_array_merge p i n (Znth i l 0) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma ge_gmp_array_strategy203_correctness : ge_gmp_array_strategy203.
Proof.
  pre_process_default.
  change
    (store_Z (p + i * sizeof ("__mpz_struct")) v)
    with (mpz_store p i v).
  sep_apply_l_atomic (mpz_array_merge p i n v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.
