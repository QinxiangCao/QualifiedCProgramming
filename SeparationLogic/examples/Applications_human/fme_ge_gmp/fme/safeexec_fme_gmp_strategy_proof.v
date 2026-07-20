Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.fme Require Import safeexec_fme_gmp_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma safeexec_fme_gmp_strategy3_correctness : safeexec_fme_gmp_strategy3.
Proof.
  pre_process_default.
Qed.

Lemma safeexec_fme_gmp_strategy4_correctness : safeexec_fme_gmp_strategy4.
Proof.
  pre_process_default.
Qed.

Lemma safeexec_fme_gmp_strategy5_correctness : safeexec_fme_gmp_strategy5.
Proof.
  pre_process_default.
  entailer!.
  apply bind_equiv; assumption.
Qed.

Lemma safeexec_fme_gmp_strategy6_correctness : safeexec_fme_gmp_strategy6.
Proof.
  pre_process_default.
Qed.

Lemma safeexec_fme_gmp_strategy7_correctness : safeexec_fme_gmp_strategy7.
Proof.
  pre_process_default.
Qed.

Lemma safeexec_fme_gmp_strategy1_correctness : safeexec_fme_gmp_strategy1.
Proof.
  pre_process_default.
Qed.

Lemma safeexec_fme_gmp_strategy2_correctness : safeexec_fme_gmp_strategy2.
Proof.
  pre_process_default.
  entailer!.
  eapply safeExec_proequiv; eauto.
Qed.
