Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.convex_hull Require Import safeexec_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma safeexec_strategy3_correctness : safeexec_strategy3.
  pre_process_default.
Qed.

Lemma safeexec_strategy4_correctness : safeexec_strategy4.
  pre_process_default.
Qed.

Lemma safeexec_strategy5_correctness : safeexec_strategy5.
Proof.
  pre_process_default.
  Intros_p H.
  Intros_p H0.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    eapply bind_equiv.
    + exact H.
    + exact H0.
Qed.

Lemma safeexec_strategy8_correctness : safeexec_strategy8.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma safeexec_strategy9_correctness : safeexec_strategy9.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma safeexec_strategy1_correctness : safeexec_strategy1.
  pre_process_default.
Qed.

Lemma safeexec_strategy6_correctness : safeexec_strategy6.
  pre_process_default.
Qed.

Lemma safeexec_strategy7_correctness : safeexec_strategy7.
  pre_process_default.
Qed.

Lemma safeexec_strategy2_correctness : safeexec_strategy2.
Proof.
  pre_process_default.
  Intros_p H0.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    eapply safeExec_proequiv.
    + exact H0.
    + exact H.
Qed.
