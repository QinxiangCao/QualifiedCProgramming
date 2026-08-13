Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.typeinfer Require Import typeinfer_strategy_goal.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.typeinfer Require Import typeinfer_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma typeinfer_strategy0_correctness : typeinfer_strategy0.
  pre_process_default.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma typeinfer_strategy1_correctness : typeinfer_strategy1.
  pre_process_default.
  subst.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma typeinfer_strategy2_correctness : typeinfer_strategy2.
  pre_process_default.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma typeinfer_strategy3_correctness : typeinfer_strategy3.
  pre_process_default.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma typeinfer_strategy4_correctness : typeinfer_strategy4.
  pre_process_default.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma typeinfer_strategy5_correctness : typeinfer_strategy5.
  pre_process_default.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma typeinfer_strategy6_correctness : typeinfer_strategy6.
  pre_process_default.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  subst.
  entailer!.
Qed.

Lemma typeinfer_strategy10_correctness : typeinfer_strategy10.
  pre_process_default.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma typeinfer_strategy11_correctness : typeinfer_strategy11.
  pre_process_default.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma typeinfer_strategy12_correctness : typeinfer_strategy12.
  pre_process_default.
  entailer!.
  subst.
  assumption.
Qed.

Lemma typeinfer_strategy13_correctness : typeinfer_strategy13.
  pre_process_default.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma typeinfer_strategy14_correctness : typeinfer_strategy14.
  pre_process_default.
  entailer!.
  subst.
  assumption.
Qed.

Lemma typeinfer_strategy15_correctness : typeinfer_strategy15.
  pre_process_default.
  entailer!.
  subst.
  Intros_R.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma typeinfer_strategy16_correctness : typeinfer_strategy16.
  pre_process_default.
  entailer!.
  subst.
  assumption.
Qed.

Lemma typeinfer_strategy20_correctness : typeinfer_strategy20.
  pre_process_default.
Qed.

Lemma typeinfer_strategy21_correctness : typeinfer_strategy21.
  pre_process_default.
  subst.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma typeinfer_strategy22_correctness : typeinfer_strategy22.
  pre_process_default.
Qed.

Lemma typeinfer_strategy23_correctness : typeinfer_strategy23.
  pre_process_default.
Qed.

Lemma typeinfer_strategy24_correctness : typeinfer_strategy24.
  pre_process_default.
  subst.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.
